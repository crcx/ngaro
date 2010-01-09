;;; ngaro.el -- implementation of the Ngaro VM in Emacs Lisp
;;;
;;; Copyright 2010 by Jay Skeer
;;;
;;; Permission to use, copy, modify, and/or distribute this software for
;;; any purpose with or without fee is hereby granted, provided that the
;;; above copyright notice and this permission notice appear in all
;;; copies.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
;;; WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
;;; AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL
;;; DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
;;; PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
;;; TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
;;; PERFORMANCE OF THIS SOFTWARE.
;;;

;;; Currently input into the VM isn't so nice.  You have to eval a
;;; lisp expression to give input.  The good news is you can do it at
;;; any time, even before the VM starts up.  The other good news is
;;; that the VM will go into a wait state if no input is waiting.  The
;;; bad news is while the VM is running, it just about totally takes
;;; over your emacs.
;;;
;;; 1: byte compile ngaro.el
;;; 2: load ngaro.elc
;;; 3: insert something like the following in a buffer
;;;
;;; 	(let ((start (current-time))
;;; 	      (end))
;;; 	  (setq ngaro-input-queue nil)
;;; 	  (ngaro-queue-input-file "c:/cygwin/home/Jay/src/forth/retro/git/retro10/source/meta.retro")
;;; 	  (ngaro-queue-input-file "c:/cygwin/home/Jay/src/forth/retro/git/retro10/source/core.retro")
;;; 	  (ngaro-queue-input-file "c:/cygwin/home/Jay/src/forth/retro/git/retro10/source/stage2.retro")
;;; 	  (ngaro-queue-input-file "c:/cygwin/home/Jay/src/forth/retro/git/retro10/source/stage3.retro")
;;; 	  (ngaro-queue-input-file "c:/cygwin/home/Jay/src/forth/retro/git/retro10/source/final.retro")
;;; 	  (ngaro-start-image "c:/cygwin/home/Jay/src/forth/retro/git/retro10/retroImageEmacs")
;;; 	  (setq end (current-time))
;;; 	  (time-subtract end start))
;;;
;;; 4: evaluate previous sexp (C-u C-x C-e) with point after the (let...)
;;; 5: see this...
;;; 	RETRO
;;; 
;;; 	ok ( ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ )
;;; 	[... much output ...]
;;; 	ok save 
;;; 	ok bye 
;;; 
;;; 	[Ngaro VM (Emacs Lisp) halted.]
;;; 	(0 14 422000)
;;;
;;; That indicates doing a meta compile took about 14.4 seconds on my
;;; machine.  That is using the bytecompile version of ngaro.elc
;;; There is no need to meta compile an image though, you can just load one.
;;;
;;;     (ngaro-start-image "c:/cygwin/home/Jay/src/forth/retro/git/retro10/retroImageEmacs")
;;;
;;; but it is much better to use a "shrunk" image.  Should be around
;;; 30K bytes.  Right now emacs only saves --shrink type images.  Try
;;; copying pristine to retroImageEmacs perhaps.

(defvar ngaro-mem nil
  "The memory image of the current ngaro VM.  There can only be one.")
(defvar ngaro-memsize 0
  "The size, in 29bit cells, of the memory image.")
(defvar ngaro-dstk (make-vector 99 0)
  "The data (aka parameter) stack of the current ngaro VM.")
(defvar ngaro-rstk (make-vector 99 0)
  "The return (aka address) stack of the current ngaro VM.")
(defvar ngaro-dsp 2
  "Index of the top element of the data stack.")
(defvar ngaro-rsp 2
  "Index of the top element of the return stack.")
;; so we are a little less fragile, actually leave 3 elements unused
;; at the bottom of both stacks.  We will report the depth of a stack
;; as (- sp 2).  And we won't get a lisp problem till we try to access
;; the 4th element below the bottom of the stack.
(defvar ngaro-ip  -1
  "Index in ngaro-mem of the current instruction.")
(defvar ngaro-port (make-vector 99 0)
  "The io ports of the Ngaro VM.")
(defvar ngaro-image-file nil
  "The path of the file from which the current image was loaded.")
(defvar ngaro-trace-buffer nil
  "A buffer logging trace output from the VM.")
(defvar ngaro-trace nil
  "non-nil to enable tracing")
(defvar ngaro-input-queue nil
  "Queue of characters waiting to be read by Ngaro.")
(defvar ngaro-status 'VM_HALT
  "Current run/halt/wait status of VM.")
(defvar ngaro-opcodes (make-vector 100 'VM_HALT)
  "Vector of opcodes implemented by VM")
(defvar ngaro-image-load-index nil
  "Internal used when loading image files.")
(defvar ngaro-image-save-index nil
  "Internal used when saving image files.")

;;; read an image from a buffer
(defun ngaro-image-load-next-byte()
    (prog1 (char-after) (forward-char)))

(defun ngaro-image-load-next-int()
    "Return 29 of the next 32 bits as an int"
    ;; assume 'little byte at low address'
    ;; $TODO$ detect and fix endian issues
    (let* ((b0 (ngaro-image-load-next-byte))
           (b1 (ngaro-image-load-next-byte))
           (b2 (ngaro-image-load-next-byte))
           (b3 (ngaro-image-load-next-byte)))
      (+ (lsh (+ (lsh (+ (lsh (logand 31 b3) 8) b2) 8) b1) 8) b0)))

(defun ngaro-image-load-next-1k()
  (let ((i 0))
    (message "Loading image ... %d%% ..."
	     (floor (* 100 (/ (point) (+ 0.0 (point-max))))))
    (while (and (< i 1024) (< (point) (point-max)))
      (aset ngaro-mem ngaro-image-load-index (ngaro-image-load-next-int))
      (setq i (+ 1 i))
      (setq ngaro-image-load-index (+ 1 ngaro-image-load-index)))))

(defun ngaro-load-image(image-file)
  "Load a ngaro VM image."
  (interactive "fImage file name: ")
  (let ((ngaro-image-buffer))
    (setq ngaro-image-load-index 0)
    (save-excursion
      (setq ngaro-image-buffer (find-file-noselect image-file nil :read-raw))
      (set-buffer ngaro-image-buffer)
      ;; allocate an extra 6K cells
      (setq ngaro-mem (make-vector (+ (* 16 1024) (/ (point-max) 4)) 0))
      (goto-char (point-min))
      (message "Loading image ... 0%% ...")
      (while (< (point) (point-max))
	(ngaro-image-load-next-1k)
	(message "Loading image ... %d%% ..."
		 (floor (* 100 (/ (point) (+ 0.0 (point-max)))))))
      (message "Loading image done."))
    (setq ngaro-memsize (length ngaro-mem))
    (kill-buffer ngaro-image-buffer)))

(defun ngaro-image-save-int(int)
    "Save the 29 bit int given as 32 bits"
    ;; writes 'little byte at low address'
    ;; $TODO$ write other endian optionally?
    (let* ((i0 int)
	   (b0 (logand i0 255))
	   (i1 (ash i0 -8))
	   (b1 (logand i1 255))
	   (i2 (ash i1 -8))
	   (b2 (logand i2 255))
	   (i3 (ash i2 -8))
	   (b3 (logand i3 255)))
      (insert b0)
      (insert b1)
      (insert b2)
      (insert b3)))

(defun ngaro-image-save-next-1k()
  (let ((i 0))
    (message "Saving image ... %d%% ..."
	     (floor (* 100 (/ ngaro-image-save-index (+ 0.0 ngaro-memsize)))))
    (while (and (< i 1024) (< ngaro-image-save-index ngaro-memsize))
      (ngaro-image-save-int (aref ngaro-mem ngaro-image-save-index))
      (setq i (+ 1 i))
      (setq ngaro-image-save-index (+ 1 ngaro-image-save-index)))))

(defun ngaro-save-image (image-file)
  "Save the current memory image of the Ngaro VM"
  (interactive "fImage file name: ")
  (let ((ngaro-image-buffer)
	(ngaro-memsize (aref ngaro-mem 3)) ;; always do --shrink
	)
    (setq ngaro-image-save-index 0)
    (save-excursion
      (setq ngaro-image-buffer (find-file-noselect image-file nil :read-raw))
      (set-buffer ngaro-image-buffer)
      (delete-region (point-min) (point-max))
      (message "Saving image ... 0%% ...")
      (while (< ngaro-image-save-index ngaro-memsize)
	(ngaro-image-save-next-1k)
	(message "Saving image ... %d%% ..."
		 (floor (* 100 (/ ngaro-image-save-index (+ 0.0 ngaro-memsize))))))
      (write-region (point-min) (point-max) image-file)
      (set-buffer-modified-p nil)
      (message "Saving image done."))
      (kill-buffer ngaro-image-buffer)))

;;; stack macros for convenience
(defmacro ngaro-push(sp sa v)
  `(progn
     (setq ,sp (+ 1 ,sp))
     (aset ,sa ,sp ,v)))

(defmacro ngaro-pop(sp sa)
  `(prog1
     (aref ,sa ,sp)
     (setq ,sp (- ,sp 1))))

(defmacro dpush(v)
  `(let ((tmp ,v))
     (ngaro-push ngaro-dsp ngaro-dstk tmp)))

(defmacro dpop()
  `(ngaro-pop ngaro-dsp ngaro-dstk))

(defmacro tos()
  `(aref ngaro-dstk ngaro-dsp))

(defmacro nos()
  `(aref ngaro-dstk (- ngaro-dsp 1)))

(defun ngaro-ddepth()
  (- ngaro-dsp 2))

(defmacro rpush(v)
  `(let ((tmp ,v))
     (ngaro-push ngaro-rsp ngaro-rstk tmp)))

(defmacro rpop()
  `(ngaro-pop  ngaro-rsp ngaro-rstk))

(defmacro tors()
  `(aref ngaro-rstk ngaro-rsp))

(defmacro nors()
  `(aref ngaro-rstk (- ngaro-rsp 1)))

(defun ngaro-rdepth()
  (- ngaro-rsp 2))

(defun ngaro-init-vm ()
  "Initialize the state of the VM."
  (let ((opcodeinit [VM_NOP     VM_LIT       VM_DUP     VM_DROP
		     VM_SWAP    VM_PUSH      VM_POP     VM_CALL
		     VM_JUMP    VM_RETURN    VM_GT_JUMP VM_LT_JUMP
		     VM_NE_JUMP VM_EQ_JUMP   VM_FETCH   VM_STORE
		     VM_ADD     VM_SUB       VM_MUL     VM_DIVMOD
		     VM_AND     VM_OR        VM_XOR     VM_SHL
		     VM_SHR     VM_ZERO_EXIT VM_INC     VM_DEC
		     VM_IN      VM_OUT       VM_WAIT    VM_HALT])
	(i 0))
    (setq ngaro-opcodes (make-vector 100 'VM_HALT))
    (while (< i (length opcodeinit))
      (aset ngaro-opcodes i (aref opcodeinit i))
      (setq i (+ 1 i)))
    (setq ngaro-ip   0)
    (setq ngaro-dsp  2)
    (aset ngaro-dstk 0 9999)
    (aset ngaro-dstk 1 9999)
    (aset ngaro-dstk 2 9999)
    (setq ngaro-rsp  2)
    (aset ngaro-rstk 0 9999)
    (aset ngaro-rstk 1 9999)
    (aset ngaro-rstk 2 9999)
    (setq ngaro-trace nil)
    (setq ngaro-status 'VM_RUN)
    (setq ngaro-port (make-vector 99 0))
    (setq ngaro-image-file nil)))

(defun ngaro-continue ()
  "Resume execution of the Ngaro VM."
  (interactive)
  (if (equal ngaro-status 'VM_HALT)
      (error "The VM halted.  You must reload the image and start it again.")
    (setq ngaro-status 'VM_RUN))
  (let ((opnum) (opcode) (oparg))
    (while (and (equal ngaro-status 'VM_RUN)
		(< ngaro-ip ngaro-memsize))
      (setq opnum  (aref ngaro-mem ngaro-ip))
      (setq oparg  (aref ngaro-mem (+ 1 ngaro-ip)))
      (setq opcode (aref ngaro-opcodes opnum))
      (if ngaro-trace (ngaro-add-trace-line opnum opcode oparg))
      (cond
       ((eq opcode 'VM_HALT)      (progn
				    (setq ngaro-status 'VM_HALT)
				    (setq ngaro-ip (+ 1 ngaro-memsize))))
       ((eq opcode 'VM_NOP)) ;; do nothing
       ((eq opcode 'VM_LIT)       (progn
				    (dpush oparg)
				    (setq ngaro-ip (+ 1 ngaro-ip))))
       ((eq opcode 'VM_DUP)       (dpush (dpush (dpop))))
       ((eq opcode 'VM_DROP)      (dpop))
       ((eq opcode 'VM_SWAP)      (let* ((te (dpop)) (ne (dpop)))
				    (dpush te)
				    (dpush ne)))
       ((eq opcode 'VM_PUSH)      (rpush (dpop)))
       ((eq opcode 'VM_POP)       (dpush (rpop)))
       ((eq opcode 'VM_CALL)      (progn
				    (rpush (+ 1 ngaro-ip))
				    (setq ngaro-ip (- oparg 1))))
       ((eq opcode 'VM_JUMP)      (setq ngaro-ip (- oparg 1)))
       ((eq opcode 'VM_RETURN)    (setq ngaro-ip (rpop)))
       ((eq opcode 'VM_GT_JUMP)   (let* ((te (dpop)) (ne (dpop)))
				    (if (> ne te)
					(setq ngaro-ip (- oparg 1))
				      (setq ngaro-ip (+ 1 ngaro-ip)))))
       ((eq opcode 'VM_LT_JUMP)   (let* ((te (dpop)) (ne (dpop)))
				    (if (< ne te)
					(setq ngaro-ip (- oparg 1))
				      (setq ngaro-ip (+ 1 ngaro-ip)))))
       ((eq opcode 'VM_NE_JUMP)   (let* ((te (dpop)) (ne (dpop)))
				    (if (= ne te)
					(setq ngaro-ip (+ 1 ngaro-ip))
				      (setq ngaro-ip (- oparg 1)))))
       ((eq opcode 'VM_EQ_JUMP)   (let* ((te (dpop)) (ne (dpop)))
				    (if (= ne te)
					(setq ngaro-ip (- oparg 1))
				      (setq ngaro-ip (+ 1 ngaro-ip)))))
       ((eq opcode 'VM_FETCH)     (let* ((te (dpop)))
				    (dpush (aref ngaro-mem te))))
       ((eq opcode 'VM_STORE)     (let* ((te (dpop)) (ne (dpop)))
				    (aset ngaro-mem te ne)))
       ((eq opcode 'VM_ADD)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (+ ne te))))
       ((eq opcode 'VM_SUB)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (- ne te))))
       ((eq opcode 'VM_MUL)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (* ne te))))
       ((eq opcode 'VM_DIVMOD)    (let* ((te (dpop)) (ne (dpop)))
				    (dpush (% ne te))
				    (dpush (/ ne te))))
       ((eq opcode 'VM_AND)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (logand ne te))))
       ((eq opcode 'VM_OR)        (let* ((te (dpop)) (ne (dpop)))
				    (dpush (logior ne te))))
       ((eq opcode 'VM_XOR)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (logxor ne te))))
       ((eq opcode 'VM_SHL)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (ash ne te))))
       ((eq opcode 'VM_SHR)       (let* ((te (dpop)) (ne (dpop)))
				    (dpush (ash ne (- te)))))
       ((eq opcode 'VM_ZERO_EXIT) (let* ((te (dpop)))
				    (if (= 0 te)
					(setq ngaro-ip (rpop))
				      (dpush te))))
       ((eq opcode 'VM_INC)       (let* ((te (dpop))) (dpush (+ te 1))))
       ((eq opcode 'VM_DEC)       (let* ((te (dpop))) (dpush (- te 1))))
       ((eq opcode 'VM_IN)        (let* ((te (dpop)))
				    (dpush (aref ngaro-port te))
				    (aset ngaro-port te 0)))
       ((eq opcode 'VM_OUT)       (let* ((te (dpop)) (ne (dpop)))
				    (aset ngaro-port 0 0)
				    (aset ngaro-port te ne)))
       ((eq opcode 'VM_WAIT)
	(if (= (aref ngaro-port 0) 1)
	    t
	  (cond
	   ((and (= (aref ngaro-port 0) 0)
		 (= (aref ngaro-port 1) 1))
	    (let ((byte (ngaro-get-input-byte)))
	      (if (null byte)
		  (setq ngaro-status 'ngaro-input-queue)
		(aset ngaro-port 1 byte)
		(aset ngaro-port 0 1))))
	 
	   ((= (aref ngaro-port 2) 1)
	    (insert (dpop))
	    (aset ngaro-port 2 0)
	    (aset ngaro-port 0 1))
	 
	   ((= (aref ngaro-port 4) 1)
	    (ngaro-save-image ngaro-image-file)
	    (aset ngaro-port 2 0)
	    (aset ngaro-port 0 1))
	 
	   ((= (aref ngaro-port 5) -1)
	    (aset ngaro-port 5 ngaro-memsize)
	    (aset ngaro-port 0 1))
	 
	   ((and (<= -4 (aref ngaro-port 5))
		 (<= (aref ngaro-port 5) -2))
	    (aset ngaro-port 5 0)
	    (aset ngaro-port 0 1))
	 
	   ((= (aref ngaro-port 5) -5)
	    (aset ngaro-port 5 (- ngaro-dsp 2))
	    (aset ngaro-port 0 1))
	 
	   ((= (aref ngaro-port 5) -6)
	    (aset ngaro-port 5 (ngaro-rdepth))
	    (aset ngaro-port 0 1))))))
      (when (= (aref ngaro-port 3) 0)
	(aset ngaro-port 3 1)
	;; (ngaro-dev-refresh)
	(redisplay))
      (if (equal ngaro-status 'VM_RUN)
	  (setq ngaro-ip (+ 1 ngaro-ip))))
    (if (or (<= ngaro-memsize ngaro-ip)
	    (equal ngaro-status 'VM_HALT))
	(insert "\n\n[Ngaro VM (Emacs Lisp) halted.]\n"))))

(defun ngaro-add-trace-line(opnum opcode oparg)
  (let* ((i 0)
	 (dd  (ngaro-ddepth))
	 (ddd (max 0 (min 3 dd)))
	 (rd  (ngaro-rdepth))
	 (drd (max 0 (min 3 rd))))
    (save-excursion
      (set-buffer "*Ngaro-trace-buffer*")
      (insert (format "%4d:%2x %12S" ngaro-ip opnum opcode))
      (if (member opcode '())
	  (insert (format " %4d  "  oparg))
	(insert "       "))
      (insert (format "<%2d>" dd))
      (setq i 0)
      (while (< i ddd)
	(insert (format " %4d" (aref ngaro-dstk (+ (- ngaro-dsp (- ddd i)) 1))))
	(setq i (+ i 1)))
      (insert (format " --- <%2d>" rd))
      (setq i 0)
      (while (< i drd)
	(insert (format " %4d" (aref ngaro-rstk (+ (- ngaro-rsp (- drd i)) 1))))
	(setq i (+ i 1)))
      (insert "\n"))))
  
(defun ngaro-queue-input-file(file-path)
  "Add the contents of FILE to the input queue for the ngaro vm"
  (interactive "fQueue input from file: ")
  (save-excursion
    (set-buffer (or (get-file-buffer file-path)
		    (find-file file-path)))
    (goto-char (point-min))
    (setq ngaro-input-queue (append ngaro-input-queue (list (current-buffer)) nil)))
  (if (equal ngaro-status 'ngaro-input-queue) (ngaro-continue)))

(defun ngaro-queue-input-byte(char)
  "Add a character or vector of chars to the queue of chars waiting to be read by Ngaro"
  (interactive "M")
  (cond
   ((stringp char)
    (setq ngaro-input-queue (append ngaro-input-queue (string-to-list char) nil)))
   ((or (vectorp char) (listp char))
    (setq ngaro-input-queue (append ngaro-input-queue char nil)))
   (t (setq ngaro-input-queue (append ngaro-input-queue (list char) nil))))
  (if (equal ngaro-status 'ngaro-input-queue) (ngaro-continue)))

(defun ngaro-get-input-byte-from-buffer (buffer)
  (save-excursion
    (set-buffer buffer)
    (if (< (point) (point-max))
	(prog1
	    (char-after (point))
	  (forward-char 1))
      (setq ngaro-input-queue (cdr ngaro-input-queue))
      (ngaro-get-input-byte))))

(defun ngaro-get-input-byte ()
  "Return an integer character, or NIL meaning none is ready."
  (if (<= (length ngaro-input-queue) 0)
      nil
    (if (bufferp (car ngaro-input-queue))
	(ngaro-get-input-byte-from-buffer (car ngaro-input-queue))
      (prog1
	  (car ngaro-input-queue)
	(setq ngaro-input-queue
	      (cdr ngaro-input-queue))))))

(defun ngaro-start-image (image-file &optional trace)
  "Start the Ngaro virtual machine running with IMAGE-FILE
With non-nil TRACE, or prefix argument, send a trace of the VM's execution to a buffer."
  (interactive "fImage file name: \np")
  (ngaro-init-vm)
  (ngaro-load-image image-file)
  (setq ngaro-image-file image-file)
  (setq ngaro-trace trace)
  (if ngaro-trace
      (setq ngaro-trace-buffer (get-buffer-create " *Ngaro-trace-buffer*")))
;;  (setq ngaro-interaction-buffer (get-buffer-create "*Ngaro-interaction*"))
;;  (ngaro-interaction-mode)
  (ngaro-continue))

