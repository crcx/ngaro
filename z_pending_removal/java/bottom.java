    }
  }

/**
 * Initialize the Ngaro VM. Should this be merged into
 * the constructor?
 */
  public void init()
  {
    sp = 0;
    rsp = 0;
    ip = 0;
    data    = new int[100];
    address = new int[100];
    ports   = new int[1024];
    memory  = new int[5000000];
    initial_image();
  }


 /**
  * Handler for the emulated hardware devices
  */
  public void handleDevices()
  {
    byte[] b = { 0, 0, 0 };
    char c = ' ';
    int d = 0;

    if (ports[0] == 1)
      return;

    if (ports[0] == 0 && ports[1] == 1)
    {
      try { System.in.read(b, 0, 1); } catch(Exception e) { System.out.println(e); }
      ports[1] = (int)b[0];
      ports[0] = 1;
    }
    if (ports[2] == 1)
    {
      c = (char)data[sp];
      if (data[sp] < 0)
      {
        for(c = 0; c < 300; c++)
          System.out.println("\n");
      }
      else
        System.out.print(c);
      sp--;
      ports[2] = 0;
      ports[0] = 1;
    }
    if (ports[4] == 1)
    {
      saveImage("retroImage");
      ports[4] = 0;
      ports[0] = 1;
    }

    /* Capabilities */
    if (ports[5] == -1)
    {
      ports[5] = 5000000;
      ports[0] = 1;
    }
    if (ports[5] == -2 || ports[5] == -3 || ports[5] == -4)
    {
      ports[5] = 0;
      ports[0] = 1;
    }
    if (ports[5] == -5)
    {
      ports[5] = sp;
      ports[0] = 1;
    }
    if (ports[5] == -6)
    {
      ports[5] = rsp;
      ports[0] = 1;
    }
  }


 /**
  * Process a single opcode
  */
  public void process()
  {
    int op = memory[ip];
    int x, y, z;

    switch(memory[ip])
    {
    case VM_NOP:
      break;
    case VM_LIT:
      sp++; ip++; data[sp] = memory[ip];
      break;
    case VM_DUP:
      sp++; data[sp] = data[sp-1];
      break;
    case VM_DROP:
      data[sp] = 0; sp--;
      break;
    case VM_SWAP:
      x = data[sp];
      y = data[sp-1];
      data[sp] = y;
      data[sp-1] = x;
      break;
    case VM_PUSH:
      rsp++;
      address[rsp] = data[sp];
      sp--;
      break;
    case VM_POP:
      sp++;
      data[sp] = address[rsp];
      rsp--;
      break;
    case VM_CALL:
      ip++; rsp++;
      address[rsp] = ip++;
      ip = memory[ip-1] - 1;
      break;
    case VM_JUMP:
      ip++;
      ip = memory[ip] - 1;
      break;
    case VM_RETURN:
      ip = address[rsp]; rsp--;
      break;
    case VM_GT_JUMP:
      ip++;
      if (data[sp-1] > data[sp])
        ip = memory[ip] - 1;
      sp = sp - 2;
      break;
    case VM_LT_JUMP:
      ip++;
      if (data[sp-1] < data[sp])
        ip = memory[ip] - 1;
      sp = sp - 2;
      break;
    case VM_NE_JUMP:
      ip++;
      if (data[sp-1] != data[sp])
        ip = memory[ip] - 1;
      sp = sp - 2;
      break;
    case VM_EQ_JUMP:
      ip++;
      if (data[sp-1] == data[sp])
        ip = memory[ip] - 1;
      sp = sp - 2;
      break;
    case VM_FETCH:
      x = data[sp];
      data[sp] = memory[x];
      break;
    case VM_STORE:
      memory[data[sp]] = data[sp-1];
      sp = sp - 2;
      break;
    case VM_ADD:
      data[sp-1] += data[sp]; data[sp] = 0; sp--;
      break;
    case VM_SUB:
      data[sp-1] -= data[sp]; data[sp] = 0; sp--;
      break;
    case VM_MUL:
      data[sp-1] *= data[sp]; data[sp] = 0; sp--;
      break;
    case VM_DIVMOD:
      x = data[sp];
      y = data[sp-1];
      data[sp] = y / x;
      data[sp-1] = y % x;
      break;
    case VM_AND:
      x = data[sp];
      y = data[sp-1];
      sp--;
      data[sp] = x & y;
      break;
    case VM_OR:
      x = data[sp];
      y = data[sp-1];
      sp--;
      data[sp] = x | y;
      break;
    case VM_XOR:
      x = data[sp];
      y = data[sp-1];
      sp--;
      data[sp] = x ^ y;
      break;
    case VM_SHL:
      x = data[sp];
      y = data[sp-1];
      sp--;
      data[sp] = y << x;
      break;
    case VM_SHR:
      x = data[sp];
      y = data[sp-1];
      sp--;
      data[sp] = y >>= x;
      break;
    case VM_ZERO_EXIT:
      if (data[sp] == 0)
      {
        sp--;
        ip = address[rsp]; rsp--;
      }
      break;
    case VM_INC:
      data[sp]++;
      break;
    case VM_DEC:
      data[sp]--;
      break;
    case VM_IN:
      x = data[sp];
      data[sp] = ports[x];
      ports[x] = 0;
      break;
    case VM_OUT:
      ports[0] = 0;
      ports[data[sp]] = data[sp-1];
      sp = sp - 2;
      break;
    case VM_WAIT:
      handleDevices();
      break;
    default:
      System.out.println("Invalid Opcode at " + ip + " : " + switchEndian(op));
      ip = 5000000;
    }
  }


 /**
  * The main entry point. What else needs to be said?
  */
  public static void main(String[] args)
  {
    if (System.getProperty("os.name").startsWith("Windows"))
    {
      System.out.println("Windows is not supported!");
      System.exit(-1);
    }
    retro vm = new retro();

    vm.init();

    if (args.length > 0)
    {
      int x, i;
      for (i = 0; i < args.length; i++)
      {
        if (args[i].equals("--endian"))
        {
          for (i = 0; i < 5000000; i++)
            vm.memory[i] = vm.switchEndian(vm.memory[i]);
        }
        if (args[i].equals("--about"))
        {
          System.out.println("Retro Language  [VM: java]");
          System.exit(0);
        }
      }
    }

    vm.set_tty(true);

    for (vm.ip = 0; vm.ip < 5000000; vm.ip++)
       vm.process();

    vm.set_tty(false);
  }
}