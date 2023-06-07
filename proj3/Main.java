public static void Main(String[] args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
    {
        CQueue q = new CQueue();
        for(int i = 0 ; i < 100 ; i++)
        //@ invariant [?f]CQueueInv(q) &*& [_]System_out(o) &*& o != null;
        {
            //@ close [f/2]CQueueInv(q);
            (new MyEnqThread(q, i)).start();
            //@ close [f/4]CQueueInv(q);
            (new MyDeqThread(q)).start();
        }
    }