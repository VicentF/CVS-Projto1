class MyDeqThread implements Runnable {

	public CQueue loc_cc;
  	//@ predicate pre() = MyDeqThreadInv(this);
  	//@ predicate post() = true;
  
  	public MyDeqThread(CQueue cc)
  	//@ requires cc != null &*& [1/2]CQueueInv(cc);
  	//@ ensures Deq_threadInv(this);
  	{
   		loc_cc = cc;
  	}
  	
  	public void run()
 	//@ requires pre();
 	//@ ensures post();
  	{
   		while(true)
   		//@ invariant Deq_threadInv(this);
 		{ 
 			loc_cc.dequeue();
 		}
  	}
}