class MyEnqThread implements Runnable {

	public CQueue loc_cc;
	public int val;	
  	//@ predicate pre() = MyEnqThreadInv(this);
  	//@ predicate post() = true;
  
  	public MyEnqThread(CQueue cc, int i)
  	//@ requires cc != null &*& [1/2]CQueueInv(cc);
  	//@ ensures Enq_threadInv(this);
  	{
   		loc_cc = cc;
   		val = i;
  	}
  	
  	public void run()
 	//@ requires pre();
 	//@ ensures post();
  	{
   		while(true)
   		//@ invariant Enq_threadInv(this);
 		{ 
 			loc_cc.enqueue(i);
 		}
  	}
}