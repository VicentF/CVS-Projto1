class MyDeqThread implements Runnable {

	CQueue q;
  	//@ predicate pre() = CQueueInv(this.q);
  	//@ predicate post() = true;
  
  	public MyDeqThread(CQueue cc)
  	//@ requires cc != null &*& [1/2]CQueueInv(cc);
  	//@ ensures CQueueInv(this.q);
  	{
   		this.q = cc;
  	}
  	
  	public void run()
 	//@ requires pre();
 	//@ ensures post();
  	{
   		while(true)
   		//@ invariant CQueueInv(this.q);
 		{ 
 			q.dequeue();
 		}
  	}
}