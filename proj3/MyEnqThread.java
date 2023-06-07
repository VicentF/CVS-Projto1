class MyEnqThread implements Runnable {

	CQueue q;
	int val;	
  	//@ predicate pre() = CQueueInv(this.q);
  	//@ predicate post() = true;
  
  	public MyEnqThread(CQueue cc, int i)
  	//@ requires cc != null &*& [1/2]CQueueInv(cc);
  	//@ ensures CQueueInv(this.q);
  	{
   		this.q = cc;
   		this.val = i;
  	}
  	
  	public void run()
 	//@ requires pre();
 	//@ ensures post();
  	{
   		while(true)
   		//@ invariant CQueueInv(this.q);
 		{ 
 			q.enqueue(i);
 		}
  	}
}