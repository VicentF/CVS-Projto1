import java.util.concurrent.*;
import java.util.concurrent.locks.*;

// TASK 2 - predicates and Lemmas
/*@
	lemma void append_nnil(list<int> l1, list<int> l2)
		requires l2 != nil;
		ensures append(l1,l2) != nil;
	{
		switch (l1) 
		{
			case nil:
			case cons(x,xs):
		}
	}

	lemma void reverse_nnil(list<int> xs)
		requires xs != nil;
		ensures reverse(xs) != nil;
	{
		switch(xs) 
		{
			case nil:
			case cons(h, t):
			append_nnil(reverse(t),cons(h,nil));
		}
	}
	
@*/

/*@
	predicate CQueueInv(CQueue q;) = q.mon |-> ?l 
					&*& l != null 
					&*& lck(l, 1, CQueue_shared_state(q));

	
	predicate_ctor CQueue_shared_state (CQueue q) () = (q.left |-> ?l &*& StackInv(l, ?l1)) 
							&*& (q.right |-> ?r &*& StackInv(r, ?r2))
							&*& l != null &*& r != null;
@*/

// TASK 2
public class CQueue {

	Stack left;
	Stack right;
	ReentrantLock mon;
	
	public CQueue()
	//@ requires true;
	//@ ensures CQueueInv(this);
	{
		this.left = new Stack();
		this.right = new Stack();
		//@ close CQueue_shared_state(this)();
		//@ close enter_lck(1, CQueue_shared_state(this));
		this.mon = new ReentrantLock();
		//@ assert this.mon |-> ?l  &*& lck(l, 1, CQueue_shared_state(this));
 		//@ close CQueueInv(this);
	}
	
	public void enqueue(int elem) 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		//@ open CQueueInv(this);
		this.mon.lock(); 
		//@ open CQueue_shared_state(this)();
		this.left.push(elem);
		//@ close CQueue_shared_state(this)();
		this.mon.unlock();
	}
	
	private void flush() 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{	
		//@ open CQueueInv(this);
		this.mon.lock();
		//@ open CQueue_shared_state(this)();
		this.left.flip();
		this.right = this.left;
		this.left = new Stack();
		//@ close CQueue_shared_state(this)();
		this.mon.unlock();
	}
	
	public int dequeue() 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		//@ open CQueueInv(this);
		this.mon.lock();
		//@ open CQueue_shared_state(this)();
		if (this.right.isEmpty()) 
		{
			flush();
		}
		//@ close CQueue_shared_state(this)();
		this.mon.unlock();
		
		
		return this.right.pop();
	}
	
	public boolean isEmpty() 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		return this.right.isEmpty() && this.left.isEmpty();
	}
	
}

/*
public static void main(String[] args)
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
*/