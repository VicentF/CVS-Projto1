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
	predicate CQueueInv(CQueue q, list<int> left, list<int> right) = q.mon |-> ?l 
									&*& l != null 
									&*& lck(l, 1, CQueue_shared_state(q, left, right));

	
	predicate_ctor CQueue_shared_state (CQueue q, list<int> left, list<int> right) () = (q.left |-> ?l &*& StackInv(l, left)) 
									     		&*& (q.right |-> ?r &*& StackInv(r, right))
									     		&*& l != null &*& r != null;
@*/

// TASK 2
public class CQueue {

	Stack left;
	Stack right;
	ReentrantLock mon;
	
	public CQueue()
	//@ requires true;
	//@ ensures CQueueInv(this, nil, nil);
	{
		this.left = new Stack();
		this.right = new Stack();
		//@ close CQueue_shared_state(this, nil, nil)();
		//@ close enter_lck(1, CQueue_shared_state(this, nil, nil));
		this.mon = new ReentrantLock();
		//@ assert this.mon |-> ?l  &*& lck(l, 1, CQueue_shared_state(this, nil, nil));
 		//@ close CQueueInv(this, nil, nil);
	}
	
	private void enqueue(int elem) 
	//@ requires CQueueInv(this, ?l, ?r);
	//@ ensures NonEmptyStackInv(this.left, cons(?v, ?t)) &*& CQueueInv(this, ?l2, r);
	{
		//@ open CQueueInv(this, l, r);
		this.mon.lock(); 
		//@ open CQueue_shared_state(this, l, r)();
		this.left.push(elem);
		//@ close CQueue_shared_state(this, l, r)();
		this.mon.unlock();
	}
	
	public void flush() 
	// requires
	// ensures
	{
		this.right = this.left.flip();
		this.left = new Stack();
	}
	
	public int dequeue() 
	// requires
	// ensures
	{
		if (this.right.isEmpty())
			flush();
		return this.right.pop();
	}
	
	public boolean isEmpty() 
	// requires
	// ensures
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