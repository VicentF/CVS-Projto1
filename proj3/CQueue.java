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
					&*& lck(l, 1, CQueue_shared_state(q))
					&*& q.notEmpty |-> ?qc
					&*& qc != null
					&*& cond(qc, CQueue_shared_state(q), CQueue_notEmptyQueue(q));

	
	predicate_ctor CQueue_shared_state (CQueue q) () = (q.left |-> ?l &*& StackInv(l, ?l1)) 
							&*& (q.right |-> ?r &*& StackInv(r, ?r2))
							&*& l != null &*& r != null;
							
	predicate_ctor CQueue_notEmptyQueue(CQueue q) () = q.left |-> ?l &*& StackInv(l, ?ll) 
							&*& q.right |-> ?r &*& StackInv(r, ?lr) 
							&*& (lr != nil || ll != nil) 
							&*& l != null &*& r != null;
@*/

// TASK 2
public class CQueue {

	Stack left;
	Stack right;
	ReentrantLock mon;
	Condition notEmpty;
	
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
 		//@ close set_cond(CQueue_shared_state(this), CQueue_notEmptyQueue(this));
		this.notEmpty = mon.newCondition();
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
		//@ close CQueue_notEmptyQueue(this)();
		notEmpty.signal();
		this.mon.unlock();
		//@ close CQueueInv(this);
	}
	
	private void flush() 
	//@ requires (this.left |-> ?l &*& StackInv(l, ?ll)) &*& (this.right |-> ?r &*& StackInv(r, ?rl)) &*& l != null &*& r != null &*& rl == nil &*& ll != nil;
	//@ ensures (this.left |-> ?l2 &*& StackInv(l2, rl)) &*& (this.right |-> ?r2 &*& StackInv(r2, reverse(ll))) &*& l2 != null &*& r2 != null;
	{	
		this.left.flip();
		//@ reverse_nnil(ll);
		this.right = this.left;
		this.left = new Stack();
	}
	
	public int dequeue() 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		this.mon.lock();
		//@ open CQueue_shared_state(this)();
		while (this.right.isEmpty() && this.left.isEmpty()) 
		/*@ invariant (this.left |-> ?l &*& StackInv(l, ?ll)) 
				&*& (this.right |-> ?r &*& StackInv(r, ?rl))
				&*& l != null 
				&*& r != null
				&*& this.notEmpty |-> ?qc
				&*& qc != null
				&*& cond(qc, CQueue_shared_state(this), CQueue_notEmptyQueue(this));
		@*/
		{
			//@ close CQueue_shared_state(this)();
			try { notEmpty.await(); }  catch (InterruptedException e) {} 
			//@ open CQueue_notEmptyQueue(this)();
		}
		
		if(this.right.isEmpty()) 
		{
			flush();
			//@ reverse_nnil(ll);
			//@ assert this.right |-> ?rs &*& StackInv(rs, ?dl) &*& dl != nil;
		}
	
		int result = this.right.pop();
		//@ close CQueue_shared_state(this)();
		this.mon.unlock();

    		//@ close CQueueInv(this);
    		return result;
	}
	
	public boolean isEmpty() 
	//@ requires CQueueInv(this);
	//@ ensures CQueueInv(this);
	{
		//@ open CQueueInv(this);
		this.mon.lock(); 
		//@ open CQueue_shared_state(this)();
		boolean val = this.right.isEmpty() && this.left.isEmpty();
		//@ close CQueue_shared_state(this)();
		this.mon.unlock();
		//@ close CQueueInv(this);
		return val;
	}
	
}
