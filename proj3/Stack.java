
	/*@
	predicate Node(Node t; Node n, int v) = t.next |-> n &*& t.val |-> v;
	predicate List(Node n; list<int> elems) = n == null? (emp &*& elems == nil): Node(n,?nn,?v) &*& List(nn,?tail) &*& elems == cons(v,tail);
	predicate StackInv(Stack l; list<int> elems) = l.head |-> ?h &*& List(h,elems);
	predicate NonEmptyStackInv(Stack t; list<int> elems) = t.head |-> ?h &*& h != null &*& List(h, elems);
	@*/



class Node {
	
	Node next;
	int val;

	Node(int v, Node next)
	//@requires true;
	//@ensures Node(this,next,v);
	{
		this.next = next;
		this.val = v;
	}
}

public class Stack {
	
	Node head;
	
	public Stack() 
	//@ requires true;
	//@ ensures StackInv(this, nil);
	{
		this.head = null;
	}
 
    public boolean isEmpty() 
    //@ requires StackInv(this, ?l);
    //@ ensures result?StackInv(this, ?l2):NonEmptyStackInv(this, ?l2);
    {
		return head == null;
    }

    public void push(int newVal) 
    //@requires StackInv(this, ?l);
    //@ensures NonEmptyStackInv(this, cons(?v, ?t));
    // ensures NonEmptyStackInv(this, ?l) &*& StackInv(this, ?);
    {
    	Node newNode = new Node(newVal, head);
    	head = newNode;
    }

    // l != 0 * p -> MList(p) } pop p { result == l[0] * p -> MList(l[1..]) }
    // old(head) == l(0)
    public int pop() 
    //@ requires NonEmptyStackInv(this, cons(?v, ?t));
    //@ ensures StackInv(this, t) &*& result == v;
    // requires NonEmptyStackInv(this, ?elems);
    // ensures StackInv(this, tail(elems)) &*& result == head(elems);
    {
    	int val = head.val; 
    	head = head.next; 
    	return val;
    }

    // { l != 0 * p -> MList (l) } peek p { result == l[0] * p -> MList(l) }
    public int peek() 
    //@ requires NonEmptyStackInv(this, ?l);
    //@ ensures StackInv(this, ?l2);
    {
		return head.val;
    }

    public void flip() 
    {
    	 Node prev = null;
         Node current = head;
         Node next = null;
         while (current != null) {
             next = current.next;
             current.next = prev;
             prev = current;
             current = next;
         }
         head = prev;
    }
}