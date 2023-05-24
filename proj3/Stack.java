

public class Stack {
	
	Node head;
	
	/*
	 * predicate Node(Node t; Node n, int v) = t.nxt |-> n &*& t.val |-> v;
	 * predicate List(Node n;) = n == null ? emp : Node(n, ?nn, _) &*& List(nn);
	 * predicate StackInv(Stack t;) = t.head |-> ?h &*& List(h);
	 */
	
	public Stack() 
	// requires @true
	// ensures StackInv(this)
	{
		this.head = null;
    }

    public boolean isEmpty() 
    //@ requires StackInv(this);
    //@ ensures result?StackInv(this):NonEmptyStackInv(this);
    {
		return head == null;
    }

    public void push(int newVal) 
    {
    	Node newNode = new Node(newVal, head);
    	head = newNode;
    }

    // l != 0 * p -> MList(p) } pop p { result == l[0] * p -> MList(l[1..]) }
    public int pop() 
    //@ requires NonEmptyStackInv(this);
    //@ ensures StackInv(this);
    {
    	int val = head.getValue(); 
    	head = head.getNext(); 
    	return val;
    }

    // { l != 0 * p -> MList (l) } peek p { result == l[0] * p -> MList(l) }
    public int peek() 
    //@ requires NonEmptyStackInv(this);
    //@ ensures StackInv(this);
    {
		return head.getValue();
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

    /**
     * p -> MList (l)
     * l = [0, 1, 2, 3 ...]
     */
}

