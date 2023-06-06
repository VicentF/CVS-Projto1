
// TASK 1 - predicates
/*@
	predicate Node(Node t; Node n, int v) = t.next |-> n &*& t.val |-> v;
	predicate List(Node n; list<int> elems) = n == null? (emp &*& elems == nil): Node(n,?nn,?v) &*& List(nn,?tail) &*& elems == cons(v,tail);
	predicate StackInv(Stack l; list<int> elems) = l.head |-> ?h &*& List(h,elems);
	predicate NonEmptyStackInv(Stack t; list<int> elems) = t.head |-> ?h &*& h != null &*& List(h, elems);
@*/

// TASK 1
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

    	public int peek() 
    	//@ requires NonEmptyStackInv(this, ?l);
    	//@ ensures StackInv(this, ?l2);
    	{
		return head.val;
    	}

    	public void flip() 
    	//@ requires StackInv(this, ?l);
    	//@ ensures StackInv(this, reverse(l));
    	{

    		Node n = null;
         	//@ open StackInv(this, l);
         	while (head != null) 
         	//@ invariant head |-> ?h &*& List(h, ?l1) &*& List(n, ?l2) &*& l == append(reverse(l2), l1);
         	{
             		Node next = head.next;
             		head.next = n;
             		n = head;
             		head = next;
             		//@assert l1 == cons(?v,?tail0) &*& l == append(reverse(l2),cons(v,tail0));
	     		//@reverse_reverse(cons(v,tail0));
	     		//@reverse_append( reverse(cons(v,tail0)) , l2 );
	     		//@append_assoc(reverse(tail0),cons(v,nil),l2);
	     		//@reverse_append(reverse(tail0),cons(v,l2));
	     		//@reverse_reverse(tail0);
         	}
         	//@ open List(h, l1);
         	head = n;
         	//@append_nil(reverse(l2));
    	}
}

