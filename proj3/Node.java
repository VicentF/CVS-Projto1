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