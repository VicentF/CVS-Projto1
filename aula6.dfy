class Set {
    var store:array<int>;
    var nelems: int;
    
    ghost var Repr:set<object>;
    ghost var Elems: set<int>;

    ghost predicate RepInv()
    reads this, Repr
    {
        this in Repr && store in Repr &&
        0 < store.Length
        && 0 <= nelems <= store.Length
        && (forall i :: 0 <= i < nelems ==> store[i] in Elems)
        && (forall x :: x in Elems ==> exists i :: 0 <= i < nelems && store[i] == x)
    }

    // the construction operation
    constructor(n: int)
    requires 0 < n
    ensures RepInv()
    ensures fresh(Repr-{this})
    {
        store := new int[n];
        nelems := 0;
        Repr := {this, store};
        Elems := {};
    }

    // returns the number of elements in the set
    function size() :int
    requires RepInv()
    ensures RepInv()
    reads Repr
    { nelems }

    // returns the maximum number of elements in the set
    function maxSize():int
    requires RepInv()
    ensures RepInv()
    reads Repr
    { store.Length }

    // checks if the element given is in the set
    method contains(v:int) returns (b:bool)
    requires RepInv()
    ensures RepInv()
    ensures b <==> v in Elems
    // exists j::(0 <= j < nelems) && v == store[j]
    {
        var i := find(v);
        return i >= 0;
    }

    // adds a new element to the set if space available
    method add(v:int)
    requires RepInv()
    requires size() < maxSize()
    ensures RepInv()
    modifies Repr
    ensures fresh(Repr-old(Repr))
    {
        var f:int := find(v);
        if (f < 0) {
            store[nelems] := v;
            nelems := nelems + 1;
            Elems := Elems + {v};
            
            assert forall i :: 0 <= i <= nelems - 1 ==> old(store[i]) == store[i];

            assert this in Repr && store in Repr && 0 < store.Length;
            assert 0 <= nelems <= store.Length;
            assert (forall i :: 0 <= i < nelems ==> store[i] in Elems);
            assert (forall x :: x in Elems ==> exists i :: 0 <= i < nelems && store[i] == x);
        }
    }

    // private method that should not be in the
    method find(x:int) returns (r:int)
    requires RepInv()
    ensures RepInv()
    ensures r < 0 ==> x !in Elems
    ensures r >=0 ==> r < nelems && x in Elems
    {
        var i:int := 0;
        while (i<nelems)
        decreases nelems-i
        invariant 0 <= i <= nelems;
        invariant forall j::(0<=j< i) ==> x != store[j];
        {
            if (store[i]==x) { return i; }
            i := i + 1;
        }
        return -1;
    }

    method Main()
    {
        var s := new Set(10);
        if (s.size() < s.maxSize()) {
            var n := s.size();
            s.add(2);
            var b := s.contains(2);
            if (s.size() < s.maxSize()) {
                s.add(3);
            }
        }
    }
}
