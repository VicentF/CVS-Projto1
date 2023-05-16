datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

ghost function mem<T>(x:T,l:List<T>) : bool 
{
    match l 
    {
        case Nil => false
        case Cons(y,xs) => x==y || mem(x,xs)
    }
}

ghost function length<T>(l:List<T>) : int 
{
    match l 
    {
        case Nil => 0
        case Cons(_,xs) => 1 + length(xs)
    } 
}

function list_find<K(==),V(!new)>(k:K,l:List<(K,V)>) : Option<V>
ensures match list_find(k,l) 
    {
    case None => forall v :: !mem((k,v),l)
    case Some(v) => mem((k,v),l)
    }
{
    match l 
    {
        case Nil => None
        case Cons((k',v),xs) => if k==k' then Some(v) else list_find(k,xs)
    }
}

function list_remove<K(==,!new),V(!new)>(k:K,l:List<(K,V)>) : List<(K,V)>
decreases l
ensures forall k' , v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k != k')
{
    match l 
    {
        case Nil => Nil
        case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
        Cons((k',v),list_remove(k,xs))
    } 
}


class Hashtable<K(==,!new),V(!new)> {
    var size : int
    var data : array<List<(K,V)>>
    var Map : map<K, Option<V>>

    ghost predicate valid_hash(d: array<List<(K,V)>>, i: int) 
    requires 0 <= i < d.Length
    reads d
    {
       forall k,v :: mem((k,v),d[i]) ==> bucket(k, d.Length) == i
    }

    ghost predicate valid_data(k: K, v: V, m: map<K, Option<V>>, d: array<List<(K,V)>>)
    requires d.Length > 0
    reads d
    {
        mem((k,v), d[bucket(k, d.Length)]) ==> k in m && m[k] == Some(v)
    }

    ghost predicate Valid()
    reads this, data
    {
        data.Length > 0 &&
        (forall i:int :: 0 <= i < data.Length ==> valid_hash(data, i))
        &&
        forall k,v :: valid_data(k,v,Map,data)
    }

    constructor(n: int)
    requires n > 0
    ensures data.Length > 0
    {
        size := 0;
        data := new List<(K,V)>[n];
    }

    function hash(key: K) : int

    function bucket(k: K, n: int) : int
    requires n > 0
    {
        hash(k) % n
    }

    method clear() 
    {
        
    }

    method resize()
    requires data.Length > 0
    ensures old(data.Length) < data.Length
    ensures fresh(data)
    ensures Valid()
    modifies data, `data, `size
    {
        var newData := new List<(K,V)>[data.Length*2];
        var i := data.Length - 1;

        while(i >= 0)
        decreases i
        invariant -1 <= i < data.Length
        {
            var current := data[i];

            if(current != Nil) {
                while (current != Nil)
                decreases current
                invariant current != Nil
                {
                    var hash := bucket(current.head.0, newData.Length);
                    newData[hash] := Cons(current.head, newData[hash]);

                    assert(mem((current.head.0, current.head.1), newData[hash]));
                    current := current.tail;
                    break;
                }
            }

            i := i - 1;
        }
        
        data := newData;
    }

    method find(k: K) returns (r: Option<V>)
    {
        /*
        matchlistfin(k,l)
        case none => ...
        case some(V) => ...
        */
        r := None;
    }

    method remove(k: K)
    {
        /*
        match listfind(k.l)
        case none => ...
        case some(V) => ...
        */
    }

    method add(k: K,v: V)
    requires data.Length > 0
    ensures exists i:int :: 0 <= i < data.Length && mem((k,v), data[i])
    ensures Valid()
    modifies data, `data, `size 
    {
        var oldData := data;
        var oldSize := data.Length;

        if(size >= data.Length * 3/4) {
            resize();
        }

        remove(k);
        var hash := bucket(k, data.Length);
        data[hash] := Cons((k,v), data[hash]);

        assert(mem((k,v), data[hash]));

        size := size + 1;

        if(data.Length == oldSize) {
            // the key-value pair was not added to data because resize was not called
            assert(mem((k,v), oldData[hash]));
            assert(exists i :: 0 <= i < data.Length && mem((k,v), data[i]));
        }
    }
}
