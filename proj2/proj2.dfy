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
        mem((k,v), d[bucket(k, d.Length)]) <==> (k in m && m[k] == Some(v))
    }

    ghost predicate Valid()
    reads this, data
    {
        data.Length > 0 &&
        (forall i:int :: 0 <= i < data.Length ==> valid_hash(data, i))
        &&
        (forall k,v :: valid_data(k,v,Map,data))
    }

    constructor(n: int)
    requires n > 0
    ensures data.Length > 0
    ensures Valid()
    {
        size := 0;
        data := new List<(K,V)>[n] (i => Nil);
        Map := map[];
    }

    function hash(key: K) : int

    function bucket(k: K, n: int) : int
    requires n > 0
    {
        hash(k) % n
    }

    method clear()
    requires Valid()
    ensures old(data.Length) == data.Length
    ensures fresh(data)
    ensures Valid()
    modifies this, data, `data
    {
        size := 0;
        data := new List<(K,V)>[data.Length](i => Nil);
        Map := map[];
    }


method rehash(l: List<(K,V)>, newData: array<List<(K,V)>>, newSize:int, i:int, oldSize:int) returns (newList:())
    requires newData != data
    requires newData.Length == data.Length*2 == newSize
    requires 0 < oldSize == data.Length
    requires forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == i
    requires forall k,v :: (if 0 <= bucket(k, oldSize) < i then valid_data(k, v, Map, newData)
                            else if bucket(k, oldSize) == i then ((k in Map && Map[k] == Some(v)) <==> mem((k,v), l) || mem((k,v), newData[bucket(k, newData.Length)]))
                            else !mem((k,v), newData[bucket(k, newData.Length)]))
    ensures forall j :: 0 <= j < newSize ==> valid_hash(newData, j)
    ensures forall k,v :: (if 0 <=bucket(k, oldSize) <= i then valid_data(k, v, Map, newData)
                           else !mem((k,v), newData[bucket(k, newData.Length)]))
    decreases l
    modifies newData
    {
        match l
        {
            case Nil => return ();
            case Cons((k,v), xs) =>
                var newHash := bucket(k, newSize);
                assert(exists v:V :: mem((k,v),l));
                newData[newHash] := Cons((k,v), newData[newHash]);
                assert(mem((k,v), newData[newHash]));
                var newList' := rehash(xs, newData, newSize, i, oldSize);
                return newList';
        }
    }

    method resize()
    requires data.Length > 0
    requires size > 0
    requires Valid()
    ensures old(data.Length) < data.Length
    ensures fresh(data)
    ensures Valid()
    modifies this, data
    {
        var oldSize := data.Length;
        var newSize := data.Length*2;
        var newData := new List<(K,V)>[newSize];
        var i := 0;

        while(i < data.Length)
        decreases data.Length - i
        modifies data, newData
        invariant 0 <= i < data.Length
        invariant data.Length*2== newData.Length == newSize
        invariant data.Length == oldSize
        invariant newSize == 2*oldSize
        assert Valid();
        {
            var _ := rehash(data[i], newData, newSize, i, oldSize);
            i := i + 1;
        }

        data := newData;
    }

    method find(k: K) returns (r: Option<V>)
        requires data.Length > 0
        requires Valid()
        ensures Valid()
    {
        var i := data.Length - 1;
        r:= None;

        while (i >= data.Length)
        decreases i
        invariant -1 <= i < data.Length
        {
            match list_find(k,data[i])
                case None =>
                case Some(V) => r := Some(V);
            i := i -1;
        }
    }

    method remove(k: K)
    requires data.Length > 0
    requires Valid()
    ensures size <= old(size)
    ensures Valid()
    modifies this, data, `data, `size
    {
        var i := data.Length - 1;

        var hash := bucket(k, data.Length);
        match list_find(k, data[hash])
                case None =>
                    assert(forall v:V:: !mem((k,v), data[hash]));
                    assert(size == old(size));
                    assert(Valid());
                case Some(V) =>
                    assert(exists v:V:: mem((k,v), data[hash]));
                    assert forall k,v :: valid_data(k,v,Map,data) && (k in Map && Map[k] == Some(v)) <==> mem((k,v),data[bucket(k,data.Length)]);
                    data[hash] := list_remove(k, data[hash]);
                    Map := Map[k := None];
                    assert(forall v:V:: !mem((k,v), data[hash]));
                    assert(Map[k] == None);
                    size := size - 1;
                    assert(size < old(size));
                    assert forall k,v :: valid_data(k,v,Map,data) && (k in Map && Map[k] == Some(v)) <==> mem((k,v),data[bucket(k,data.Length)]);
                    assert(Valid());
    }


    method add(k: K,v: V)
    requires data.Length > 0
    requires Valid()
    ensures exists i:int :: 0 <= i < data.Length && mem((k,v), data[i])
    ensures Valid()
    modifies this, data, `data, `size
    {
        var oldData := data;
        var oldSize := data.Length;

        if(size >= data.Length * 3/4) {
            resize();
        }

        remove(k);
        var hash := bucket(k, data.Length);
        data[hash] := Cons((k,v), data[hash]);
        Map := Map[k := Some(v)];

        assert(mem((k,v), data[hash]));

        size := size + 1;

        if(data.Length == oldSize) {
            // the key-value pair was not added to data because resize was not called
            assert(mem((k,v), oldData[hash]));
            assert(exists i :: 0 <= i < data.Length && mem((k,v), data[i]));
        }
    }
}
