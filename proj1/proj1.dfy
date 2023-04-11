function sum (a:array<int>, i:int, j:int) :int
decreases j
reads a
requires 0 <= i <= j <= a.Length
{
    if i == j then
        0
    else
        a[j-1] + sum(a, i, j-1)
}

method query (a:array<int>, i:int, j:int) returns (s:int)
requires 0 <= i <= j < a.Length
ensures s == sum(a, i, j)
{
    s := 0;
    var aux := i;

    while (aux < j)
    invariant i <= aux <= j
    invariant s == sum(a, i, aux)
    decreases  j - aux
    {
        s := s + a[aux];
        aux := aux + 1;
    }
    return s;
}





method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
requires is_prefix_sum_for(a,c) ∧ 0 <= i <= j <= a.Length ∧ a.Length < c.Length
{
    r:= 0;

    if i == 0{
        r := c[j - 1];
    }
    else {
        r := c[j-1] - c[i-1];
    }
    return r;
}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
reads c, a
{
    var i := c.Length;

    while (i >= 1)
    invariant 1 <= i <= c.Length
    decreases i
    {
        c[i] == sum(a,0,i-1);
        i := i - 1;
    }
}
