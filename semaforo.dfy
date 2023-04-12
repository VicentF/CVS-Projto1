datatype color = Yellow | Red | Green

class Semaforo {

    var c: color;

    constructor()
    {
        c := Green;
    }

    predicate isYellow()
    reads `c
    {
        c == Yellow
    }

    predicate isGreen()
    reads `c
    {
        c == Green
    }

    predicate isRed()
    reads `c
    {
        c == Red
    }

    method turnRed() 
    requires isYellow()
    ensures isRed()
    modifies `c
    {
        c := Red;
    }

    method turnGreen() 
    requires isYellow()
    ensures isGreen()
    modifies `c
    {
        c := Green;
    }

    method turnYellow() 
    requires isRed() || isGreen()
    ensures isYellow()
    modifies `c
    {
        c := Yellow;
    }
}

method Main()
{
    var s := new Semaforo();
    assert s.isGreen();
    s.turnRed();
}
