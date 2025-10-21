module Auxiliaries {

    lemma SetIncrement(m: set<nat>, a: nat, b: nat)
    requires forall c :: c in m ==> c <= b
    requires a <= b
    ensures forall c :: c in m+{a} ==> c <= b
    {}

    method FindMax(m: set<nat>) returns (a: nat)
    ensures forall b :: b in m ==> b <= a
    decreases |m|
    {
        if |m| == 0 {
            a := 1;
            assert forall b :: b in m ==> b <= a;
        } else {
            var t :| t in m;
            var x := FindMax(m - {t});
            assert forall b :: b in m-{t} ==> b <= x;
            if x > t {
                assert forall b :: b in m-{t} ==> b <= x;
                a := x;
            } else {
                assert forall b :: b in m-{t} ==> b <= t;
                a := t;
            }
            assert forall b :: b in m-{t} ==> b <= a;
            assert t <= a;
            SetIncrement(m-{t}, t, a);
            assert forall b :: b in m-{t}+{t} ==> b <= a;
        }
    }
    method FindFresh(m: set<nat>) returns (a: nat)
    ensures a !in m
    {
        var b := FindMax(m);
        a := b + 1;
    }
}