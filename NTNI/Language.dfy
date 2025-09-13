/** We start with the syntax and semantics for the simple functional programming language
 */
 include "AuxiliaryLemmas.dfy"

 module Language{

    import opened Auxiliaries

    type Variable(==)
    type Address = nat

    // const variables : iset<Variable>
    
    datatype Value = 
        | Err
        | Num(n: int)
        | Addr(a: Address)
        | Func(x: Variable, e: Expression)
    datatype Expression = 
        | Val(v: Value)
        | Var(x: Variable)
        | Alloc(e: Expression)    // new_a e
        | Assn(l: Expression, r: Expression)  // e := e
        | App(f: Expression, e: Expression)   // e e
        | Deref(e: Expression)                // !e
        | If(cond: Expression, thn: Expression, els: Expression) // if e then e else e
        | Plus(l: Expression, r: Expression)  // e \oplus e
    /**
     * In the following we define rules for the big-step operational semantics
     */ 
 
    type MState = map<Address, Value>

    lemma {: axiom} FreshVariable(vars : set<Variable>) returns (v: Variable)
    ensures v !in vars

    // Get a set of free variables in an expression
    function FreeVariables(e: Expression) : set<Variable>
    {
        match e {
            case Val(v) =>
                match v {
                    case Func(y, e2) => FreeVariables(e2) - {y}
                    case _ => {}
                }
            case Var(x) => {x}
            case Alloc(e2) => FreeVariables(e2)
            case Assn(l, r) => FreeVariables(l) + FreeVariables(r)
            case App(f, e2) => FreeVariables(f) + FreeVariables(e2)
            case Deref(e2) => FreeVariables(e2)
            case If(cond, thn, els) => FreeVariables(cond) + FreeVariables(thn) + FreeVariables(els)
            case Plus(l, r) => FreeVariables(l) + FreeVariables(r)
        }
    }
    // substitute each occurrence of y in e1 with e2
    function Subst(e1: Expression, y: Variable, e2: Expression): Expression 
    requires y !in FreeVariables(e2)
    ensures FreeVariables(Subst(e1, y, e2)) <= FreeVariables(e1) + FreeVariables(e2) - {y}
    {
        // the case that y does not appear in e1 should be handled directly in the semantics
        if ! (y in FreeVariables(e1)) then e1 else (
            if e1.Val? then (if e1.v.Func? then var fun := e1.v; Val(Func(fun.x, Subst(fun.e, y, e2))) else e1)
            else if e1.Var? then (if e1.x == y then e2 else e1)
            else if e1.Alloc? then Alloc(Subst(e1.e, y, e2))
            else if e1.Assn? then Assn(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
            else if e1.App? then App(Subst(e1.f, y, e2), Subst(e1.e, y, e2))
            else if e1.Deref? then Deref(Subst(e1.e, y, e2))
            else if e1.If? then If(Subst(e1.cond, y, e2), Subst(e1.thn, y, e2), Subst(e1.els, y, e2))
            else Plus(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
        )
    }

    // This defines a large-step operational semantics
    method Eval(m: MState, e: Expression) returns (m': MState, v: Value)
    requires FreeVariables(e) == {} // e contains no free variable
    requires forall a : Address :: a in m ==> FreeVariables(Val(m[a])) == {}
    ensures FreeVariables(Val(v)) == {}
    ensures forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}
    decreases *
    {
        match e {
            case Val(_) => m', v := m, e.v; assert FreeVariables(Val(v)) == {}; // *
            // case Var(x) => 
            case Alloc(e2) => 
                // ALLOC 
                var m1, v1 := Eval(m, e2);
                // var a: Address :| a !in m1;
                var a := FindFresh(m.Keys); 
                m', v := m1[a := v1], Addr(a); 
                assert FreeVariables(Val(v)) == {}; 
                assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
            case Assn(l, r) => 
                // ASSIGN
                var m1, a := Eval(m, l); 
                var m2, v := Eval(m1, r);
                if a.Addr?{
                    m', v := m2[a.a := v], v;
                } else {
                    m', v := m2, Err;
                }
                assert FreeVariables(Val(v)) == {}; 
                assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
            case App(f, e2) => 
                // APP
                var m1, f1 := Eval(m, f);
                assert FreeVariables(Val(f1)) == {};
                if f1.Func?{
                    var m2, v := Eval(m1, e2);
                    assert FreeVariables(Val(v)) == {};
                    var e3 := Subst(f1.e, f1.x, Val(v));
                    assert FreeVariables(e3) == {};
                    m', v := Eval(m2, e3);
                    assert FreeVariables(Val(v)) == {};
                } else {
                    m', v := m1, Err;
                    assert FreeVariables(Val(v)) == {};
                }
            case Deref(e2) => 
                // DEREF
                var m1, v := Eval(m, e2);
                if v.Addr? && v.a in m1 {
                    m', v := m1, m1[v.a]; // v.a might not be in the domain of m1 ?
                } else {
                    m', v := m1, Err;
                }
                assert FreeVariables(Val(v)) == {}; 
                assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
                
            case If(cond, thn, els) => 
                // THEN && ELSE
                var m1, v1 := Eval(m, cond);
                if v1.Num? {
                    if v1.n != 0 {
                        m', v := Eval(m1, thn);
                    } 
                    else {
                        m', v := Eval(m1, els);
                    }
                } else {
                    m', v := m1, Err; // map[], Err;
                }
                assert FreeVariables(Val(v)) == {}; 
                assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
            case Plus(l, r) => 
                // OP
                var m1, v1 := Eval(m, l);
                var m2, v2 := Eval(m1, r);
                if v1.Num? && v2.Num?{
                    m', v := m2, Num(v1.n + v2.n);
                } else {
                    m', v := m2, Err;
                }
                assert FreeVariables(Val(v)) == {}; 
                assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
            // case _ => m', v := m, Err;
        }
        // assert FreeVariables(Val(v)) == {}; 
        // assert forall a : Address :: a in m' ==> FreeVariables(Val(m'[a])) == {}; // *
    }

 }