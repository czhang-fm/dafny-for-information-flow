/** We start with the syntax and semantics for the simple functional programming language
 */

 module Language{
    type Variable(==)
    type Address(==)
    
    datatype Value = 
        | Num(n: int)
        | Addr(a: Address)
        | Func(x: Variable, e: Expression)
    datatype Expression = 
        | Val(v: Value)
        | Var(x: Variable)
        | Alloc(a: Address, e: Expression)
        | Assn(l: Expression, r: Expression)
        | App(f: Expression, e: Expression)
        | Deref(e: Expression)
        | If(cond: Expression, thn: Expression, els: Expression)
        | Plus(l: Expression, r: Expression)
    /**
     * In the following we define rules for the big-step operational semantics
     */ 
 
    type MState = map<Address, Value>

    function Expression2Value(e: Expression) : Value
    requires e.Val?
    {
        match e {
            case Val(value) => value
        }
    }

    function Subst(e1: Expression, y: Variable, e2: Expression): Expression 
    // pre-conddition-1: y must be free in e1 // the case that y does not appear in e1 should be handled directly in the semantics
    {
        if e1.Val? then (if e1.v.Func? then var fun := Expression2Value(e1); Val(Func(fun.x, Subst(fun.e, y, e2))) else e1)
        else if e1.Var? then (if e1.x == y then e2 else e1)
        else if e1.Alloc? then Alloc(e1.a, Subst(e1.e, y, e2))
        else if e1.Assn? then Assn(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
        else if e1.App? then App(Subst(e1.f, y, e2), Subst(e1.e, y, e2))
        else if e1.Deref? then Deref(Subst(e1.e, y, e2))
        else if e1.If? then If(Subst(e1.cond, y, e2), Subst(e1.thn, y, e2), Subst(e1.els, y, e2))
        else Plus(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
    }

    function Eval(m1: MState, e: Expression): (MState, Value)

 }