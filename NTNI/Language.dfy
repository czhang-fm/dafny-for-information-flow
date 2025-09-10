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

    // If an expression is a value, we can unwrap it
    function Expression2Value(e: Expression) : Value
    requires e.Val?
    {
        match e {
            case Val(value) => value
        }
    }
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
            case Alloc(a, e2) => FreeVariables(e2)
            case Assn(l, r) => FreeVariables(l) + FreeVariables(r)
            case App(f, e2) => FreeVariables(f) + FreeVariables(e2)
            case Deref(e2) => FreeVariables(e2)
            case If(cond, thn, els) => FreeVariables(cond) + FreeVariables(thn) + FreeVariables(els)
            case Plus(l, r) => FreeVariables(l) + FreeVariables(r)
        }
    }
    // substitute each occurrence of y in e1 with e2
    function Subst(e1: Expression, y: Variable, e2: Expression): Expression 
    {
        // the case that y does not appear in e1 should be handled directly in the semantics
        if ! (y in FreeVariables(e1)) then e1 else (
            if e1.Val? then (if e1.v.Func? then var fun := Expression2Value(e1); Val(Func(fun.x, Subst(fun.e, y, e2))) else e1)
            else if e1.Var? then (if e1.x == y then e2 else e1)
            else if e1.Alloc? then Alloc(e1.a, Subst(e1.e, y, e2))
            else if e1.Assn? then Assn(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
            else if e1.App? then App(Subst(e1.f, y, e2), Subst(e1.e, y, e2))
            else if e1.Deref? then Deref(Subst(e1.e, y, e2))
            else if e1.If? then If(Subst(e1.cond, y, e2), Subst(e1.thn, y, e2), Subst(e1.els, y, e2))
            else Plus(Subst(e1.l, y, e2), Subst(e1.r, y, e2))
        )
    }
    // This defines a large-step operational semantics
    function Eval(m1: MState, e: Expression): (MState, Value)

 }