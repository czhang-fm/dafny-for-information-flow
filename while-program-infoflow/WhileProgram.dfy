/* We start with the syntax and semantics for the simple while language 
 */
module WhileProgram{
    type Variable(==)
    datatype Expr = 
        | Num(n: int) 
        | Var(x: Variable) 
        | Plus(e1: Expr, e2: Expr)
    datatype Cmd = 
        | Skip 
        | Assn(x: Variable, e: Expr) 
        | If(cond: Expr, thn: Cmd, els: Cmd) 
        | While(cond: Expr, c: Cmd)
        | Seq(c1: Cmd, c2: Cmd)

    /* In the following we define the SOS rules */
    const variables: set<Variable>
    type MState = map<Variable, int>
    ghost predicate typeOK(s: MState){
        s.Keys <= variables
    }
    /* The set of variables in an expression */
    function VariablesInExpr(e: Expr): set<Variable>
    {
        match e {
            case Num(_) => {}
            case Var(x) => {x}
            case Plus(e1, e2) => VariablesInExpr(e1) + VariablesInExpr(e2)
        }
    }
    /* The set of variables in a program */
    function VariablesInCmd(c: Cmd): set<Variable>
    {
        match c {
            case Skip => {}
            case Assn(x, e) => {x} + VariablesInExpr(e)
            case If(e, c1, c2) => VariablesInExpr(e) + VariablesInCmd(c1)+ VariablesInCmd(c2)
            case While(e, c) => VariablesInExpr(e) + VariablesInCmd(c)
            case Seq(c1, c2) => VariablesInCmd(c1)+ VariablesInCmd(c2)
        }
    }
    function Evaluate(s: MState, e: Expr) : int
    requires typeOK(s) && VariablesInExpr(e) <= s.Keys
    {
        match e {
            case Num(n) => n
            case Var(x) => s[x]
            case Plus(e1, e2) => Evaluate(s, e1) + Evaluate(s, e2)
        }
    }

    function TransitionSmallStep(s: MState, c: Cmd) : (MState, Cmd)
    requires typeOK(s) && VariablesInCmd(c) <= s.Keys
    decreases c
    {
        match c {
            case Skip => // termination
                (s, c) 
            case Assn(x, e) => // assignment
                (s[x:= Evaluate(s, e)], Skip)
            case If(e, c1, c2) => // if-then-else
                var res := Evaluate(s, e);
                if (res != 0) then (s, c1) else (s, c2)
            case While(e, c1) => // while-loop
                var res := Evaluate(s, e);
                if (res != 0) then (s, Seq(c1, c)) else (s, Skip)
            case Seq(c1, c2) => // sequential composition
                match c1 {
                    case Skip => TransitionSmallStep(s, c2)
                    case _ => 
                        var (s', c') := TransitionSmallStep(s, c1); (s', Seq(c', c2))
                }
        }
        
    }
    lemma AssignmentTest(s: MState, x: Variable, value: int)
    requires typeOK(s) && x in s.Keys
    {
        var (s1, c1) := TransitionSmallStep(s, Assn(x, Num(value)));
        assert s1[x] == value;
    }
    lemma TransitionSmallStepTypeOK(s: MState, c: Cmd, s': MState, c': Cmd)
    requires typeOK(s) && VariablesInCmd(c) <= s.Keys
    requires (s', c') == TransitionSmallStep(s, c)
    ensures s.Keys == s'.Keys
    ensures typeOK(s') && VariablesInCmd(c') <= s'.Keys
    {}

}