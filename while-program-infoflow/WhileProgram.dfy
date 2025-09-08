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
    predicate EmptyCmd(c: Cmd)
    {
        match c
        case Skip => true
        case _ => false
    }

    // Next we define how a program terminates within n steps of transitions
    predicate Terminates(c: Cmd, s: MState, s': MState, n: int)
    requires typeOK(s) && typeOK(s') && n >= 0
    requires VariablesInCmd(c) <= s.Keys == s'.Keys
    decreases n
    {
        match c {
            case Skip => s == s' && n == 0
            case _ => 
                var (s1, c1) := TransitionSmallStep(s, c); 
                TransitionSmallStepTypeOK(s, c, s1, c1);
                // assert !EmptyCmd(c);
                n >= 1 && Terminates(c1, s1, s', n-1)
        }
    }
    // One step termination: after a small step, the remaining program terminates
    lemma {:induction false} SmallStepTermination(s1: MState, s2: MState, c: Cmd, k: int) returns (s': MState, c': Cmd)
    requires typeOK(s1) && typeOK(s2) && k >= 0
    requires VariablesInCmd(c) <= s1.Keys == s2.Keys
    requires Terminates(c, s1, s2, k)
    requires !EmptyCmd(c)
    ensures typeOK(s')
    ensures (s', c') == TransitionSmallStep(s1, c) 
    ensures VariablesInCmd(c') <= s'.Keys == s2.Keys
    ensures Terminates(c', s', s2, k-1)
    {
        match c {
            case Skip => 
                assert false;
            case Assn(x, e) => // assignment
                s', c' := s1[x:= Evaluate(s1, e)], Skip;
                assert typeOK(s');
                assert VariablesInCmd(c') <= s'.Keys == s2.Keys;
                assert k >= 1;
                assert Terminates(c', s', s2, k-1); assert s2 == s';
            case If(e, c1, c2) => // if-then-else
                var res := Evaluate(s1, e);
                if (res != 0){
                    s', c' := s1, c1;
                } else {
                    s', c' := s1, c2;
                }
                assert typeOK(s');
                assert k >= 1;
            case While(e, c1) => // while-loop
                var res := Evaluate(s1, e);
                if (res != 0){
                    s', c' := s1, Seq(c1, c);
                } else {
                    s', c' := s1, Skip;
                }
                assert typeOK(s');
                assert k >= 1;
            case Seq(c1, c2) => // sequential composition
                match c1 {
                    case Skip => 
                        var p := TransitionSmallStep(s1, c2);
                        s', c' := p.0, p.1;
                        TransitionSmallStepTypeOK(s1, c, s', c');
                        assert typeOK(s');
                        assert k >= 1;
                    case _ => 
                        var (s3, c3) := TransitionSmallStep(s1, c1); 
                        s', c' := s3, Seq(c3, c2);
                        TransitionSmallStepTypeOK(s1, c, s', c');
                        assert typeOK(s');
                        assert k >= 1;
                }
        }
        assert Terminates(c', s', s2, k-1);  
        assert VariablesInCmd(c') <= s'.Keys == s2.Keys;
        assert Terminates(c', s', s2, k-1);
    }
    // The complement of the above lemma, to prove later ...
    lemma {:axiom} SkipTermination(s1: MState, s2: MState, c: Cmd, k: int)
    requires typeOK(s1) && typeOK(s2) && k >= 0
    requires VariablesInCmd(c) <= s1.Keys == s2.Keys
    requires Terminates(Seq(Skip, c), s1, s2, k)
    ensures Terminates(c, s1, s2, k)
    // {}

    // Multiple step termination for sequential composition
    lemma {:induction false} Sequencing(s1: MState, s2: MState, c1: Cmd, c2: Cmd, k: int) returns (s': MState, k': int)
    requires typeOK(s1) && typeOK(s2) && k >= 0
    requires VariablesInCmd(c1) <= s1.Keys == s2.Keys
    requires VariablesInCmd(c2) <= s1.Keys == s2.Keys
    requires Terminates(Seq(c1, c2), s1, s2, k)
    // requires !EmptyCmd(c1)
    ensures typeOK(s') 
    ensures k' >= 0 && k - k' >= 0 
    ensures VariablesInCmd(c1) <= s1.Keys == s2.Keys == s'.Keys
    ensures VariablesInCmd(c2) <= s1.Keys == s2.Keys == s'.Keys
    ensures Terminates(c1, s1, s', k')
    ensures Terminates(c2, s', s2, k - k')
    decreases k, c1, c2
    {
        if (EmptyCmd(c1)){ // c1 == Skip // the base case
            s' := s1; 
            k' := 0;
            assert typeOK(s');
            SkipTermination(s1, s2, c2, k);
            assert Terminates(c1, s1, s', k');
            assert Terminates(c2, s', s2, k - k');
        } else {
            // need to consider a number of cases for c1
            match c1 {
                case Seq(c3, c4) => // sequential composition
                    // if (EmptyCmd(c3) && EmptyCmd(c4)){ // Seq(Skip, Skip) => Skip 
                    //     s' := s1; 
                    //     k' := 1;
                    //     assert Terminates(c1, s1, s', k');
                    //     assert Terminates(c2, s', s2, k - k');
                    // } // the above case is covered by the following case
                    if (EmptyCmd(c3)) {
                        var (s3, c5) := TransitionSmallStep(s1, c4);
                        assert (s3, Seq(c5, c2)) == TransitionSmallStep(s1, Seq(c1, c2));
                        TransitionSmallStepTypeOK(s1, Seq(c1,c2), s3, Seq(c5,c2));
                        assert Terminates(Seq(c5, c2), s3, s2, k-1);
                        assert typeOK(s3);
                        var s4, k2 := Sequencing(s3, s2, c5, c2, k-1);
                        s', k' := s4, k2+1;
                        assert Terminates(c2, s', s2, k-k');
                        assert Terminates(c1, s1, s', k');
                    } else {
                        var (s3, c5) := TransitionSmallStep(s1, c3); 
                        assert (s3, Seq(Seq(c5, c4), c2)) == TransitionSmallStep(s1, Seq(c1, c2));
                        TransitionSmallStepTypeOK(s1, Seq(c1,c2), s3, Seq(Seq(c5, c4), c2));
                        assert Terminates(Seq(Seq(c5, c4), c2), s3, s2, k-1);
                        assert typeOK(s3);
                        var s4, k2 := Sequencing(s3, s2, Seq(c5, c4), c2, k-1);
                        s', k' := s4, k2+1;
                    }
                case _ =>
                    var (s3, c3) := TransitionSmallStep(s1, c1);
                    assert (s3, Seq(c3, c2)) == TransitionSmallStep(s1, Seq(c1, c2));
                    TransitionSmallStepTypeOK(s1, Seq(c1, c2), s3, Seq(c3, c2));
                    assert Terminates(Seq(c3, c2), s3, s2, k-1);
                    assert typeOK(s3);
                    var s4, k2 := Sequencing(s3, s2, c3, c2, k-1);
                    assert Terminates(c3, s3, s4, k2); 
                    assert Terminates(c1, s1, s4, k2 + 1);
                    s', k' := s4, k2+1;
                    assert Terminates(c2, s4, s2, k-k'); 
            }
        }
    }
}