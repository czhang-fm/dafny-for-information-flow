include "WhileProgram.dfy"
include "VSITypeSystem.dfy"

module VSISoundness {
    import opened WhileProgram
    import opened VolpanoSmithIrvine

    /** In the following we prove the type information is preserved by SOS */
    lemma SubjectReduction(s: MState, ctx: Context, c: Cmd) returns (s': MState, c': Cmd)
    requires typeOK(s) && VariablesInCmd(c) <= s.Keys
    requires VariablesInCmd(c) <= ctx.Keys
    requires HasCmdType(ctx, c) != Invalid
    ensures TransitionSmallStep(s, c) == (s', c')
    ensures VariablesInCmd(c') <= ctx.Keys
    ensures HasCmdType(ctx, c') != Invalid
    {
        match c{
            case Skip => // termination
                s', c' := s, c; 
                assert TransitionSmallStep(s, c) == (s', c');
            case Assn(x, e) => // assignment
                s', c' := s[x:= Evaluate(s, e)], Skip;
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case If(e, c1, c2) => // if-then-else
                var res := Evaluate(s, e);
                if (res != 0) {
                    s', c' := s, c1;
                } else {
                    s', c' := s, c2;
                } 
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case While(e, c1) => // while-loop
                var res := Evaluate(s, e);
                if (res != 0) {
                    s', c' := s, Seq(c1, c);
                } else {
                    s', c' := s, Skip;
                } 
                assert TransitionSmallStep(s, c) == (s', c');
                assert VariablesInCmd(c') <= ctx.Keys;
            case Seq(c1, c2) => // sequential composition
                match c1 {
                    case Skip => 
                        s', c' := SubjectReduction(s, ctx, c2); 
                        assert TransitionSmallStep(s, c) == (s', c');
                    case _ => 
                        var s1', c1' := SubjectReduction(s, ctx, c1); 
                        s' := s1';
                        c' := Seq(c1', c2);
                        assert TransitionSmallStep(s, c) == (s', c');
                }
                assert VariablesInCmd(c') <= ctx.Keys;
        }
    }

    /**  We prove the information flow security is enforced by the VSI type checking
     */
}