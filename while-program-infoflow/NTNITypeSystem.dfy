include "WhileProgram.dfy"

/** This file defines the Nontransitive Noninterference type system
 *  which is proved to be sound for secure informaiton flow in 
 *  a While-loop programming language */

module NontransitiveFlow{
    import opened WhileProgram

    // The security labels
    type Label(==)
    const labels: set<Label>
    // The reflexive flow relation on Labels
    const flow: set<(Label, Label)>
    lemma {: axiom} ReflexiveFlow(l: Label)
    requires l in labels 
    ensures (l, l) in flow

    // The set of labels that can interfere with a label
    method CanFlow(l: Label) returns (incoming: set<Label>)
    requires l in labels
    ensures forall l':: l' in labels && (l',l) in flow ==> l' in incoming
    ensures forall l':: l' in incoming ==> (l', l) in flow
    {
        incoming := (set l' | l' in labels && (l', l) in flow :: l');
        // assert forall l':: l' in labels && (l',l) in flow ==> l' in incoming;
        // assert forall l':: l' in incoming ==> (l', l) in flow;
    }
    // Testing for all labels l, l is in the set of labels in CanFlow(l)
    method TestSelfFlow(l: Label)
    requires l in labels
    {
        var lset := CanFlow(l);
        ReflexiveFlow(l);
        assert l in lset;
    }

    // The type language
    type BaseType = set<Label> 
    datatype PhraseType = ExprType(t: BaseType) | CmdType(t: BaseType) | Invalid
    type Context = map<Variable, BaseType>

    function GetBaseType(t: PhraseType) : BaseType
    requires t != Invalid
    {
        match t {
            case ExprType(t') => t'
            case CmdType(t') => t'
        }
    }
    // The meet and join are now set based operators
    function Join(t1: BaseType, t2: BaseType) : BaseType
    {
        t1 + t2
    }
    function Meet(t1: BaseType, t2: BaseType) : BaseType
    {
        t1 * t2
    }
    // The following defines a type system for the while programming language
    // We start with the expression types
    // This function never produces Invalid
    function HasExprType(ctx: Context, e: Expr): PhraseType
    requires VariablesInExpr(e) <= ctx.Keys
    decreases e
    {
        match e {
            case Num(n) => 
                ExprType({}) 
            case Var(x) => 
                ExprType(ctx[x])
            case Plus(e1, e2) => 
                var t1, t2 := HasExprType(ctx, e1), HasExprType(ctx, e2); 
                if t1 == Invalid || t2 == Invalid then Invalid 
                else ExprType(Join(GetBaseType(t1), GetBaseType(t2)))
        }
    }
}