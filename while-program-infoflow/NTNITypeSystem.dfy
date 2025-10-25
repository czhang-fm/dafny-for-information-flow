include "WhileProgram.dfy"

/** This file defines the Nontransitive Noninterference type system
 *  which is proved to be sound for secure informaiton flow in 
 *  a While-loop programming language */

module NontransitiveFlow{
    import opened WhileProgram

    // The security labels
    type Label(==)
    const labels: set<Label>
    // The reflexive flow relation on Labels, which is a global policy
    const flow: set<(Label, Label)>
    // lemma {: axiom} ReflexiveFlow(l: Label)
    // requires l in labels 
    // ensures (l, l) in flow
    // An initial labelling on variables
    // Intuitively, an "unimportant" variable may be labelled by \top 
    // which may influence any other labels and may accept information flow from any other labels
    const coarse_label: map<Variable, Label>
    predicate policyTypeOK(){
        && coarse_label.Keys == variables
        && (forall l :: l in labels ==> (l, l) in flow)
        && forall x :: x in variables ==> coarse_label[x] in labels
    }

    // The set of labels that can interfere with a label
    // method CanFlow(l: Label) returns (incoming: set<Label>)
    // requires l in labels
    // ensures forall l':: l' in labels && (l',l) in flow ==> l' in incoming
    // ensures forall l':: l' in incoming ==> (l', l) in flow
    // ensures incoming <= labels
    // {
    //     incoming := (set l' | l' in labels && (l', l) in flow :: l');
    //     // assert forall l':: l' in labels && (l',l) in flow ==> l' in incoming;
    //     // assert forall l':: l' in incoming ==> (l', l) in flow;
    // }
    function CanFlow(l: Label): set<Label>
    requires l in labels
    ensures forall l':: l' in labels && (l',l) in flow ==> l' in CanFlow(l)
    ensures forall l':: l' in CanFlow(l) ==> (l', l) in flow
    ensures CanFlow(l) <= labels
    {
        (set l' | l' in labels && (l', l) in flow :: l')
    }

    // Testing for all labels l, l is in the set of labels in CanFlow(l)
    method TestSelfFlow(l: Label)
    requires l in labels
    requires policyTypeOK()
    {
        var lset := CanFlow(l);
        // ReflexiveFlow(l);
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
    //// In principle, this function should never produce Invalid
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
    // The type checking process for a command/statement
    // If type checking fails the return type will be Invalid
    function HasCmdType(ctx: Context, pc: set<Label>, c:Cmd): PhraseType
    requires policyTypeOK()
    requires VariablesInCmd(c) <= ctx.Keys && pc <= labels
    requires VariablesInCmd(c) <= variables
    requires forall x :: x in ctx.Keys ==> ctx[x] <= labels
    {
        match c {
            case Skip => CmdType({})
            case Assn(x, e) =>  
                // t1 is the policy label of x; t2 represents information from RHS of assn
                var t1, t2 := coarse_label[x], HasExprType(ctx, e); 
                if t2 == Invalid then Invalid
                else 
                    // get the set of labels allowed to influence label(x)
                    var flowsFrom := CanFlow(t1); 
                    if (GetBaseType(t2) + pc) <= ctx[x] && (GetBaseType(t2) + pc) <= flowsFrom
                    then CmdType({t1}) else Invalid
            case If(e, c1, c2) => CmdType({})
            case While(e, c1) => CmdType({})
            case Seq(c1, c2) => CmdType({})
        }
    }
}