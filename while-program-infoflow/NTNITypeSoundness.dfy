include "WhileProgram.dfy"
include "NTNITypeSystem.dfy"

module NTNISoundness {
    import opened WhileProgram
    import opened NontransitiveFlow

    /** We prove the nontransitive information flow security is enforced by the type system
     *  NTNI security for program c:
     *  For all label l in labels, for all states M1 =CanFlow(l)= M2
     *  (M1, c) ==>* (M1', Skip) /\ (M2, c) ==>* (M2, Skip)
     *  we have M1 ={l}= M2
     *  This says the l component of a state can only be influenced by the components labeled by l'
     *  with (l', l) in flow as defined by the (global) security policy
     */
}