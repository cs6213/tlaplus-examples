------------------------------ MODULE ABSpec --------------------------------
(* Example 05: Alternating bit protocols specification. *)

EXTENDS Integers

CONSTANT Data  \* The set of all possible data values.

VARIABLES AVar,   \* The last <<value, bit>> pair A decided to send.
          BVar    \* The last <<value, bit>> pair B received.
          
(***************************************************************************)
(* Type correctness means that AVar and BVar are tuples <<d, i>> where     *)
(* d \in Data and i \in {0, 1}.                                            *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}

(***************************************************************************)
(* It's useful to define vars to be the tuple of all variables, for        *)
(* example so we can write [Next]_vars instead of [Next]_<< ...  >>        *)
(***************************************************************************)
vars == << AVar, BVar >>


(***************************************************************************)
(* Initially AVar can equal <<d, 1>> for any Data value d, and BVar equals *)
(* AVar.                                                                   *)
(***************************************************************************)
Init == /\ AVar \in Data \X {1} 
        /\ BVar = AVar

(***************************************************************************)
(* When AVar = BVar, the sender can "send" an arbitrary data d item by     *)
(* setting AVar[1] to d and complementing AVar[2].  It then waits until    *)
(* the receiver "receives" the message by setting BVar to AVar before it   *)
(* can send its next message.  Sending is described by action A and        *)
(* receiving by action B.                                                  *)
(***************************************************************************)
A == /\ AVar = BVar \* This conjunct in enabling for this action
     /\ \E d \in Data: AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* For understanding the spec, it's useful to define formulas that should  *)
(* be invariants and check that they are invariant.  The following         *)
(* invariant Inv asserts that, if AVar and BVar have equal second          *)
(* components, then they are equal (which by the invariance of TypeOK      *)
(* implies that they have equal first components).                         *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

-----------------------------------------------------------------------------

TempProp == \A v \in Data \X {0, 1}: AVar = v ~> BVar = v


(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps via Next as long as these steps are enabled.                      *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next) 

\* Alternative, weaker fairness: only B is mandated to take a step
\* But A can stop taking steps at any point.
FairSpecB == Spec /\ WF_vars(B) 

=============================================================================

