--------------------------- MODULE SimpleProgram ---------------------------

(*
Example 01

This is an encoding of a simple program, corresponding to the following
pseudo-C code:

int i;
void simpleProgram() {
    i = someNumber(); // A number between 0 and 1000
    i = i + 1;
}

The implementation below uses a program counter to encode control flow.

In relations defined steps, non-primed variables denote present values, 
and primed ones are values after taking a step.
*)

EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"

Add1 == \/ /\ pc = "middle"
           /\ i' = i + 1
           /\ pc' = "done"

Next == \/ Pick
        \/ Add1

=============================================================================