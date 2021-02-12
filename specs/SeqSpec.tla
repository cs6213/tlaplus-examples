\* Copyright: Leslie Lamport, The TLA+ Video Course
\* http://lamport.azurewebsites.net/video/videos.html

---- MODULE SeqSpec ----
EXTENDS TLC, Integers, Sequences


(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]

\* Try to evaluate this using the VSCode action
x == Remove(3, <<1,2,3,4>>)

====
