Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VSTArrayProgs.binary_search. (* Import the AST of this C program *)

(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Fixpoint sorted (l : list Z) : Prop :=
match l with
| [] => True
| _ :: [] => True
| x :: y :: l' => x <= y /\ sorted l'
end.
