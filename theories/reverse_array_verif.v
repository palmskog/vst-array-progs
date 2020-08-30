Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.floyd.sublist.
Require Import VSTArrayProgs.reverse_array. (* Import the AST of this C program *)

(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Fixpoint swap_pos_aux {A} (n : nat) (l : list A) (x : A) :=
match n, l with
| 0%nat, h :: l' => (h, x :: l')
| S n', h :: l' =>
  let (y, l0) := swap_pos_aux n' l' x in
  (y, h :: l0)
| _, [] => (x, [])
end.

Fixpoint swap_pos {A} (i j : nat) (l : list A) :=
match i, j, l with
| 0%nat, 0%nat, _ => l
| 0%nat, S j', h :: l' =>
  let (h0, l0) := swap_pos_aux j' l' h in
  h0 :: l0
| S i', 0%nat, h :: l' =>
  let (h0, l0) := swap_pos_aux i' l' h in
  h0 :: l0
| S i', S j', h :: l' => h :: swap_pos i' j' l'
| _, _, [] => []
end.

Definition Zswap_pos {A} (i j : Z) (l : list A) :=
  if zlt i 0 then [] else if zlt j 0 then []
  else swap_pos (Z.to_nat i) (Z.to_nat j) l.

Definition swap_spec :=
  DECLARE _swap
   WITH a : val, sh : share, contents : list Z, i : Z, j : Z
   PRE [ tptr tint, tint, tint ]
     PROP (writable_share sh;
          0 <= i < Zlength contents;
          0 <= j < Zlength contents;
          Zlength contents <= Int.max_signed;
          Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents)
     PARAMS (a; Vint (Int.repr i); Vint (Int.repr j))
     SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
   POST [ tvoid ]
     PROP () RETURN ()
     SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr (Zswap_pos i j contents))) a).

Definition Gprog : funspecs := ltac:(with_library prog [swap_spec]).

Lemma swap_pos_sym : forall A (l : list A) i j, swap_pos i j l = swap_pos j i l.
Proof.
induction l.
- intros i j; destruct i; destruct j; simpl; reflexivity.
- intros i j; destruct i; destruct j; simpl; try reflexivity.
  rewrite <- IHl.
  reflexivity.
Qed.

Lemma body_swap: semax_body Vprog Gprog f_swap swap_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
entailer!.
unfold data_at, field_at; simpl.
entailer!.
unfold at_offset.
entailer!.
unfold data_at_rec.
simpl.
entailer!.
unfold array_pred,aggregate_pred.array_pred.
entailer!.
- admit.
- unfold at_offset.
  erewrite aggregate_pred.rangespec_ext.
  * admit.
  * admit.
Admitted.
