Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.floyd.sublist.
Require Import VSTArrayProgs.binary_search. (* Import the AST of this C program *)
Require Import Lia.

Ltac do_compute_expr_warning::=idtac.

(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Fixpoint sorted (l : list Z) : Prop :=
match l with
| [] => True
| _ :: [] => True
| x :: y :: l' => x <= y /\ sorted l'
end.

Definition insertion_point (ip : Z) (key : Z) (l : list Z) :=
0 <= ip <= Zlength l /\
Forall (fun x => x < key) (sublist 0 ip l) /\
Forall (fun x => key < x) (sublist ip (Zlength l) l).

Definition binary_search_spec :=
 DECLARE _binary_search
  WITH a: val, sh : share, contents : list Z, len : Z, key : Z
  PRE [ tptr tint, tint, tint ]
          PROP (readable_share sh;
                 Zlength contents <= Int.max_signed;
                 len = Zlength contents;
                 Int.min_signed <= key <= Int.max_signed;
                 Forall (fun x => Int.min_signed <= x <= Int.max_signed) contents;
                 sorted contents)
          PARAMS (a; Vint (Int.repr len); Vint (Int.repr key))
          SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX i:Z,
         PROP (if in_dec Z.eq_dec key contents then Znth i contents = key else insertion_point (-i - 1) key contents)
         RETURN (Vint (Int.repr i))
         SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

Definition binary_search_while_spec a sh contents len key :=
EX low : Z, EX high : Z,
 PROP (0 <= low <= len;
  Int.min_signed <= high < len;
  In key contents -> In key (sublist low (high + 1) contents);
  ~ In key contents -> Forall (fun x => x < key) (sublist 0 low contents) /\ Forall (fun x => key < x) (sublist (high + 1) len contents))
 LOCAL (temp _a a; temp _low (Vint (Int.repr low)); temp _high (Vint (Int.repr high)); temp _key (Vint (Int.repr key)))
 SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).
           
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [binary_search_spec; main_spec]).

Lemma sublist_nil1 : forall A i j (l : list A), j <= i -> sublist i j l = [].
Proof.
  intros *.
  apply sublist_nil_gen.
Qed.

Lemma mean_le : forall i j : Z,
 i <= j ->
 i <= i + ((j - i) / 2) <= j.
Proof.
intros i j H_ij.
split.
- assert (Hle: 0 <= (j - i) / 2) by (apply Zdiv_le_lower_bound; lia).
  lia.
- assert (H_ji: 0 <= j - i) by auto with zarith.
  assert (Hle: (j - i) / 2 <= j - i) by (apply Zdiv_le_upper_bound; lia).
  lia.
Qed.

Lemma body_search: semax_body Vprog Gprog f_binary_search binary_search_spec.
Proof.
start_function.
forward.
forward.
forward_while (binary_search_while_spec a sh contents len key).
- entailer!.
  Exists 0; Exists (Zlength contents - 1).
  entailer!.
  split; intros; [|split].
  * autorewrite with sublist in *.
    assumption.
  * autorewrite with sublist in *.
    apply Forall_nil.
  * autorewrite with sublist in *.
    apply Forall_nil.
- entailer!.
- forward.
  * entailer!.
    split.
    + assert (Hle: low <= high) by lia.
      pose proof (mean_le _ _  Hle) as Hdle.
      assert (Heq: (high - low) / 2 = Int.signed (Int.divs (Int.repr (high - low)) (Int.repr 2))).
        unfold Int.divs.
        rewrite !Int.signed_repr.
        -- rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity.
        -- set (j := Int.min_signed) in *; compute in j; subst j.
           set (j := Int.max_signed) in *; compute in j; subst j.
           lia.
        -- set (j := Int.min_signed) in *; compute in j; subst j.
           set (j := Int.max_signed) in *; compute in j; subst j.
           lia.
        -- rewrite !Int.signed_repr;
             set (j := Int.min_signed) in *; compute in j; subst j;
             set (j := Int.max_signed) in *; compute in j; subst j; try lia.
           rewrite Zquot.Zquot_Zdiv_pos by lia.
           lia.
        -- rewrite <- Heq.
           set (j := Int.min_signed) in *; compute in j; subst j.
           set (j := Int.max_signed) in *; compute in j; subst j.
           lia.
    + intro.
      destruct H0.
      unfold Int.mone in H11.
      apply repr_inj_signed in H11; [congruence|idtac|idtac].
      -- unfold repable_signed.
         pose proof Int.min_signed_neg as Hneg.
         set (j := Int.max_signed) in *; compute in j; subst j.
         lia.
      -- unfold repable_signed.
         set (j := Int.min_signed) in *; compute in j; subst j.
         set (j := Int.max_signed) in *; compute in j; subst j.
         lia.
   * assert_PROP (0 <= Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2))) < Zlength (map Int.repr contents)).
       entailer!.
       autorewrite with sublist.
       admit.
     assert_PROP ((0 <= Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2))) < Zlength contents)).
       entailer!.
       autorewrite with sublist in *.
       apply H8.
     forward.
     forward_if.
     -- forward.
        ** entailer!.
           assert (Hle: low <= high) by lia.
           pose proof (mean_le _ _  Hle) as Hdle.
           assert (Heq: low + (high - low) / 2 = Int.signed (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
             unfold Int.divs.
             rewrite add_repr.
             rewrite !Int.signed_repr.
             ++ rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity.
             ++ set (j := Int.min_signed) in *; compute in j; subst j.
               set (j := Int.max_signed) in *; compute in j; subst j.
               lia.
             ++ set (j := Int.min_signed) in *; compute in j; subst j.
               set (j := Int.max_signed) in *; compute in j; subst j.
               lia.
             ++ rewrite !Int.signed_repr;
               set (j := Int.min_signed) in *; compute in j; subst j;
               set (j := Int.max_signed) in *; compute in j; subst j; try lia.
               rewrite Zquot.Zquot_Zdiv_pos by lia.
               lia.
             ++ rewrite <- Heq.
               set (j := Int.min_signed) in *; compute in j; subst j.
               set (j := Int.max_signed) in *; compute in j; subst j.
               lia.
        ** entailer!.
           Exists ((low + ((high - low)/2)) + 1,high).
           entailer!.
           assert (Hle: low <= high) by lia.
           pose proof (mean_le _ _  Hle) as Hdle.
           split; [lia|].           
           admit.
      -- forward_if.
         ** forward.
            ++ entailer!.
              assert (Hle: low <= high) by lia.
              pose proof (mean_le _ _  Hle) as Hdle.
              assert (Heq: low + (high - low) / 2 = Int.signed (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
                unfold Int.divs.
                rewrite add_repr.
                rewrite !Int.signed_repr.
                --- rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity.
                --- set (j := Int.min_signed) in *; compute in j; subst j.
                    set (j := Int.max_signed) in *; compute in j; subst j.
                    lia.
                --- set (j := Int.min_signed) in *; compute in j; subst j.
                    set (j := Int.max_signed) in *; compute in j; subst j.
                    lia.
                --- rewrite !Int.signed_repr;
                    set (j := Int.min_signed) in *; compute in j; subst j;
                    set (j := Int.max_signed) in *; compute in j; subst j; try lia.
                    rewrite Zquot.Zquot_Zdiv_pos by lia.
                    lia.
                --- rewrite <- Heq.
                    set (j := Int.min_signed) in *; compute in j; subst j.
                    set (j := Int.max_signed) in *; compute in j; subst j.
                    lia.
            ++ entailer!.
              Exists (low,(low + ((high - low)/2)) - 1).
              entailer!.
              autorewrite with sublist in *.
              assert (Hle: low <= high) by lia.
              pose proof (mean_le _ _  Hle) as Hdle.
              set (j := Int.min_signed) in *; compute in j; subst j.
              split; [lia|].              
              admit.
         ** forward.
            assert (H_key_eq:
             Int.signed (Int.repr (Znth (Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))) contents)) = key) by lia.
            Exists (low + ((high - low) / 2)).
            entailer!.
            case (in_dec _ _); intro.
            ++ autorewrite with sublist in *.
              admit.
            ++ contradict n.
              admit.
- forward.
  + entailer!.
    set (j := Int.min_signed) in *; compute in j; subst j.
    set (j := Int.max_signed) in *; compute in j; subst j.
    set (j := Int.signed Int.zero) in *; compute in j; subst j.
    lia.
  + Exists (-low - 1).
    entailer!.
    case (in_dec _ _); intro.
    * specialize (H6 i).
      contradict H6.
      assert (Hlow: high + 1 <= low) by lia.
      rewrite sublist_nil1; auto.
    * unfold insertion_point.
      assert (Hl: - (- low - 1) - 1 = low) by lia.
      rewrite Hl.
      specialize (H7 n).
      destruct H7.
      split; [lia|].
      split; auto.
      admit.      
Admitted.

(*
Lemma sorted_array_index_elt_le : 
  (forall (intP_a_1_4_alloc_table_at_L:(alloc_table intP)),
   (forall (intP_intM_a_1_4_at_L:(memory intP int32)),
    (forall (a_1_0:(pointer intP)),
     (forall (len_0_0:Z),
      ((offset_min intP_a_1_4_alloc_table_at_L a_1_0) <= 0 /\
       (offset_max intP_a_1_4_alloc_table_at_L a_1_0) >= (len_0_0 - 1) ->
       ((sorted a_1_0 0 (len_0_0 - 1) intP_intM_a_1_4_at_L) ->
        (forall (i_3:Z),
         (forall (j_0:Z),
          (0 <= i_3 /\ i_3 <= (len_0_0 - 1) ->
           (0 <= j_0 /\ j_0 <= (len_0_0 - 1) ->
            (i_3 <= j_0 ->
             (integer_of_int32
              (select intP_intM_a_1_4_at_L (shift a_1_0 i_3))) <=
             (integer_of_int32
              (select intP_intM_a_1_4_at_L (shift a_1_0 j_0)))))))))))))).
Proof.
move => alloc_table mem a len [H_min H_max] H_srt i j.
move: i.
elim/(well_founded_ind (Zwf_well_founded 0)): j.
move => x H_ind i H_x H_j H_ix.
have H_ltx: i = x \/ i < x by omega.
elim H_ltx => H_ltx'; first by rewrite H_ltx'; auto with zarith.  
suff H_lt: integer_of_int32 (select mem (shift a (x-1))) <= integer_of_int32 (select mem (shift a x)).
- suff H_ltm: integer_of_int32 (select mem (shift a i)) <= integer_of_int32 (select mem (shift a (x-1))) by auto with zarith.
  by apply H_ind; rewrite /Zwf; auto with zarith.
- pose proof (H_srt (x-1)) as H_ran.
  move: H_ran.
  have ->: x - 1 + 1 = x by auto with zarith.
  move => H_ran.
  by apply H_ran; auto with zarith.
Qed.

Lemma sorted_array_index_lt : 
  (forall (intP_a_2_5_alloc_table_at_L:(alloc_table intP)),
   (forall (intP_intM_a_2_5_at_L:(memory intP int32)),
    (forall (a_2:(pointer intP)),
     (forall (len_1:Z),
      ((offset_min intP_a_2_5_alloc_table_at_L a_2) <= 0 /\
       (offset_max intP_a_2_5_alloc_table_at_L a_2) >= (len_1 - 1) ->
       ((sorted a_2 0 (len_1 - 1) intP_intM_a_2_5_at_L) ->
        (forall (i_4:Z),
         (forall (j_1:Z),
          (0 <= i_4 /\ i_4 <= (len_1 - 1) ->
           (0 <= j_1 /\ j_1 <= (len_1 - 1) ->
            ((integer_of_int32 (select intP_intM_a_2_5_at_L (shift a_2 i_4))) <
             (integer_of_int32 (select intP_intM_a_2_5_at_L (shift a_2 j_1))) ->
             i_4 < j_1))))))))))).
Proof.
move => alloc_table mem a len H_ran H_srt i j H_lei H_lej.
elim (Z_lt_ge_dec i j) => H_dec; first by [].
have H_ji: j <= i by auto with zarith.
have H_le_le: integer_of_int32 (select mem (shift a j)) <= integer_of_int32 (select mem (shift a i)).
  by apply (sorted_array_index_elt_le _ _ _ _ H_ran H_srt _ _ H_lej H_lei).
by move => H_lt; auto with zarith.
Qed.
*)
