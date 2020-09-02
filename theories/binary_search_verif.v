From VST Require Import floyd.proofauto floyd.sublist.
From VSTArrayProgs Require Import binary_search_theory binary_search.

Ltac do_compute_expr_warning::=idtac.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

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
         PROP (if in_dec Z.eq_dec key contents then Znth i contents = key
               else insertion_point (-i - 1) contents key 0 (Zlength contents))
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
  
Lemma body_binary_search: semax_body Vprog Gprog f_binary_search binary_search_spec.
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
        unfold Int.divs; rewrite !Int.signed_repr; try rep_lia; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
        rewrite !Int.signed_repr; try rep_lia.
        rewrite Zquot.Zquot_Zdiv_pos by lia.
        rep_lia.
      rewrite <- Heq.
      rep_lia.
    + intro.
      destruct H0.
      unfold Int.mone in H11.
      apply repr_inj_signed in H11; [congruence|unfold repable_signed|unfold repable_signed]; rep_lia.
   * assert_PROP (0 <= Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2))) < Zlength (map Int.repr contents)).
       entailer!.
       autorewrite with sublist.       
       assert (Hle: low <= high) by lia.
       pose proof (mean_le _ _  Hle) as Hdle.
       assert (Heq: low + (high - low) / 2 = Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
         unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
         rewrite Zquot.Zquot_Zdiv_pos by lia.
         rewrite add_repr.
         rewrite !Int.unsigned_repr; auto.
         rep_lia.
       rewrite <- Heq; lia.
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
             unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
             rewrite add_repr.
             rewrite !Int.signed_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
             rewrite Zquot.Zquot_Zdiv_pos by lia.
             rep_lia.
           rewrite <- Heq; rep_lia.
        ** entailer!.
           Exists ((low + ((high - low)/2)) + 1,high).
           entailer!.
           assert (Hle: low <= high) by lia.
           pose proof (mean_le _ _  Hle) as Hdle.
           split; [lia|].
           assert (Heq: low + (high - low)/2 = Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
             unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
             rewrite add_repr.
             rewrite !Int.unsigned_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
             rewrite Zquot.Zquot_Zdiv_pos by lia.
             rep_lia.
           rewrite <- Heq in H9,H10.
           rewrite !Int.signed_repr in H10; [split; [|split]; intros|].
           --- specialize (H6 H0).
               eapply In_sorted_gt; eauto; lia.
           --- specialize (H7 H0).
               destruct H7 as [Hlow Hhigh].
               split; [|assumption].
               apply Forall_forall; intros.
               eapply Znth_lt_sublist_lt; eauto.
           --- f_equal.
               unfold Int.add at 1.
               f_equal.
               rewrite <- Heq.
               rewrite !Int.unsigned_repr; rep_lia.
           --- assert (Hin: In (Znth (low + (high - low) / 2) contents) contents) by (eapply Znth_In; eauto).
               pose proof (Forall_forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) contents) as HFA.
               simpl in HFA.
               destruct HFA as [HFA1 HFA2].
               apply (HFA1 H2 _ Hin).
      -- forward_if.
         ** forward.
            ++ entailer!.
              assert (Hle: low <= high) by lia.
              pose proof (mean_le _ _  Hle) as Hdle.
              assert (Heq: low + (high - low) / 2 = Int.signed (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
                unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
                rewrite add_repr.
                rewrite !Int.signed_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
                rewrite Zquot.Zquot_Zdiv_pos by lia.
                rep_lia.
              rewrite <- Heq; rep_lia.
            ++ entailer!.
              Exists (low,(low + ((high - low)/2)) - 1).
              entailer!.
              autorewrite with sublist in *.
              assert (Hle: low <= high) by lia.
              pose proof (mean_le _ _  Hle) as Hdle.
              assert (Heq: low + (high - low)/2 = Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
                unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
                rewrite add_repr.
                rewrite !Int.unsigned_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
                rewrite Zquot.Zquot_Zdiv_pos by lia.
                rep_lia.
              assert (Hle': Int.min_signed <= Znth (Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))) contents <= Int.max_signed).
                rewrite <- Heq.
                assert (Hin: In (Znth (low + (high - low) / 2) contents) contents) by (eapply Znth_In; eauto; rewrite Heq; reflexivity).
                pose proof (Forall_forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) contents) as HFA.
                simpl in HFA.
                destruct HFA as [HFA1 HFA2].
                apply (HFA1 H2 _ Hin).
              rewrite !Int.signed_repr in H11; auto.
              rewrite <- Heq in H11.
              split; [rep_lia|]; split; [|split]; intros.
              --- specialize (H6 H0).
                  eapply (In_sorted_lt _ _ _ _ _ (high + 1)); eauto; lia.
              --- specialize (H7 H0).
                  destruct H7 as [Hl Hh].
                  split; [assumption|].
                  apply Forall_forall; intros.
                  revert H7.
                  apply Znth_gt_sublist_gt; auto.
                  lia.
              --- f_equal.
                  unfold Int.sub.
                  f_equal.
                  rewrite !Int.unsigned_repr; [|rep_lia].
                  rewrite <- Heq; reflexivity.
         ** forward.
            assert (H_key_eq:
             Int.signed (Int.repr (Znth (Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))) contents)) = key) by lia.
            Exists (low + ((high - low) / 2)).
            entailer!.
            assert (Hle: low <= high) by lia.
            pose proof (mean_le _ _  Hle) as Hdle.
            assert (Heq: low + (high - low) / 2 = Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))).
              unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
              rewrite add_repr.
              rewrite !Int.unsigned_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
              rewrite Zquot.Zquot_Zdiv_pos by lia.
              rep_lia.
            assert (Hrange: Int.min_signed <= Znth (Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2)))) contents <= Int.max_signed).
              rewrite <- Heq.
              assert (Hin: In (Znth (low + (high - low) / 2) contents) contents) by (eapply Znth_In; eauto; rewrite Heq; reflexivity).
              pose proof (Forall_forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) contents) as HFA.
              simpl in HFA.
              destruct HFA as [HFA1 HFA2].
              apply (HFA1 H2 _ Hin).
            case (in_dec _ _); intro.
            ++ split.
              --- rewrite !Int.signed_repr; auto.
                  rewrite <- Heq.
                  reflexivity.
              --- f_equal.                  
                  rewrite Heq.
                  unfold Int.add.
                  f_equal.
                  rewrite !Int.unsigned_repr; [reflexivity|idtac|rep_lia].
                  unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
                  rewrite !Int.unsigned_repr; rewrite Zquot.Zquot_Zdiv_pos; rep_lia.              
            ++ contradict n.
              assert (Hin: In (Znth (low + (high - low) / 2) contents) contents) by (eapply Znth_In; eauto; rewrite Heq; reflexivity).
              rewrite <- Heq.
              rewrite !Int.signed_repr; auto.
              rewrite Heq; auto.
- forward.
  + entailer!.
    set (j := Int.signed Int.zero) in *; compute in j; subst j.
    rep_lia.
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
      assert (Hle: high + 1 <= low) by lia.
      eapply Forall_sublist_overlap; eauto.
Qed.

Definition four_contents := [1; 2; 3; 4].

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward_call (gv _four,Ews,four_contents,4,3).
  { split. auto.
    change (Zlength four_contents) with 4.
    repeat constructor; computable.
  }
  Intro r; forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_binary_search.
semax_func_cons body_main.
Qed.
