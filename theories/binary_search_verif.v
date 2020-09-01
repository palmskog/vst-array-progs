From VST Require Import floyd.proofauto floyd.sublist.
From VSTArrayProgs Require Import binary_search.

Ltac do_compute_expr_warning::=idtac.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Fixpoint sorted (l : list Z) : Prop :=
  match l with
  | [] => True
  | x::rest =>
    match rest with [] => True | y::_ =>  x <= y /\ sorted rest end
  end.

Fixpoint sorted' (l : list Z) : Prop :=
match l with
| [] => True
| _ :: [] => True
| x :: y :: l' => x <= y /\ sorted' l'
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

Lemma Znth_In : forall A (d: Inhabitant A) i (l : list A) x (Hrange : 0 <= i < Zlength l)
 (Hnth : Znth i l = x), In x l.
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); [lia|].
  subst; apply nth_In.
  rewrite Zlength_correct in Hrange; auto.
  rep_lia.
Qed.

Lemma In_Znth : forall A (d: Inhabitant A) (l : list A) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; lia.
  - destruct (zlt (Z.of_nat n) 0); [lia|].
    rewrite Nat2Z.id; auto.
Qed.

Lemma sublist_of_nil : forall A i j, sublist i j (nil : list A) = [].
Proof.
  intros; unfold sublist.
  rewrite firstn_nil, skipn_nil; auto.
Qed.

Fixpoint sorted2 l :=
  match l with
  | [] => True
  | x :: rest => Forall (fun y => x <= y) rest /\ sorted2 rest
  end.

Lemma sorted_equiv : forall l, sorted l <-> sorted2 l.
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct l.
    + simpl; split; auto.
    + rewrite IHl; simpl; split; intros (? & Hall & ?); split3; auto.
       * constructor; auto.
          rewrite Forall_forall in *; intros ? Hin.
          specialize (Hall _ Hin); lia.
       * inversion H. auto.
Qed.

Lemma sorted_mono : forall l i j (Hsort : sorted l) (Hi : 0 <= i <= j)
                           (Hj : j < Zlength l),
    Znth i l <= Znth j l.
Proof.
induction l; intros.
* rewrite !Znth_nil. lia.
* 
 rewrite sorted_equiv in Hsort. destruct Hsort as [H9 Hsort].
 rewrite <- sorted_equiv in Hsort. rewrite Forall_forall in H9.
 rewrite Zlength_cons in Hj.
 destruct (zeq i 0).
 +
   subst i; rewrite Znth_0_cons. 
   destruct (zeq j 0).
   - subst j. rewrite Znth_0_cons. lia.
   - rewrite Znth_pos_cons by lia.
      apply H9.
      eapply Znth_In; [ | reflexivity]; lia.
 +
    rewrite !Znth_pos_cons by lia.
    apply IHl; auto; lia.
Qed.

Lemma In_sorted_range : forall lo hi x l (Hsort : sorted l) (Hlo : 0 <= lo <= hi)
                              (Hhi : hi <= Zlength l)
                              (Hin : In x (sublist lo hi l)),
    Znth lo l <= x <= Znth (hi - 1) l.
Proof.
  intros.
  generalize (In_Znth _ _ _ _ Hin); intros (i & Hrange & Hi).
  rewrite Zlength_sublist in Hrange by auto.
  rewrite Znth_sublist in Hi by lia.
  subst; split; apply sorted_mono; auto; lia.
Qed.

Lemma In_sorted_gt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : n < x),
    In x (sublist (i + 1) hi l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in Hin; try lia.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range lo (i + 1) x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | lia]).
  replace (i + 1 - 1) with i in X by lia.
  specialize (X H); subst; lia.
Qed.

Lemma In_sorted_lt : forall x i n l lo hi (Hsort : sorted l) (Hlo : lo >= 0)
                            (Hhi : hi <= Zlength l)
                            (Hin : In x (sublist lo hi l))
                            (Hi : lo <= i < hi) (Hn : Znth i l = n)
                            (Hgt : x < n),
    In x (sublist lo i l).
Proof.
  intros.
  rewrite sublist_split with (mid := i) in Hin; try lia.
  rewrite in_app in Hin; destruct Hin; auto.
  generalize (In_sorted_range i hi x _ Hsort); intro X.
  repeat (lapply X; [clear X; intro X | lia]).
  specialize (X H); subst; lia.
Qed.

Lemma Znth_In_sublist : forall A (d: Inhabitant A) i (l : list A) lo hi
  (Hlo : 0 <= lo <= i) (Hhi : i < hi <= Zlength l),
  In (Znth i l) (sublist lo hi l).
Proof.
  intros.
  apply Znth_In with (i := i - lo)(d := d).
  - rewrite Zlength_sublist; lia.
  - rewrite <- (Z.sub_simpl_r i lo) at 2.
    apply Znth_sublist; lia.
Qed.

Lemma sublist_In_sublist : forall A (l : list A) x lo hi lo' hi' (Hlo : 0 <= lo <= lo')
  (Hhi : hi' <= hi), In x (sublist lo' hi' l) -> In x (sublist lo hi l).
Proof.
  intros.
  apply sublist_In with (lo0 := lo' - lo)(hi0 := hi' - lo); rewrite sublist_sublist;
    try split; try lia.
  - repeat rewrite Z.sub_simpl_r; auto.
  - destruct (Z_le_dec hi' lo'); try lia.
    rewrite sublist_nil1 in *; auto; simpl in *; contradiction.
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

Lemma Znth_lt_sublist_lt :
  forall l i x key,
    0 <= i < Zlength l ->
    sorted l ->
    Znth i l < key ->
    In x (sublist 0 (i + 1) l) ->
    x < key.
Proof.
intros.
apply (In_sorted_range _ _ _ _ H0) in H2; try lia.
assert (Hi: i + 1 - 1 = i) by lia.
rewrite Hi in H2; clear Hi.
lia.
Qed.

Lemma Znth_gt_sublist_gt :
  forall l i x key,
  0 <= i < Zlength l ->
  sorted l ->
  key < Znth i l ->
  In x (sublist i (Zlength l) l) ->
  key < x.
Proof.
intros.
apply (In_sorted_range _ _ _ _ H0) in H2; try lia.
Qed.

Lemma sublist_lt_0 : forall low high (l : list Z),
  low < 0 ->
  sublist low high l = sublist 0 high l.
Proof.
intros.
unfold sublist.
rewrite Z2Nat_neg; auto.
Qed.

Lemma Forall_sublist_overlap : forall (l : list Z) P low high,  
  high <= low ->
  Forall P (sublist high (Zlength l) l) ->
  Forall P (sublist low (Zlength l) l).
Proof.
intros l P low high Hle Hhigh.
case (Z_lt_dec high 0); intros.
  rewrite sublist_lt_0 in Hhigh; auto.
  case (Z_lt_dec low 0); intros; [rewrite sublist_lt_0; auto|].  
  apply Forall_forall.
  intros.
  assert (0 <= low) by lia.
  pose proof (Forall_forall P (sublist 0 (Zlength l) l)) as [Hp1 Hp2].
  specialize (Hp1 Hhigh).
  apply Hp1.
  revert H.
  apply sublist_In_sublist; auto with zarith.
assert (0 <= high) by lia.
apply Forall_forall; intros.
pose proof (Forall_forall P (sublist high (Zlength l) l)) as [Hp1 Hp2].
specialize (Hp1 Hhigh).
apply Hp1.
revert H0.
apply sublist_In_sublist; auto with zarith.
Qed.
  
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
