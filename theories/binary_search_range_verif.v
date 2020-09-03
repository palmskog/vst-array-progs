From VST Require Import floyd.proofauto floyd.sublist.
From VSTArrayProgs Require Import binary_search_theory binary_search_range.

Ltac do_compute_expr_warning::=idtac.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition binary_search_range_spec :=
 DECLARE _binary_search_range
  WITH a: val, sh : share, contents : list Z, from : Z, to : Z, key : Z
  PRE [ tptr tint, tint, tint, tint ]
          PROP (readable_share sh;
                0 <= from <= to;
                to <= Zlength contents <= Int.max_signed;
                Int.min_signed <= key <= Int.max_signed;
                Forall (fun x => Int.min_signed <= x <= Int.max_signed) (sublist from to contents);
                sorted (sublist from to contents))
          PARAMS (a; Vint (Int.repr from); Vint (Int.repr to); Vint (Int.repr key))
          SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a)
  POST [ tint ]
    EX i:Z,
         PROP (if in_dec Z.eq_dec key (sublist from to contents) then Znth i (sublist from to contents) = key
               else insertion_point (-i - 1) (sublist from to contents) key from to)
         RETURN (Vint (Int.repr i))
         SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

Definition binary_search_range_while_spec a sh contents from to key :=
EX low : Z, EX high : Z,
 PROP (from <= low <= to;
       Int.min_signed <= high < to;
       In key (sublist from to contents) -> In key (sublist low (high + 1) contents);
       ~ In key (sublist from to contents) ->
        Forall (fun x => x < key) (sublist from low contents) /\
        Forall (fun x => key < x) (sublist (high + 1) to contents))
 LOCAL (temp _a a; temp _key (Vint (Int.repr key)); temp _low (Vint (Int.repr low)); temp _high (Vint (Int.repr high)))
 SEP (data_at sh (tarray tint (Zlength contents)) (map Vint (map Int.repr contents)) a).

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

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [binary_search_range_spec; binary_search_spec; main_spec]).

Lemma In_sorted_gt_sublist : forall x i n l from to low high,
 0 <= from <= low ->
 high <= to <= Zlength l ->
 sorted (sublist from to l) ->
 In x (sublist low high l) ->
 low <= i < high ->
 Znth i l = n ->
 n < x ->
 In x (sublist (i + 1) high l).
Proof.
  intros.
  rewrite sublist_split with (mid := i + 1) in H2; try lia.
  rewrite in_app in H2; destruct H2; auto.
  generalize (In_sorted_range low (i + 1) x _ H1); intro X.
  repeat (lapply X; [clear X; intro X | lia]).
  replace (i + 1 - 1) with i in X by lia.
Admitted.

Lemma body_binary_search_range: semax_body Vprog Gprog f_binary_search_range binary_search_range_spec.
Proof.
start_function.
forward.
forward.
forward_while (binary_search_range_while_spec a sh contents from to key).
- unfold binary_search_range_while_spec.
  entailer!.
  Exists from; Exists (to - 1).
  entailer!.
  split; intros; [|split]; autorewrite with sublist in *.
  * assumption.
  * apply Forall_nil.
  * apply Forall_nil.
- entailer!.
- assert (Hle: low <= high) by lia.
  pose proof (mean_le _ _  Hle) as Hdle.
  assert (Heq: Int.signed (Int.divs (Int.repr (high - low)) (Int.repr 2)) = (high - low) / 2).
    unfold Int.divs; rewrite !Int.signed_repr; try rep_lia; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
    rewrite !Int.signed_repr; try rep_lia.
    rewrite Zquot.Zquot_Zdiv_pos by lia.
    rep_lia.
  assert (Heq': Int.unsigned (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2))) = low + (high - low) / 2).
    unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
    rewrite Zquot.Zquot_Zdiv_pos by lia.
    rewrite add_repr.
    rewrite !Int.unsigned_repr; auto.
    rep_lia.
  assert (Heq'': Int.signed (Int.add (Int.repr low) (Int.divs (Int.repr (high - low)) (Int.repr 2))) = low + (high - low) / 2).
    unfold Int.divs; rewrite !Int.signed_repr; try rep_lia.
    rewrite add_repr.
    rewrite !Int.signed_repr; [rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity|].
    rewrite Zquot.Zquot_Zdiv_pos by lia.
    rep_lia.
  forward.
  * entailer!.
    destruct H11.
    unfold Int.mone in H12.
    apply repr_inj_signed in H12; [congruence|unfold repable_signed|unfold repable_signed]; rep_lia.
  * forward.
    forward_if.
    + forward.
      entailer!.
      Exists ((low + ((high - low)/2)) + 1,high).
      entailer!.
      split; [lia|]; split; [|split]; intros.
      -- specialize (H6 H12).
Admitted.

Lemma body_binary_search: semax_body Vprog Gprog f_binary_search binary_search_spec.
Proof.
start_function.
forward_call (a, sh, contents, 0, len, key).
- pose proof (Zlength_nonneg contents) as Hlen.
  rewrite H0.
  split; auto; split; [lia|]; split; [lia|]; split; auto; split.
  * autorewrite with sublist; assumption.
  * autorewrite with sublist; assumption.
- Intro res.
  forward.
  revert H4.
  autorewrite with sublist.
  case (in_dec _ _ _); intros; Exists res; entailer!.
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
semax_func_cons body_binary_search_range.
semax_func_cons body_binary_search.
semax_func_cons body_main.
Qed.
