From VST Require Import floyd.proofauto floyd.sublist.
From VSTArrayProgs Require Import binary_search_theory binary_search_range.

Ltac do_compute_expr_warning::=idtac.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition binary_search_range_spec :=
 DECLARE _binary_search_range
  WITH a: val, sh : share, contents : list Z, from : Z, to : Z, key : Z
  PRE [ tptr tint, tint, tint ]
          PROP (readable_share sh;
                0 <= from;
                from <= to;
                to <= Zlength contents;
                Zlength contents <= Int.max_signed;
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
