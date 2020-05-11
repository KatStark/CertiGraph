From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "kruskal_edgelist.c"%string.
  Definition normalized := true.
End Info.

Definition _E : ident := 9%positive.
Definition _Union : ident := 68%positive.
Definition _V : ident := 8%positive.
Definition ___builtin_ais_annot : ident := 12%positive.
Definition ___builtin_annot : ident := 21%positive.
Definition ___builtin_annot_intval : ident := 22%positive.
Definition ___builtin_bswap : ident := 14%positive.
Definition ___builtin_bswap16 : ident := 16%positive.
Definition ___builtin_bswap32 : ident := 15%positive.
Definition ___builtin_bswap64 : ident := 13%positive.
Definition ___builtin_clz : ident := 47%positive.
Definition ___builtin_clzl : ident := 48%positive.
Definition ___builtin_clzll : ident := 49%positive.
Definition ___builtin_ctz : ident := 50%positive.
Definition ___builtin_ctzl : ident := 51%positive.
Definition ___builtin_ctzll : ident := 52%positive.
Definition ___builtin_debug : ident := 63%positive.
Definition ___builtin_fabs : ident := 17%positive.
Definition ___builtin_fmadd : ident := 55%positive.
Definition ___builtin_fmax : ident := 53%positive.
Definition ___builtin_fmin : ident := 54%positive.
Definition ___builtin_fmsub : ident := 56%positive.
Definition ___builtin_fnmadd : ident := 57%positive.
Definition ___builtin_fnmsub : ident := 58%positive.
Definition ___builtin_fsqrt : ident := 18%positive.
Definition ___builtin_membar : ident := 23%positive.
Definition ___builtin_memcpy_aligned : ident := 19%positive.
Definition ___builtin_read16_reversed : ident := 59%positive.
Definition ___builtin_read32_reversed : ident := 60%positive.
Definition ___builtin_sel : ident := 20%positive.
Definition ___builtin_va_arg : ident := 25%positive.
Definition ___builtin_va_copy : ident := 26%positive.
Definition ___builtin_va_end : ident := 27%positive.
Definition ___builtin_va_start : ident := 24%positive.
Definition ___builtin_write16_reversed : ident := 61%positive.
Definition ___builtin_write32_reversed : ident := 62%positive.
Definition ___compcert_i64_dtos : ident := 32%positive.
Definition ___compcert_i64_dtou : ident := 33%positive.
Definition ___compcert_i64_sar : ident := 44%positive.
Definition ___compcert_i64_sdiv : ident := 38%positive.
Definition ___compcert_i64_shl : ident := 42%positive.
Definition ___compcert_i64_shr : ident := 43%positive.
Definition ___compcert_i64_smod : ident := 40%positive.
Definition ___compcert_i64_smulh : ident := 45%positive.
Definition ___compcert_i64_stod : ident := 34%positive.
Definition ___compcert_i64_stof : ident := 36%positive.
Definition ___compcert_i64_udiv : ident := 39%positive.
Definition ___compcert_i64_umod : ident := 41%positive.
Definition ___compcert_i64_umulh : ident := 46%positive.
Definition ___compcert_i64_utod : ident := 35%positive.
Definition ___compcert_i64_utof : ident := 37%positive.
Definition ___compcert_va_composite : ident := 31%positive.
Definition ___compcert_va_float64 : ident := 30%positive.
Definition ___compcert_va_int32 : ident := 28%positive.
Definition ___compcert_va_int64 : ident := 29%positive.
Definition _a : ident := 72%positive.
Definition _edge : ident := 7%positive.
Definition _edge_list : ident := 10%positive.
Definition _find : ident := 67%positive.
Definition _free : ident := 71%positive.
Definition _free_graph : ident := 81%positive.
Definition _graph : ident := 11%positive.
Definition _graph__1 : ident := 80%positive.
Definition _i : ident := 75%positive.
Definition _i__1 : ident := 85%positive.
Definition _init_graph_sample : ident := 91%positive.
Definition _init_mst : ident := 92%positive.
Definition _j : ident := 76%positive.
Definition _kruskal : ident := 89%positive.
Definition _kruskal_sort : ident := 90%positive.
Definition _m : ident := 73%positive.
Definition _main : ident := 93%positive.
Definition _makeSet : ident := 69%positive.
Definition _mallocN : ident := 70%positive.
Definition _mst : ident := 82%positive.
Definition _n : ident := 74%positive.
Definition _next_edge : ident := 86%positive.
Definition _parent : ident := 1%positive.
Definition _pivot : ident := 77%positive.
Definition _popMin : ident := 65%positive.
Definition _pq : ident := 84%positive.
Definition _pq_emp : ident := 66%positive.
Definition _push : ident := 64%positive.
Definition _rank : ident := 2%positive.
Definition _sort_edges : ident := 79%positive.
Definition _subset : ident := 3%positive.
Definition _subsets : ident := 83%positive.
Definition _tmp : ident := 78%positive.
Definition _u : ident := 4%positive.
Definition _ufind : ident := 87%positive.
Definition _v : ident := 5%positive.
Definition _vfind : ident := 88%positive.
Definition _weight : ident := 6%positive.
Definition _t'1 : ident := 94%positive.
Definition _t'10 : ident := 103%positive.
Definition _t'11 : ident := 104%positive.
Definition _t'12 : ident := 105%positive.
Definition _t'13 : ident := 106%positive.
Definition _t'14 : ident := 107%positive.
Definition _t'15 : ident := 108%positive.
Definition _t'16 : ident := 109%positive.
Definition _t'17 : ident := 110%positive.
Definition _t'18 : ident := 111%positive.
Definition _t'19 : ident := 112%positive.
Definition _t'2 : ident := 95%positive.
Definition _t'20 : ident := 113%positive.
Definition _t'21 : ident := 114%positive.
Definition _t'22 : ident := 115%positive.
Definition _t'3 : ident := 96%positive.
Definition _t'4 : ident := 97%positive.
Definition _t'5 : ident := 98%positive.
Definition _t'6 : ident := 99%positive.
Definition _t'7 : ident := 100%positive.
Definition _t'8 : ident := 101%positive.
Definition _t'9 : ident := 102%positive.

Definition f_sort_edges := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct _edge noattr))) :: (_m, tint) ::
                (_n, tint) :: nil);
  fn_vars := ((_tmp, (Tstruct _edge noattr)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_pivot, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Olt (Etempvar _m tint) (Etempvar _n tint) tint)
  (Ssequence
    (Sset _pivot
      (Efield
        (Ederef
          (Ebinop Oadd (Etempvar _a (tptr (Tstruct _edge noattr)))
            (Etempvar _n tint) (tptr (Tstruct _edge noattr)))
          (Tstruct _edge noattr)) _weight tint))
    (Ssequence
      (Sset _i (Etempvar _m tint))
      (Ssequence
        (Sset _j (Etempvar _n tint))
        (Ssequence
          (Swhile
            (Ebinop Ole (Etempvar _i tint) (Etempvar _j tint) tint)
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _a (tptr (Tstruct _edge noattr)))
                            (Etempvar _i tint) (tptr (Tstruct _edge noattr)))
                          (Tstruct _edge noattr)) _weight tint))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'11 tint)
                                   (Etempvar _pivot tint) tint)
                      Sskip
                      Sbreak))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint)))
                Sskip)
              (Ssequence
                (Sloop
                  (Ssequence
                    (Ssequence
                      (Sset _t'10
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _a (tptr (Tstruct _edge noattr)))
                              (Etempvar _j tint)
                              (tptr (Tstruct _edge noattr)))
                            (Tstruct _edge noattr)) _weight tint))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'10 tint)
                                     (Etempvar _pivot tint) tint)
                        Sskip
                        Sbreak))
                    (Sset _j
                      (Ebinop Osub (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint)))
                  Sskip)
                (Sifthenelse (Ebinop Ole (Etempvar _i tint)
                               (Etempvar _j tint) tint)
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _a (tptr (Tstruct _edge noattr)))
                              (Etempvar _i tint)
                              (tptr (Tstruct _edge noattr)))
                            (Tstruct _edge noattr)) _u tint))
                      (Sassign
                        (Efield (Evar _tmp (Tstruct _edge noattr)) _u tint)
                        (Etempvar _t'9 tint)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _a (tptr (Tstruct _edge noattr)))
                                (Etempvar _i tint)
                                (tptr (Tstruct _edge noattr)))
                              (Tstruct _edge noattr)) _v tint))
                        (Sassign
                          (Efield (Evar _tmp (Tstruct _edge noattr)) _v tint)
                          (Etempvar _t'8 tint)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Etempvar _a (tptr (Tstruct _edge noattr)))
                                  (Etempvar _i tint)
                                  (tptr (Tstruct _edge noattr)))
                                (Tstruct _edge noattr)) _weight tint))
                          (Sassign
                            (Efield (Evar _tmp (Tstruct _edge noattr))
                              _weight tint) (Etempvar _t'7 tint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'6
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _a (tptr (Tstruct _edge noattr)))
                                    (Etempvar _j tint)
                                    (tptr (Tstruct _edge noattr)))
                                  (Tstruct _edge noattr)) _u tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _a (tptr (Tstruct _edge noattr)))
                                    (Etempvar _i tint)
                                    (tptr (Tstruct _edge noattr)))
                                  (Tstruct _edge noattr)) _u tint)
                              (Etempvar _t'6 tint)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _a (tptr (Tstruct _edge noattr)))
                                      (Etempvar _j tint)
                                      (tptr (Tstruct _edge noattr)))
                                    (Tstruct _edge noattr)) _v tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _a (tptr (Tstruct _edge noattr)))
                                      (Etempvar _i tint)
                                      (tptr (Tstruct _edge noattr)))
                                    (Tstruct _edge noattr)) _v tint)
                                (Etempvar _t'5 tint)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'4
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _a (tptr (Tstruct _edge noattr)))
                                        (Etempvar _j tint)
                                        (tptr (Tstruct _edge noattr)))
                                      (Tstruct _edge noattr)) _weight tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _a (tptr (Tstruct _edge noattr)))
                                        (Etempvar _i tint)
                                        (tptr (Tstruct _edge noattr)))
                                      (Tstruct _edge noattr)) _weight tint)
                                  (Etempvar _t'4 tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'3
                                    (Efield
                                      (Evar _tmp (Tstruct _edge noattr)) _u
                                      tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _a (tptr (Tstruct _edge noattr)))
                                          (Etempvar _j tint)
                                          (tptr (Tstruct _edge noattr)))
                                        (Tstruct _edge noattr)) _u tint)
                                    (Etempvar _t'3 tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'2
                                      (Efield
                                        (Evar _tmp (Tstruct _edge noattr)) _v
                                        tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _a (tptr (Tstruct _edge noattr)))
                                            (Etempvar _j tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _v tint)
                                      (Etempvar _t'2 tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'1
                                        (Efield
                                          (Evar _tmp (Tstruct _edge noattr))
                                          _weight tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _a (tptr (Tstruct _edge noattr)))
                                              (Etempvar _j tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _weight
                                          tint) (Etempvar _t'1 tint)))
                                    (Ssequence
                                      (Sset _i
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))
                                      (Sset _j
                                        (Ebinop Osub (Etempvar _j tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))))))))))))
                  Sskip))))
          (Ssequence
            (Scall None
              (Evar _sort_edges (Tfunction
                                  (Tcons (tptr (Tstruct _edge noattr))
                                    (Tcons tint (Tcons tint Tnil))) tvoid
                                  cc_default))
              ((Etempvar _a (tptr (Tstruct _edge noattr))) ::
               (Etempvar _m tint) :: (Etempvar _j tint) :: nil))
            (Scall None
              (Evar _sort_edges (Tfunction
                                  (Tcons (tptr (Tstruct _edge noattr))
                                    (Tcons tint (Tcons tint Tnil))) tvoid
                                  cc_default))
              ((Etempvar _a (tptr (Tstruct _edge noattr))) ::
               (Etempvar _i tint) :: (Etempvar _n tint) :: nil)))))))
  Sskip)
|}.

Definition f_free_graph := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph__1, (tptr (Tstruct _graph noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _edge noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
          (Tstruct _graph noattr)) _edge_list (tptr (Tstruct _edge noattr))))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _edge noattr))) :: nil)))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _graph__1 (tptr (Tstruct _graph noattr))) :: nil)))
|}.

Definition f_kruskal := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph__1, (tptr (Tstruct _graph noattr))) ::
                (_mst, (tptr (Tstruct _graph noattr))) :: nil);
  fn_vars := ((_pq, (tarray tint 8)) :: nil);
  fn_temps := ((_V, tint) :: (_subsets, (tptr (Tstruct _subset noattr))) ::
               (_i, tint) :: (_i__1, tint) :: (_weight, tint) ::
               (_next_edge, tint) :: (_u, tint) :: (_v, tint) ::
               (_ufind, tint) :: (_vfind, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _subset noattr))) :: (_t'22, tint) ::
               (_t'21, (tptr (Tstruct _edge noattr))) ::
               (_t'20, (tptr (Tstruct _edge noattr))) ::
               (_t'19, (tptr (Tstruct _edge noattr))) :: (_t'18, tint) ::
               (_t'17, (tptr (Tstruct _edge noattr))) :: (_t'16, tint) ::
               (_t'15, (tptr (Tstruct _edge noattr))) :: (_t'14, tint) ::
               (_t'13, (tptr (Tstruct _edge noattr))) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct _edge noattr))) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _edge noattr))) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _edge noattr))) :: (_t'6, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _V
    (Efield
      (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
        (Tstruct _graph noattr)) _V tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _makeSet (Tfunction (Tcons tint Tnil)
                         (tptr (Tstruct _subset noattr)) cc_default))
        ((Etempvar _V tint) :: nil))
      (Sset _subsets (Etempvar _t'1 (tptr (Tstruct _subset noattr)))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 8) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _pq (tarray tint 8)) (Etempvar _i tint)
                  (tptr tint)) tint)
              (Ebinop Osub (Econst_int (Int.repr 2147483647) tint)
                (Ebinop Odiv (Econst_int (Int.repr 2147483647) tint)
                  (Econst_int (Int.repr 8) tint) tint) tint)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Ssequence
          (Sset _i__1 (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'22
                  (Efield
                    (Ederef
                      (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                      (Tstruct _graph noattr)) _E tint))
                (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                               (Etempvar _t'22 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef
                        (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                        (Tstruct _graph noattr)) _edge_list
                      (tptr (Tstruct _edge noattr))))
                  (Sset _weight
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'21 (tptr (Tstruct _edge noattr)))
                          (Etempvar _i__1 tint)
                          (tptr (Tstruct _edge noattr)))
                        (Tstruct _edge noattr)) _weight tint)))
                (Scall None
                  (Evar _push (Tfunction
                                (Tcons tint
                                  (Tcons tint (Tcons (tptr tint) Tnil)))
                                tvoid cc_default))
                  ((Etempvar _i__1 tint) :: (Etempvar _weight tint) ::
                   (Evar _pq (tarray tint 8)) :: nil))))
            (Sset _i__1
              (Ebinop Oadd (Etempvar _i__1 tint)
                (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _pq_emp (Tfunction (Tcons (tptr tint) Tnil) tint
                                  cc_default))
                  ((Evar _pq (tarray tint 8)) :: nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _popMin (Tfunction (Tcons (tptr tint) Tnil) tint
                                    cc_default))
                    ((Evar _pq (tarray tint 8)) :: nil))
                  (Sset _next_edge (Etempvar _t'3 tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'20
                      (Efield
                        (Ederef
                          (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                          (Tstruct _graph noattr)) _edge_list
                        (tptr (Tstruct _edge noattr))))
                    (Sset _u
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _t'20 (tptr (Tstruct _edge noattr)))
                            (Etempvar _next_edge tint)
                            (tptr (Tstruct _edge noattr)))
                          (Tstruct _edge noattr)) _u tint)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'19
                        (Efield
                          (Ederef
                            (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                            (Tstruct _graph noattr)) _edge_list
                          (tptr (Tstruct _edge noattr))))
                      (Sset _v
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _t'19 (tptr (Tstruct _edge noattr)))
                              (Etempvar _next_edge tint)
                              (tptr (Tstruct _edge noattr)))
                            (Tstruct _edge noattr)) _v tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _find (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _subset noattr))
                                          (Tcons tint Tnil)) tint cc_default))
                          ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                           (Etempvar _u tint) :: nil))
                        (Sset _ufind (Etempvar _t'4 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _find (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _subset noattr))
                                            (Tcons tint Tnil)) tint
                                          cc_default))
                            ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                             (Etempvar _v tint) :: nil))
                          (Sset _vfind (Etempvar _t'5 tint)))
                        (Sifthenelse (Ebinop One (Etempvar _ufind tint)
                                       (Etempvar _vfind tint) tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'15
                                (Efield
                                  (Ederef
                                    (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                    (Tstruct _graph noattr)) _edge_list
                                  (tptr (Tstruct _edge noattr))))
                              (Ssequence
                                (Sset _t'16
                                  (Efield
                                    (Ederef
                                      (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                      (Tstruct _graph noattr)) _E tint))
                                (Ssequence
                                  (Sset _t'17
                                    (Efield
                                      (Ederef
                                        (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _edge_list
                                      (tptr (Tstruct _edge noattr))))
                                  (Ssequence
                                    (Sset _t'18
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'17 (tptr (Tstruct _edge noattr)))
                                            (Etempvar _next_edge tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _u tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'15 (tptr (Tstruct _edge noattr)))
                                            (Etempvar _t'16 tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _u tint)
                                      (Etempvar _t'18 tint))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'11
                                  (Efield
                                    (Ederef
                                      (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                      (Tstruct _graph noattr)) _edge_list
                                    (tptr (Tstruct _edge noattr))))
                                (Ssequence
                                  (Sset _t'12
                                    (Efield
                                      (Ederef
                                        (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _E tint))
                                  (Ssequence
                                    (Sset _t'13
                                      (Efield
                                        (Ederef
                                          (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                          (Tstruct _graph noattr)) _edge_list
                                        (tptr (Tstruct _edge noattr))))
                                    (Ssequence
                                      (Sset _t'14
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'13 (tptr (Tstruct _edge noattr)))
                                              (Etempvar _next_edge tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _v tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'11 (tptr (Tstruct _edge noattr)))
                                              (Etempvar _t'12 tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _v tint)
                                        (Etempvar _t'14 tint))))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _edge_list
                                      (tptr (Tstruct _edge noattr))))
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                          (Tstruct _graph noattr)) _E tint))
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                            (Tstruct _graph noattr))
                                          _edge_list
                                          (tptr (Tstruct _edge noattr))))
                                      (Ssequence
                                        (Sset _t'10
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'9 (tptr (Tstruct _edge noattr)))
                                                (Etempvar _next_edge tint)
                                                (tptr (Tstruct _edge noattr)))
                                              (Tstruct _edge noattr)) _weight
                                            tint))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'7 (tptr (Tstruct _edge noattr)))
                                                (Etempvar _t'8 tint)
                                                (tptr (Tstruct _edge noattr)))
                                              (Tstruct _edge noattr)) _weight
                                            tint) (Etempvar _t'10 tint))))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'6
                                      (Efield
                                        (Ederef
                                          (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                          (Tstruct _graph noattr)) _E tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                          (Tstruct _graph noattr)) _E tint)
                                      (Ebinop Oadd (Etempvar _t'6 tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  (Scall None
                                    (Evar _Union (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _subset noattr))
                                                     (Tcons tint
                                                       (Tcons tint Tnil)))
                                                   tvoid cc_default))
                                    ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                                     (Etempvar _u tint) ::
                                     (Etempvar _v tint) :: nil))))))
                          Sskip)))))))
            Sskip)
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _subsets (tptr (Tstruct _subset noattr))) :: nil)))))))
|}.

Definition f_kruskal_sort := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_graph__1, (tptr (Tstruct _graph noattr))) ::
                (_mst, (tptr (Tstruct _graph noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_V, tint) :: (_subsets, (tptr (Tstruct _subset noattr))) ::
               (_i, tint) :: (_u, tint) :: (_v, tint) :: (_ufind, tint) ::
               (_vfind, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _subset noattr))) :: (_t'21, tint) ::
               (_t'20, (tptr (Tstruct _edge noattr))) :: (_t'19, tint) ::
               (_t'18, (tptr (Tstruct _edge noattr))) ::
               (_t'17, (tptr (Tstruct _edge noattr))) :: (_t'16, tint) ::
               (_t'15, (tptr (Tstruct _edge noattr))) :: (_t'14, tint) ::
               (_t'13, (tptr (Tstruct _edge noattr))) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct _edge noattr))) :: (_t'10, tint) ::
               (_t'9, (tptr (Tstruct _edge noattr))) :: (_t'8, tint) ::
               (_t'7, (tptr (Tstruct _edge noattr))) :: (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _edge noattr))) :: (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _V
    (Efield
      (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
        (Tstruct _graph noattr)) _V tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _makeSet (Tfunction (Tcons tint Tnil)
                         (tptr (Tstruct _subset noattr)) cc_default))
        ((Etempvar _V tint) :: nil))
      (Sset _subsets (Etempvar _t'1 (tptr (Tstruct _subset noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'20
          (Efield
            (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
              (Tstruct _graph noattr)) _edge_list
            (tptr (Tstruct _edge noattr))))
        (Ssequence
          (Sset _t'21
            (Efield
              (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                (Tstruct _graph noattr)) _E tint))
          (Scall None
            (Evar _sort_edges (Tfunction
                                (Tcons (tptr (Tstruct _edge noattr))
                                  (Tcons tint (Tcons tint Tnil))) tvoid
                                cc_default))
            ((Etempvar _t'20 (tptr (Tstruct _edge noattr))) ::
             (Econst_int (Int.repr 0) tint) :: (Etempvar _t'21 tint) :: nil))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'19
                  (Efield
                    (Ederef
                      (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                      (Tstruct _graph noattr)) _E tint))
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Etempvar _t'19 tint) tint)
                  Sskip
                  Sbreak))
              (Ssequence
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef
                        (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                        (Tstruct _graph noattr)) _edge_list
                      (tptr (Tstruct _edge noattr))))
                  (Sset _u
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _t'18 (tptr (Tstruct _edge noattr)))
                          (Etempvar _i tint) (tptr (Tstruct _edge noattr)))
                        (Tstruct _edge noattr)) _u tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'17
                      (Efield
                        (Ederef
                          (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                          (Tstruct _graph noattr)) _edge_list
                        (tptr (Tstruct _edge noattr))))
                    (Sset _v
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _t'17 (tptr (Tstruct _edge noattr)))
                            (Etempvar _i tint) (tptr (Tstruct _edge noattr)))
                          (Tstruct _edge noattr)) _v tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _find (Tfunction
                                      (Tcons (tptr (Tstruct _subset noattr))
                                        (Tcons tint Tnil)) tint cc_default))
                        ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                         (Etempvar _u tint) :: nil))
                      (Sset _ufind (Etempvar _t'2 tint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _find (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _subset noattr))
                                          (Tcons tint Tnil)) tint cc_default))
                          ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                           (Etempvar _v tint) :: nil))
                        (Sset _vfind (Etempvar _t'3 tint)))
                      (Sifthenelse (Ebinop One (Etempvar _ufind tint)
                                     (Etempvar _vfind tint) tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Ederef
                                  (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                  (Tstruct _graph noattr)) _edge_list
                                (tptr (Tstruct _edge noattr))))
                            (Ssequence
                              (Sset _t'14
                                (Efield
                                  (Ederef
                                    (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                    (Tstruct _graph noattr)) _E tint))
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                      (Tstruct _graph noattr)) _edge_list
                                    (tptr (Tstruct _edge noattr))))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'15 (tptr (Tstruct _edge noattr)))
                                          (Etempvar _i tint)
                                          (tptr (Tstruct _edge noattr)))
                                        (Tstruct _edge noattr)) _u tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _t'13 (tptr (Tstruct _edge noattr)))
                                          (Etempvar _t'14 tint)
                                          (tptr (Tstruct _edge noattr)))
                                        (Tstruct _edge noattr)) _u tint)
                                    (Etempvar _t'16 tint))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                    (Tstruct _graph noattr)) _edge_list
                                  (tptr (Tstruct _edge noattr))))
                              (Ssequence
                                (Sset _t'10
                                  (Efield
                                    (Ederef
                                      (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                      (Tstruct _graph noattr)) _E tint))
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _edge_list
                                      (tptr (Tstruct _edge noattr))))
                                  (Ssequence
                                    (Sset _t'12
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'11 (tptr (Tstruct _edge noattr)))
                                            (Etempvar _i tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _v tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'9 (tptr (Tstruct _edge noattr)))
                                            (Etempvar _t'10 tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _v tint)
                                      (Etempvar _t'12 tint))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Ederef
                                      (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                      (Tstruct _graph noattr)) _edge_list
                                    (tptr (Tstruct _edge noattr))))
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Ederef
                                        (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _E tint))
                                  (Ssequence
                                    (Sset _t'7
                                      (Efield
                                        (Ederef
                                          (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                          (Tstruct _graph noattr)) _edge_list
                                        (tptr (Tstruct _edge noattr))))
                                    (Ssequence
                                      (Sset _t'8
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'7 (tptr (Tstruct _edge noattr)))
                                              (Etempvar _i tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _weight
                                          tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _t'5 (tptr (Tstruct _edge noattr)))
                                              (Etempvar _t'6 tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _weight
                                          tint) (Etempvar _t'8 tint))))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'4
                                    (Efield
                                      (Ederef
                                        (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _E tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _mst (tptr (Tstruct _graph noattr)))
                                        (Tstruct _graph noattr)) _E tint)
                                    (Ebinop Oadd (Etempvar _t'4 tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Scall None
                                  (Evar _Union (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _subset noattr))
                                                   (Tcons tint
                                                     (Tcons tint Tnil)))
                                                 tvoid cc_default))
                                  ((Etempvar _subsets (tptr (Tstruct _subset noattr))) ::
                                   (Etempvar _u tint) ::
                                   (Etempvar _v tint) :: nil))))))
                        Sskip))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _subsets (tptr (Tstruct _subset noattr))) :: nil))))))
|}.

Definition f_init_graph_sample := {|
  fn_return := (tptr (Tstruct _graph noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_graph__1, (tptr (Tstruct _graph noattr))) ::
               (_edge_list, (tptr (Tstruct _edge noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _graph noattr) tuint) :: nil))
    (Sset _graph__1 (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
          (Tstruct _graph noattr)) _V tint) (Econst_int (Int.repr 6) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
            (Tstruct _graph noattr)) _E tint) (Econst_int (Int.repr 6) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                             cc_default))
            ((Ebinop Omul (Econst_int (Int.repr 6) tint)
               (Esizeof (Tstruct _edge noattr) tuint) tuint) :: nil))
          (Sset _edge_list (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct _edge noattr))) (Tstruct _edge noattr)) _u
              tint) (Econst_int (Int.repr 4) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _edge noattr))) (Tstruct _edge noattr)) _v
                tint) (Econst_int (Int.repr 5) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _edge noattr))) (Tstruct _edge noattr))
                  _weight tint) (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                        (Econst_int (Int.repr 1) tint)
                        (tptr (Tstruct _edge noattr)))
                      (Tstruct _edge noattr)) _u tint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                          (Econst_int (Int.repr 1) tint)
                          (tptr (Tstruct _edge noattr)))
                        (Tstruct _edge noattr)) _v tint)
                    (Econst_int (Int.repr 2) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                            (Econst_int (Int.repr 1) tint)
                            (tptr (Tstruct _edge noattr)))
                          (Tstruct _edge noattr)) _weight tint)
                      (Econst_int (Int.repr 6) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                              (Econst_int (Int.repr 2) tint)
                              (tptr (Tstruct _edge noattr)))
                            (Tstruct _edge noattr)) _u tint)
                        (Econst_int (Int.repr 2) tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                (Econst_int (Int.repr 2) tint)
                                (tptr (Tstruct _edge noattr)))
                              (Tstruct _edge noattr)) _v tint)
                          (Econst_int (Int.repr 3) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                  (Econst_int (Int.repr 2) tint)
                                  (tptr (Tstruct _edge noattr)))
                                (Tstruct _edge noattr)) _weight tint)
                            (Econst_int (Int.repr 4) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                    (Econst_int (Int.repr 3) tint)
                                    (tptr (Tstruct _edge noattr)))
                                  (Tstruct _edge noattr)) _u tint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr (Tstruct _edge noattr)))
                                    (Tstruct _edge noattr)) _v tint)
                                (Econst_int (Int.repr 3) tint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr (Tstruct _edge noattr)))
                                      (Tstruct _edge noattr)) _weight tint)
                                  (Econst_int (Int.repr 5) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                          (Econst_int (Int.repr 4) tint)
                                          (tptr (Tstruct _edge noattr)))
                                        (Tstruct _edge noattr)) _u tint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                            (Econst_int (Int.repr 4) tint)
                                            (tptr (Tstruct _edge noattr)))
                                          (Tstruct _edge noattr)) _v tint)
                                      (Econst_int (Int.repr 1) tint))
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr (Tstruct _edge noattr)))
                                            (Tstruct _edge noattr)) _weight
                                          tint)
                                        (Econst_int (Int.repr 5) tint))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                                (Econst_int (Int.repr 5) tint)
                                                (tptr (Tstruct _edge noattr)))
                                              (Tstruct _edge noattr)) _u
                                            tint)
                                          (Econst_int (Int.repr 1) tint))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                                  (Econst_int (Int.repr 5) tint)
                                                  (tptr (Tstruct _edge noattr)))
                                                (Tstruct _edge noattr)) _v
                                              tint)
                                            (Econst_int (Int.repr 3) tint))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _edge_list (tptr (Tstruct _edge noattr)))
                                                    (Econst_int (Int.repr 5) tint)
                                                    (tptr (Tstruct _edge noattr)))
                                                  (Tstruct _edge noattr))
                                                _weight tint)
                                              (Econst_int (Int.repr 5) tint))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _graph__1 (tptr (Tstruct _graph noattr)))
                                                    (Tstruct _graph noattr))
                                                  _edge_list
                                                  (tptr (Tstruct _edge noattr)))
                                                (Etempvar _edge_list (tptr (Tstruct _edge noattr))))
                                              (Sreturn (Some (Etempvar _graph__1 (tptr (Tstruct _graph noattr))))))))))))))))))))))))))))
|}.

Definition f_init_mst := {|
  fn_return := (tptr (Tstruct _graph noattr));
  fn_callconv := cc_default;
  fn_params := ((_V, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_mst, (tptr (Tstruct _graph noattr))) ::
               (_edge_list, (tptr (Tstruct _edge noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _graph noattr) tuint) :: nil))
    (Sset _mst (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _mst (tptr (Tstruct _graph noattr)))
          (Tstruct _graph noattr)) _V tint) (Etempvar _V tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _mst (tptr (Tstruct _graph noattr)))
            (Tstruct _graph noattr)) _E tint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                             cc_default))
            ((Ebinop Omul (Etempvar _V tint)
               (Esizeof (Tstruct _edge noattr) tuint) tuint) :: nil))
          (Sset _edge_list (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _mst (tptr (Tstruct _graph noattr)))
                (Tstruct _graph noattr)) _edge_list
              (tptr (Tstruct _edge noattr)))
            (Etempvar _edge_list (tptr (Tstruct _edge noattr))))
          (Sreturn (Some (Etempvar _mst (tptr (Tstruct _graph noattr))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _subset Struct ((_parent, tint) :: (_rank, tuint) :: nil) noattr ::
 Composite _edge Struct
   ((_u, tint) :: (_v, tint) :: (_weight, tint) :: nil)
   noattr ::
 Composite _graph Struct
   ((_V, tint) :: (_E, tint) ::
    (_edge_list, (tptr (Tstruct _edge noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_push,
   Gfun(External (EF_external "push"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons tint (Tcons tint (Tcons (tptr tint) Tnil))) tvoid cc_default)) ::
 (_popMin,
   Gfun(External (EF_external "popMin"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tint) Tnil) tint cc_default)) ::
 (_pq_emp,
   Gfun(External (EF_external "pq_emp"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tint) Tnil) tint cc_default)) ::
 (_find,
   Gfun(External (EF_external "find"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _subset noattr)) (Tcons tint Tnil)) tint
     cc_default)) ::
 (_Union,
   Gfun(External (EF_external "Union"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _subset noattr)) (Tcons tint (Tcons tint Tnil)))
     tvoid cc_default)) ::
 (_makeSet,
   Gfun(External (EF_external "makeSet"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _subset noattr)) cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_sort_edges, Gfun(Internal f_sort_edges)) ::
 (_free_graph, Gfun(Internal f_free_graph)) ::
 (_kruskal, Gfun(Internal f_kruskal)) ::
 (_kruskal_sort, Gfun(Internal f_kruskal_sort)) ::
 (_init_graph_sample, Gfun(Internal f_init_graph_sample)) ::
 (_init_mst, Gfun(Internal f_init_mst)) :: nil).

Definition public_idents : list ident :=
(_init_mst :: _init_graph_sample :: _kruskal_sort :: _kruskal ::
 _free_graph :: _sort_edges :: _free :: _mallocN :: _makeSet :: _Union ::
 _find :: _pq_emp :: _popMin :: _push :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


