From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "macos".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "binary_heap_pro.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _arr : ident := $"arr".
Definition _capacity : ident := $"capacity".
Definition _cells : ident := $"cells".
Definition _data : ident := $"data".
Definition _exch : ident := $"exch".
Definition _fa : ident := $"fa".
Definition _first_available : ident := $"first_available".
Definition _freeN : ident := $"freeN".
Definition _heap_cells : ident := $"heap_cells".
Definition _i : ident := $"i".
Definition _item : ident := $"item".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _key : ident := $"key".
Definition _key1 : ident := $"key1".
Definition _key2 : ident := $"key2".
Definition _key_table : ident := $"key_table".
Definition _less : ident := $"less".
Definition _lookup : ident := $"lookup".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mallocN : ident := $"mallocN".
Definition _newpri : ident := $"newpri".
Definition _oldpri : ident := $"oldpri".
Definition _pq : ident := $"pq".
Definition _pq_edit_priority : ident := $"pq_edit_priority".
Definition _pq_free : ident := $"pq_free".
Definition _pq_insert : ident := $"pq_insert".
Definition _pq_insert_nc : ident := $"pq_insert_nc".
Definition _pq_make : ident := $"pq_make".
Definition _pq_remove_min : ident := $"pq_remove_min".
Definition _pq_remove_min_nc : ident := $"pq_remove_min_nc".
Definition _pq_size : ident := $"pq_size".
Definition _priority : ident := $"priority".
Definition _sink : ident := $"sink".
Definition _size : ident := $"size".
Definition _structItem : ident := $"structItem".
Definition _structPQ : ident := $"structPQ".
Definition _swim : ident := $"swim".
Definition _table : ident := $"table".
Definition _target : ident := $"target".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_exch := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_j, tuint) :: (_k, tuint) ::
                (_arr, (tptr (Tstruct _structItem noattr))) ::
                (_lookup, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_priority, tint) :: (_data, tint) :: (_key1, tuint) ::
               (_key2, tuint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _priority
    (Efield
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr)) _priority tint))
  (Ssequence
    (Sset _data
      (Efield
        (Ederef
          (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
            (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
          (Tstruct _structItem noattr)) _data tint))
    (Ssequence
      (Sset _key1
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
              (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
            (Tstruct _structItem noattr)) _key tuint))
      (Ssequence
        (Sset _key2
          (Efield
            (Ederef
              (Ebinop Oadd
                (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
              (Tstruct _structItem noattr)) _key tuint))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                    (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
                  (Tstruct _structItem noattr)) _priority tint))
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                    (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
                  (Tstruct _structItem noattr)) _priority tint)
              (Etempvar _t'2 tint)))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                      (Etempvar _k tuint)
                      (tptr (Tstruct _structItem noattr)))
                    (Tstruct _structItem noattr)) _data tint))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                      (Etempvar _j tuint)
                      (tptr (Tstruct _structItem noattr)))
                    (Tstruct _structItem noattr)) _data tint)
                (Etempvar _t'1 tint)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                      (Etempvar _j tuint)
                      (tptr (Tstruct _structItem noattr)))
                    (Tstruct _structItem noattr)) _key tuint)
                (Etempvar _key2 tuint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _lookup (tptr tuint))
                      (Etempvar _key2 tuint) (tptr tuint)) tuint)
                  (Etempvar _j tuint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                          (Etempvar _k tuint)
                          (tptr (Tstruct _structItem noattr)))
                        (Tstruct _structItem noattr)) _priority tint)
                    (Etempvar _priority tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                            (Etempvar _k tuint)
                            (tptr (Tstruct _structItem noattr)))
                          (Tstruct _structItem noattr)) _data tint)
                      (Etempvar _data tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                              (Etempvar _k tuint)
                              (tptr (Tstruct _structItem noattr)))
                            (Tstruct _structItem noattr)) _key tuint)
                        (Etempvar _key1 tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _lookup (tptr tuint))
                            (Etempvar _key1 tuint) (tptr tuint)) tuint)
                        (Etempvar _k tuint)))))))))))))
|}.

Definition f_pq_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
        (Tstruct _structPQ noattr)) _first_available tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_capacity := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
        (Tstruct _structPQ noattr)) _capacity tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_less := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_j, tuint) :: (_k, tuint) ::
                (_arr, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef
        (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
          (Etempvar _j tuint) (tptr (Tstruct _structItem noattr)))
        (Tstruct _structItem noattr)) _priority tint))
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef
          (Ebinop Oadd (Etempvar _arr (tptr (Tstruct _structItem noattr)))
            (Etempvar _k tuint) (tptr (Tstruct _structItem noattr)))
          (Tstruct _structItem noattr)) _priority tint))
    (Sreturn (Some (Ebinop Ole (Etempvar _t'1 tint) (Etempvar _t'2 tint)
                     tint)))))
|}.

Definition f_swim := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, tuint) :: (_arr, (tptr (Tstruct _structItem noattr))) ::
                (_lookup, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _k tuint)
                     (Econst_int (Int.repr 0) tuint) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _less (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil))) tint cc_default))
            ((Etempvar _k tuint) ::
             (Ebinop Odiv
               (Ebinop Osub (Etempvar _k tuint)
                 (Econst_int (Int.repr 1) tuint) tuint)
               (Econst_int (Int.repr 2) tuint) tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
          (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
    (Ssequence
      (Scall None
        (Evar _exch (Tfunction
                      (Tcons tuint
                        (Tcons tuint
                          (Tcons (tptr (Tstruct _structItem noattr))
                            (Tcons (tptr tuint) Tnil)))) tvoid cc_default))
        ((Etempvar _k tuint) ::
         (Ebinop Odiv
           (Ebinop Osub (Etempvar _k tuint) (Econst_int (Int.repr 1) tuint)
             tuint) (Econst_int (Int.repr 2) tuint) tuint) ::
         (Etempvar _arr (tptr (Tstruct _structItem noattr))) ::
         (Etempvar _lookup (tptr tuint)) :: nil))
      (Sset _k
        (Ebinop Odiv
          (Ebinop Osub (Etempvar _k tuint) (Econst_int (Int.repr 1) tuint)
            tuint) (Econst_int (Int.repr 2) tuint) tuint))))
  Sskip)
|}.

Definition f_sink := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, tuint) :: (_arr, (tptr (Tstruct _structItem noattr))) ::
                (_first_available, tuint) :: (_lookup, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tuint) :: (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Swhile
  (Ebinop Olt
    (Ebinop Oadd
      (Ebinop Omul (Econst_int (Int.repr 2) tuint) (Etempvar _k tuint) tuint)
      (Econst_int (Int.repr 1) tuint) tuint)
    (Etempvar _first_available tuint) tint)
  (Ssequence
    (Sset _j
      (Ebinop Oadd
        (Ebinop Omul (Econst_int (Int.repr 2) tuint) (Etempvar _k tuint)
          tuint) (Econst_int (Int.repr 1) tuint) tuint))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Olt
                       (Ebinop Oadd (Etempvar _j tuint)
                         (Econst_int (Int.repr 1) tint) tuint)
                       (Etempvar _first_available tuint) tint)
          (Ssequence
            (Scall (Some _t'2)
              (Evar _less (Tfunction
                            (Tcons tuint
                              (Tcons tuint
                                (Tcons (tptr (Tstruct _structItem noattr))
                                  Tnil))) tint cc_default))
              ((Ebinop Oadd (Etempvar _j tuint)
                 (Econst_int (Int.repr 1) tint) tuint) ::
               (Etempvar _j tuint) ::
               (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
            (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
          (Sset _t'1 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sset _j
            (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          Sskip))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _less (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                Tnil))) tint cc_default))
            ((Etempvar _k tuint) :: (Etempvar _j tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) :: nil))
          (Sifthenelse (Etempvar _t'3 tint) Sbreak Sskip))
        (Ssequence
          (Scall None
            (Evar _exch (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                (Tcons (tptr tuint) Tnil)))) tvoid
                          cc_default))
            ((Etempvar _k tuint) :: (Etempvar _j tuint) ::
             (Etempvar _arr (tptr (Tstruct _structItem noattr))) ::
             (Etempvar _lookup (tptr tuint)) :: nil))
          (Sset _k (Etempvar _j tuint)))))))
|}.

Definition f_pq_insert_nc := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) ::
                (_priority, tint) :: (_data, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_fa, tuint) ::
               (_cells, (tptr (Tstruct _structItem noattr))) ::
               (_key, tuint) :: (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _fa
    (Efield
      (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
        (Tstruct _structPQ noattr)) _first_available tuint))
  (Ssequence
    (Sset _cells
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _heap_cells
        (tptr (Tstruct _structItem noattr))))
    (Ssequence
      (Sset _key
        (Efield
          (Ederef
            (Ebinop Oadd
              (Etempvar _cells (tptr (Tstruct _structItem noattr)))
              (Etempvar _fa tuint) (tptr (Tstruct _structItem noattr)))
            (Tstruct _structItem noattr)) _key tuint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Ebinop Oadd
                (Etempvar _cells (tptr (Tstruct _structItem noattr)))
                (Etempvar _fa tuint) (tptr (Tstruct _structItem noattr)))
              (Tstruct _structItem noattr)) _priority tint)
          (Etempvar _priority tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Etempvar _cells (tptr (Tstruct _structItem noattr)))
                  (Etempvar _fa tuint) (tptr (Tstruct _structItem noattr)))
                (Tstruct _structItem noattr)) _data tint)
            (Etempvar _data tint))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _key_table (tptr tuint)))
              (Scall None
                (Evar _swim (Tfunction
                              (Tcons tuint
                                (Tcons (tptr (Tstruct _structItem noattr))
                                  (Tcons (tptr tuint) Tnil))) tvoid
                              cc_default))
                ((Etempvar _fa tuint) ::
                 (Etempvar _cells (tptr (Tstruct _structItem noattr))) ::
                 (Etempvar _t'1 (tptr tuint)) :: nil)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _first_available tuint)
                (Ebinop Oadd (Etempvar _fa tuint)
                  (Econst_int (Int.repr 1) tint) tuint))
              (Sreturn (Some (Etempvar _key tuint))))))))))
|}.

Definition f_pq_edit_priority := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) :: (_key, tint) ::
                (_newpri, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_table, (tptr tuint)) ::
               (_cells, (tptr (Tstruct _structItem noattr))) ::
               (_target, tuint) :: (_oldpri, tint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _table
    (Efield
      (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
        (Tstruct _structPQ noattr)) _key_table (tptr tuint)))
  (Ssequence
    (Sset _cells
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _heap_cells
        (tptr (Tstruct _structItem noattr))))
    (Ssequence
      (Sset _target
        (Ederef
          (Ebinop Oadd (Etempvar _table (tptr tuint)) (Etempvar _key tint)
            (tptr tuint)) tuint))
      (Ssequence
        (Sset _oldpri
          (Efield
            (Ederef
              (Ebinop Oadd
                (Etempvar _cells (tptr (Tstruct _structItem noattr)))
                (Etempvar _target tuint) (tptr (Tstruct _structItem noattr)))
              (Tstruct _structItem noattr)) _priority tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Etempvar _cells (tptr (Tstruct _structItem noattr)))
                  (Etempvar _target tuint)
                  (tptr (Tstruct _structItem noattr)))
                (Tstruct _structItem noattr)) _priority tint)
            (Etempvar _newpri tint))
          (Sifthenelse (Ebinop Ole (Etempvar _newpri tint)
                         (Etempvar _oldpri tint) tint)
            (Scall None
              (Evar _swim (Tfunction
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                (Tcons (tptr tuint) Tnil))) tvoid cc_default))
              ((Etempvar _target tuint) ::
               (Etempvar _cells (tptr (Tstruct _structItem noattr))) ::
               (Etempvar _table (tptr tuint)) :: nil))
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _first_available tuint))
              (Scall None
                (Evar _sink (Tfunction
                              (Tcons tuint
                                (Tcons (tptr (Tstruct _structItem noattr))
                                  (Tcons tuint (Tcons (tptr tuint) Tnil))))
                              tvoid cc_default))
                ((Etempvar _target tuint) ::
                 (Etempvar _cells (tptr (Tstruct _structItem noattr))) ::
                 (Etempvar _t'1 tuint) :: (Etempvar _table (tptr tuint)) ::
                 nil)))))))))
|}.

Definition f_pq_remove_min_nc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) ::
                (_item, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'16, tuint) :: (_t'15, (tptr tuint)) ::
               (_t'14, (tptr (Tstruct _structItem noattr))) ::
               (_t'13, tuint) :: (_t'12, tint) :: (_t'11, tuint) ::
               (_t'10, (tptr (Tstruct _structItem noattr))) ::
               (_t'9, tint) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _structItem noattr))) ::
               (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _structItem noattr))) ::
               (_t'3, (tptr tuint)) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'16
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _first_available tuint))
    (Sassign
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _first_available tuint)
      (Ebinop Osub (Etempvar _t'16 tuint) (Econst_int (Int.repr 1) tint)
        tuint)))
  (Ssequence
    (Ssequence
      (Sset _t'13
        (Efield
          (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _first_available tuint))
      (Ssequence
        (Sset _t'14
          (Efield
            (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
              (Tstruct _structPQ noattr)) _heap_cells
            (tptr (Tstruct _structItem noattr))))
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _key_table (tptr tuint)))
          (Scall None
            (Evar _exch (Tfunction
                          (Tcons tuint
                            (Tcons tuint
                              (Tcons (tptr (Tstruct _structItem noattr))
                                (Tcons (tptr tuint) Tnil)))) tvoid
                          cc_default))
            ((Econst_int (Int.repr 0) tuint) :: (Etempvar _t'13 tuint) ::
             (Etempvar _t'14 (tptr (Tstruct _structItem noattr))) ::
             (Etempvar _t'15 (tptr tuint)) :: nil)))))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Efield
            (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
              (Tstruct _structPQ noattr)) _heap_cells
            (tptr (Tstruct _structItem noattr))))
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _first_available tuint))
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Etempvar _t'10 (tptr (Tstruct _structItem noattr)))
                    (Etempvar _t'11 tuint)
                    (tptr (Tstruct _structItem noattr)))
                  (Tstruct _structItem noattr)) _priority tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _item (tptr (Tstruct _structItem noattr)))
                  (Tstruct _structItem noattr)) _priority tint)
              (Etempvar _t'12 tint)))))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _heap_cells
              (tptr (Tstruct _structItem noattr))))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _first_available tuint))
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _t'7 (tptr (Tstruct _structItem noattr)))
                      (Etempvar _t'8 tuint)
                      (tptr (Tstruct _structItem noattr)))
                    (Tstruct _structItem noattr)) _data tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _item (tptr (Tstruct _structItem noattr)))
                    (Tstruct _structItem noattr)) _data tint)
                (Etempvar _t'9 tint)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _heap_cells
                (tptr (Tstruct _structItem noattr))))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _first_available tuint))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _t'4 (tptr (Tstruct _structItem noattr)))
                        (Etempvar _t'5 tuint)
                        (tptr (Tstruct _structItem noattr)))
                      (Tstruct _structItem noattr)) _key tuint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _item (tptr (Tstruct _structItem noattr)))
                      (Tstruct _structItem noattr)) _key tuint)
                  (Etempvar _t'6 tuint)))))
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _heap_cells
                (tptr (Tstruct _structItem noattr))))
            (Ssequence
              (Sset _t'2
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _first_available tuint))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                      (Tstruct _structPQ noattr)) _key_table (tptr tuint)))
                (Scall None
                  (Evar _sink (Tfunction
                                (Tcons tuint
                                  (Tcons (tptr (Tstruct _structItem noattr))
                                    (Tcons tuint (Tcons (tptr tuint) Tnil))))
                                tvoid cc_default))
                  ((Econst_int (Int.repr 0) tuint) ::
                   (Etempvar _t'1 (tptr (Tstruct _structItem noattr))) ::
                   (Etempvar _t'2 tuint) :: (Etempvar _t'3 (tptr tuint)) ::
                   nil))))))))))
|}.

Definition f_pq_insert := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) ::
                (_priority, tint) :: (_data, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _first_available tuint))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _capacity tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint) (Etempvar _t'3 tuint)
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _pq_insert_nc (Tfunction
                            (Tcons (tptr (Tstruct _structPQ noattr))
                              (Tcons tint (Tcons tint Tnil))) tuint
                            cc_default))
      ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
       (Etempvar _priority tint) :: (Etempvar _data tint) :: nil))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_pq_remove_min := {|
  fn_return := (tptr (Tstruct _structItem noattr));
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_item, (tptr (Tstruct _structItem noattr))) ::
               (_t'1, (tptr tvoid)) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _first_available tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _structItem noattr) tuint) :: nil))
      (Sset _item
        (Ecast (Etempvar _t'1 (tptr tvoid))
          (tptr (Tstruct _structItem noattr)))))
    (Ssequence
      (Scall None
        (Evar _pq_remove_min_nc (Tfunction
                                  (Tcons (tptr (Tstruct _structPQ noattr))
                                    (Tcons
                                      (tptr (Tstruct _structItem noattr))
                                      Tnil)) tvoid cc_default))
        ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) ::
         (Etempvar _item (tptr (Tstruct _structItem noattr))) :: nil))
      (Sreturn (Some (Etempvar _item (tptr (Tstruct _structItem noattr))))))))
|}.

Definition f_pq_make := {|
  fn_return := (tptr (Tstruct _structPQ noattr));
  fn_callconv := cc_default;
  fn_params := ((_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pq, (tptr (Tstruct _structPQ noattr))) ::
               (_table, (tptr tuint)) ::
               (_arr, (tptr (Tstruct _structItem noattr))) :: (_i, tint) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _structPQ noattr) tuint) :: nil))
    (Sset _pq
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _structPQ noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Esizeof tuint tuint) (Etempvar _size tuint) tuint) ::
         nil))
      (Sset _table (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tuint))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                           cc_default))
          ((Ebinop Omul (Esizeof (Tstruct _structItem noattr) tuint)
             (Etempvar _size tuint) tuint) :: nil))
        (Sset _arr
          (Ecast (Etempvar _t'3 (tptr tvoid))
            (tptr (Tstruct _structItem noattr)))))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _size tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                        (Etempvar _i tint)
                        (tptr (Tstruct _structItem noattr)))
                      (Tstruct _structItem noattr)) _key tuint)
                  (Etempvar _i tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                          (Etempvar _i tint)
                          (tptr (Tstruct _structItem noattr)))
                        (Tstruct _structItem noattr)) _priority tint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _arr (tptr (Tstruct _structItem noattr)))
                            (Etempvar _i tint)
                            (tptr (Tstruct _structItem noattr)))
                          (Tstruct _structItem noattr)) _data tint)
                      (Econst_int (Int.repr 0) tint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _table (tptr tuint))
                          (Etempvar _i tint) (tptr tuint)) tuint)
                      (Etempvar _i tint))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                (Tstruct _structPQ noattr)) _capacity tuint)
            (Etempvar _size tuint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                  (Tstruct _structPQ noattr)) _first_available tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                    (Tstruct _structPQ noattr)) _heap_cells
                  (tptr (Tstruct _structItem noattr)))
                (Etempvar _arr (tptr (Tstruct _structItem noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
                      (Tstruct _structPQ noattr)) _key_table (tptr tuint))
                  (Etempvar _table (tptr tuint)))
                (Sreturn (Some (Etempvar _pq (tptr (Tstruct _structPQ noattr)))))))))))))
|}.

Definition f_pq_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pq, (tptr (Tstruct _structPQ noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tuint)) ::
               (_t'1, (tptr (Tstruct _structItem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
          (Tstruct _structPQ noattr)) _key_table (tptr tuint)))
    (Scall None
      (Evar _freeN (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _t'2 (tptr tuint)) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _pq (tptr (Tstruct _structPQ noattr)))
            (Tstruct _structPQ noattr)) _heap_cells
          (tptr (Tstruct _structItem noattr))))
      (Scall None
        (Evar _freeN (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _structItem noattr))) :: nil)))
    (Scall None
      (Evar _freeN (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _pq (tptr (Tstruct _structPQ noattr))) :: nil))))
|}.

Definition composites : list composite_definition :=
(Composite _structItem Struct
   ((_key, tuint) :: (_priority, tint) :: (_data, tint) :: nil)
   noattr ::
 Composite _structPQ Struct
   ((_capacity, tuint) :: (_first_available, tuint) ::
    (_heap_cells, (tptr (Tstruct _structItem noattr))) ::
    (_key_table, (tptr tuint)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
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
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
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
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
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
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exch, Gfun(Internal f_exch)) :: (_pq_size, Gfun(Internal f_pq_size)) ::
 (_capacity, Gfun(Internal f_capacity)) :: (_less, Gfun(Internal f_less)) ::
 (_swim, Gfun(Internal f_swim)) :: (_sink, Gfun(Internal f_sink)) ::
 (_pq_insert_nc, Gfun(Internal f_pq_insert_nc)) ::
 (_pq_edit_priority, Gfun(Internal f_pq_edit_priority)) ::
 (_pq_remove_min_nc, Gfun(Internal f_pq_remove_min_nc)) ::
 (_pq_insert, Gfun(Internal f_pq_insert)) ::
 (_pq_remove_min, Gfun(Internal f_pq_remove_min)) ::
 (_pq_make, Gfun(Internal f_pq_make)) ::
 (_pq_free, Gfun(Internal f_pq_free)) :: nil).

Definition public_idents : list ident :=
(_pq_free :: _pq_make :: _pq_remove_min :: _pq_insert :: _pq_remove_min_nc ::
 _pq_edit_priority :: _pq_insert_nc :: _sink :: _swim :: _less ::
 _capacity :: _pq_size :: _exch :: _freeN :: _mallocN :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


