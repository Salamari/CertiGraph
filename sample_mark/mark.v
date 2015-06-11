Require Import Clightdefs.

Local Open Scope Z_scope.

Definition ___builtin_ctz : ident := 40%positive.
Definition ___i64_umod : ident := 32%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_bswap16 : ident := 38%positive.
Definition ___builtin_fnmadd : ident := 46%positive.
Definition _n : ident := 54%positive.
Definition ___i64_dtou : ident := 24%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___NODE : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _x : ident := 50%positive.
Definition ___builtin_fmin : ident := 43%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition _hd : ident := 53%positive.
Definition ___builtin_fnmsub : ident := 47%positive.
Definition _r : ident := 10%positive.
Definition ___builtin_fmadd : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition ___builtin_bswap : ident := 36%positive.
Definition ___i64_smod : ident := 31%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___i64_utod : ident := 26%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_clz : ident := 39%positive.
Definition ___builtin_fabs : ident := 11%positive.
Definition ___builtin_read32_reversed : ident := 49%positive.
Definition ___builtin_bswap32 : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___i64_utof : ident := 28%positive.
Definition _m : ident := 7%positive.
Definition ___builtin_fmax : ident := 42%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition _l : ident := 9%positive.
Definition _mark : ident := 52%positive.
Definition ___builtin_fmsub : ident := 45%positive.
Definition ___builtin_fsqrt : ident := 41%positive.
Definition ___builtin_annot : ident := 13%positive.
Definition ___i64_stof : ident := 27%positive.
Definition ___i64_shl : ident := 33%positive.
Definition ___i64_stod : ident := 25%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___i64_shr : ident := 34%positive.
Definition ___i64_sdiv : ident := 29%positive.
Definition _main : ident := 55%positive.
Definition ___i64_sar : ident := 35%positive.
Definition ___i64_udiv : ident := 30%positive.
Definition ___i64_dtos : ident := 23%positive.
Definition _root_mark : ident := 51%positive.
Definition ___builtin_read16_reversed : ident := 48%positive.
Definition ___compcert_va_int32 : ident := 20%positive.

Definition f_mark := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct ___NODE noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (talignas 4%N (Tstruct ___NODE noattr)))) ::
               (_r, (tptr (talignas 4%N (Tstruct ___NODE noattr)))) ::
               (_root_mark, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct ___NODE noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _root_mark
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct ___NODE noattr)))
          (Tstruct ___NODE noattr)) _m tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _root_mark tint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Sset _l
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct ___NODE noattr)))
              (Tstruct ___NODE noattr)) _l
            (tptr (talignas 4%N (Tstruct ___NODE noattr)))))
        (Ssequence
          (Sset _r
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct ___NODE noattr)))
                (Tstruct ___NODE noattr)) _r
              (tptr (talignas 4%N (Tstruct ___NODE noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct ___NODE noattr)))
                  (Tstruct ___NODE noattr)) _m tint)
              (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall None
                (Evar _mark (Tfunction
                              (Tcons (tptr (Tstruct ___NODE noattr)) Tnil)
                              tvoid cc_default))
                ((Etempvar _l (tptr (talignas 4%N (Tstruct ___NODE noattr)))) ::
                 nil))
              (Scall None
                (Evar _mark (Tfunction
                              (Tcons (tptr (Tstruct ___NODE noattr)) Tnil)
                              tvoid cc_default))
                ((Etempvar _r (tptr (talignas 4%N (Tstruct ___NODE noattr)))) ::
                 nil)))))))))
|}.

Definition v_hd := {|
  gvar_info := (tptr (talignas 4%N (Tstruct ___NODE noattr)));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_n := {|
  gvar_info := (talignas 4%N (Tstruct ___NODE noattr));
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign (Evar _hd (tptr (talignas 4%N (Tstruct ___NODE noattr))))
    (Eaddrof (Evar _n (talignas 4%N (Tstruct ___NODE noattr)))
      (tptr (talignas 4%N (Tstruct ___NODE noattr)))))
  (Ssequence
    (Sassign
      (Efield (Evar _n (talignas 4%N (Tstruct ___NODE noattr))) _m tint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield (Evar _n (talignas 4%N (Tstruct ___NODE noattr))) _l
          (tptr (talignas 4%N (Tstruct ___NODE noattr))))
        (Evar _hd (tptr (talignas 4%N (Tstruct ___NODE noattr)))))
      (Ssequence
        (Sassign
          (Efield (Evar _n (talignas 4%N (Tstruct ___NODE noattr))) _r
            (tptr (talignas 4%N (Tstruct ___NODE noattr))))
          (Econst_int (Int.repr 0) tint))
        (Scall None
          (Evar _mark (Tfunction (Tcons (tptr (Tstruct ___NODE noattr)) Tnil)
                        tvoid cc_default))
          ((Evar _hd (tptr (talignas 4%N (Tstruct ___NODE noattr)))) :: nil))))))
|}.

Definition composites : list composite_definition :=
(Composite ___NODE Struct
   ((_m, tint) :: (_l, (tptr (talignas 4%N (Tstruct ___NODE noattr)))) ::
    (_r, (tptr (talignas 4%N (Tstruct ___NODE noattr)))) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin ___builtin_membar
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_external ___i64_dtos
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_external ___i64_dtou
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_external ___i64_stod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_external ___i64_utod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_external ___i64_stof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_external ___i64_utof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_external ___i64_sdiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_external ___i64_udiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_external ___i64_smod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_external ___i64_umod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_external ___i64_shl
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_external ___i64_shr
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_external ___i64_sar
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin ___builtin_clz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin ___builtin_ctz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) :: (_mark, Gfun(Internal f_mark)) ::
 (_hd, Gvar v_hd) :: (_n, Gvar v_n) :: (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _n :: _hd :: _mark :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctz :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

