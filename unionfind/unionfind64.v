From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.12".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "unionfind/unionfind.c".
  Definition normalized := true.
End Info.

Definition _E : ident := $"E".
Definition _Is_from : ident := $"Is_from".
Definition _MAX_EDGES : ident := $"MAX_EDGES".
Definition _Node : ident := $"Node".
Definition _Union : ident := $"Union".
Definition _V : ident := $"V".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
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
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
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
Definition ___sFILE : ident := $"__sFILE".
Definition ___sFILEX : ident := $"__sFILEX".
Definition ___sbuf : ident := $"__sbuf".
Definition ___stderrp : ident := $"__stderrp".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_11 : ident := $"__stringlit_11".
Definition ___stringlit_12 : ident := $"__stringlit_12".
Definition ___stringlit_13 : ident := $"__stringlit_13".
Definition ___stringlit_14 : ident := $"__stringlit_14".
Definition ___stringlit_15 : ident := $"__stringlit_15".
Definition ___stringlit_16 : ident := $"__stringlit_16".
Definition ___stringlit_17 : ident := $"__stringlit_17".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition __base : ident := $"_base".
Definition __bf : ident := $"_bf".
Definition __blksize : ident := $"_blksize".
Definition __close : ident := $"_close".
Definition __cookie : ident := $"_cookie".
Definition __extra : ident := $"_extra".
Definition __file : ident := $"_file".
Definition __flags : ident := $"_flags".
Definition __lb : ident := $"_lb".
Definition __lbfsize : ident := $"_lbfsize".
Definition __nbuf : ident := $"_nbuf".
Definition __offset : ident := $"_offset".
Definition __p : ident := $"_p".
Definition __r : ident := $"_r".
Definition __read : ident := $"_read".
Definition __seek : ident := $"_seek".
Definition __size : ident := $"_size".
Definition __ub : ident := $"_ub".
Definition __ubuf : ident := $"_ubuf".
Definition __ur : ident := $"_ur".
Definition __w : ident := $"_w".
Definition __write : ident := $"_write".
Definition _a : ident := $"a".
Definition _abort : ident := $"abort".
Definition _abort_with : ident := $"abort_with".
Definition _active : ident := $"active".
Definition _alloc : ident := $"alloc".
Definition _allocated : ident := $"allocated".
Definition _args : ident := $"args".
Definition _arr : ident := $"arr".
Definition _build_heap : ident := $"build_heap".
Definition _certicoq_modify : ident := $"certicoq_modify".
Definition _create_heap : ident := $"create_heap".
Definition _create_space : ident := $"create_space".
Definition _depth : ident := $"depth".
Definition _do_generation : ident := $"do_generation".
Definition _do_scan : ident := $"do_scan".
Definition _dst : ident := $"dst".
Definition _edge : ident := $"edge".
Definition _edge_list : ident := $"edge_list".
Definition _empty_graph : ident := $"empty_graph".
Definition _exch : ident := $"exch".
Definition _exit : ident := $"exit".
Definition _export_heap : ident := $"export_heap".
Definition _fake_sp : ident := $"fake_sp".
Definition _fill_edge : ident := $"fill_edge".
Definition _find : ident := $"find".
Definition _first_available : ident := $"first_available".
Definition _forward : ident := $"forward".
Definition _forward_remset : ident := $"forward_remset".
Definition _forward_roots : ident := $"forward_roots".
Definition _fp : ident := $"fp".
Definition _fprintf : ident := $"fprintf".
Definition _fr : ident := $"fr".
Definition _frame : ident := $"frame".
Definition _frames : ident := $"frames".
Definition _free : ident := $"free".
Definition _freeSet : ident := $"freeSet".
Definition _free_graph : ident := $"free_graph".
Definition _free_heap : ident := $"free_heap".
Definition _from : ident := $"from".
Definition _from_limit : ident := $"from_limit".
Definition _from_rem_limit : ident := $"from_rem_limit".
Definition _from_start : ident := $"from_start".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _garbage_collect_all : ident := $"garbage_collect_all".
Definition _gen_level : ident := $"gen_level".
Definition _graph : ident := $"graph".
Definition _graph_E : ident := $"graph_E".
Definition _graph_V : ident := $"graph_V".
Definition _graph__1 : ident := $"graph__1".
Definition _greater : ident := $"greater".
Definition _h : ident := $"h".
Definition _hd : ident := $"hd".
Definition _heap : ident := $"heap".
Definition _heapsort : ident := $"heapsort".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _init_empty_graph : ident := $"init_empty_graph".
Definition _int_or_ptr_to_int : ident := $"int_or_ptr_to_int".
Definition _int_or_ptr_to_ptr : ident := $"int_or_ptr_to_ptr".
Definition _int_to_int_or_ptr : ident := $"int_to_int_or_ptr".
Definition _is_ptr : ident := $"is_ptr".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _kruskal : ident := $"kruskal".
Definition _limit : ident := $"limit".
Definition _lo : ident := $"lo".
Definition _main : ident := $"main".
Definition _makeSet : ident := $"makeSet".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _malloc : ident := $"malloc".
Definition _mallocK : ident := $"mallocK".
Definition _mallocN : ident := $"mallocN".
Definition _mst : ident := $"mst".
Definition _n : ident := $"n".
Definition _nalloc : ident := $"nalloc".
Definition _newp : ident := $"newp".
Definition _newv : ident := $"newv".
Definition _next : ident := $"next".
Definition _num_allocs : ident := $"num_allocs".
Definition _odata : ident := $"odata".
Definition _oldp : ident := $"oldp".
Definition _p : ident := $"p".
Definition _p0 : ident := $"p0".
Definition _p_cell : ident := $"p_cell".
Definition _p_val : ident := $"p_val".
Definition _parent : ident := $"parent".
Definition _prev : ident := $"prev".
Definition _print_heapsize : ident := $"print_heapsize".
Definition _printf : ident := $"printf".
Definition _ptr_to_int_or_ptr : ident := $"ptr_to_int_or_ptr".
Definition _q : ident := $"q".
Definition _rank : ident := $"rank".
Definition _rem_limit : ident := $"rem_limit".
Definition _remembered : ident := $"remembered".
Definition _reset_heap : ident := $"reset_heap".
Definition _result_block : ident := $"result_block".
Definition _resume : ident := $"resume".
Definition _root : ident := $"root".
Definition _roots : ident := $"roots".
Definition _s : ident := $"s".
Definition _scan : ident := $"scan".
Definition _sink : ident := $"sink".
Definition _size : ident := $"size".
Definition _sp : ident := $"sp".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _src : ident := $"src".
Definition _stack_frame : ident := $"stack_frame".
Definition _start : ident := $"start".
Definition _subset : ident := $"subset".
Definition _subsets : ident := $"subsets".
Definition _summatrix : ident := $"summatrix".
Definition _sz : ident := $"sz".
Definition _tag : ident := $"tag".
Definition _test_int_or_ptr : ident := $"test_int_or_ptr".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _tinfo : ident := $"tinfo".
Definition _to : ident := $"to".
Definition _twobytwo : ident := $"twobytwo".
Definition _u : ident := $"u".
Definition _ufind : ident := $"ufind".
Definition _unionS : ident := $"unionS".
Definition _v : ident := $"v".
Definition _va : ident := $"va".
Definition _value_sp : ident := $"value_sp".
Definition _vfind : ident := $"vfind".
Definition _w : ident := $"w".
Definition _wedge : ident := $"wedge".
Definition _weight : ident := $"weight".
Definition _x : ident := $"x".
Definition _xRank : ident := $"xRank".
Definition _xRoot : ident := $"xRoot".
Definition _y : ident := $"y".
Definition _yRank : ident := $"yRank".
Definition _yRoot : ident := $"yRoot".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.

Definition f_makeSet := {|
  fn_return := (tptr (Tstruct _Node noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_x, (tptr (Tstruct _Node noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _Node noattr) tulong) :: nil))
    (Sset _x
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _parent (tptr (Tstruct _Node noattr)))
      (Etempvar _x (tptr (Tstruct _Node noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
            (Tstruct _Node noattr)) _rank tuint)
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _x (tptr (Tstruct _Node noattr))))))))
|}.

Definition f_find := {|
  fn_return := (tptr (Tstruct _Node noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _Node noattr))) ::
               (_p0, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
        (Tstruct _Node noattr)) _parent (tptr (Tstruct _Node noattr))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _Node noattr)))
                   (Etempvar _x (tptr (Tstruct _Node noattr))) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                          (tptr (Tstruct _Node noattr)) cc_default))
            ((Etempvar _p (tptr (Tstruct _Node noattr))) :: nil))
          (Sset _p0 (Etempvar _t'1 (tptr (Tstruct _Node noattr)))))
        (Ssequence
          (Sset _p (Etempvar _p0 (tptr (Tstruct _Node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _parent
              (tptr (Tstruct _Node noattr)))
            (Etempvar _p (tptr (Tstruct _Node noattr))))))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr (Tstruct _Node noattr)))))))
|}.

Definition f_unionS := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _Node noattr))) ::
                (_y, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_xRoot, (tptr (Tstruct _Node noattr))) ::
               (_yRoot, (tptr (Tstruct _Node noattr))) :: (_xRank, tuint) ::
               (_yRank, tuint) :: (_t'2, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                    (tptr (Tstruct _Node noattr)) cc_default))
      ((Etempvar _x (tptr (Tstruct _Node noattr))) :: nil))
    (Sset _xRoot (Etempvar _t'1 (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                      (tptr (Tstruct _Node noattr)) cc_default))
        ((Etempvar _y (tptr (Tstruct _Node noattr))) :: nil))
      (Sset _yRoot (Etempvar _t'2 (tptr (Tstruct _Node noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                     (Etempvar _yRoot (tptr (Tstruct _Node noattr))) tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Sset _xRank
          (Efield
            (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
              (Tstruct _Node noattr)) _rank tuint))
        (Ssequence
          (Sset _yRank
            (Efield
              (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _rank tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _xRank tuint)
                         (Etempvar _yRank tuint) tint)
            (Sassign
              (Efield
                (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _parent
                (tptr (Tstruct _Node noattr)))
              (Etempvar _yRoot (tptr (Tstruct _Node noattr))))
            (Sifthenelse (Ebinop Ogt (Etempvar _xRank tuint)
                           (Etempvar _yRank tuint) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                    (Tstruct _Node noattr)) _parent
                  (tptr (Tstruct _Node noattr)))
                (Etempvar _xRoot (tptr (Tstruct _Node noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _parent
                    (tptr (Tstruct _Node noattr)))
                  (Etempvar _xRoot (tptr (Tstruct _Node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _rank tuint)
                  (Ebinop Oadd (Etempvar _xRank tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _Node Struct
   (Member_plain _rank tuint ::
    Member_plain _parent (tptr (Tstruct _Node noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
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
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
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
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_makeSet, Gfun(Internal f_makeSet)) :: (_find, Gfun(Internal f_find)) ::
 (_unionS, Gfun(Internal f_unionS)) :: nil).

Definition public_idents : list ident :=
(_unionS :: _find :: _makeSet :: _mallocN :: ___builtin_debug ::
 ___builtin_fmin :: ___builtin_fmax :: ___builtin_fnmsub ::
 ___builtin_fnmadd :: ___builtin_fmsub :: ___builtin_fmadd ::
 ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls :: ___builtin_fence ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


