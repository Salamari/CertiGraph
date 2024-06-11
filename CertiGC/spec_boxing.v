Require Import VST.floyd.proofauto.
Require Import CertiGraph.CertiGC.boxing.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope logic.

Definition valid_int_or_ptr (x: val) :=
  match x with
  | Vint i => if Archi.ptr64 then False else Int.testbit i 0 = true
  | Vptr _ z => Ptrofs.testbit z 0 = false /\ Ptrofs.testbit z 1 = false
  | Vlong i => if Archi.ptr64 then Int64.testbit i 0 = true else False
  | _ => False
  end.

Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [int_or_ptr_type]
   PROP (valid_int_or_ptr x)
   PARAMS (x)
   GLOBALS ()
   SEP ()
 POST [ tint ]
   PROP()
   RETURN(Vint (Int.repr (match x with
                           | Vint _ => if Archi.ptr64 then 0 else 1
                           | Vlong _ => if Archi.ptr64 then 1 else 0
                           | _ => 0
                           end)))
   SEP().

Definition int_or_ptr_to_int_spec :=
  DECLARE _int_or_ptr_to_int
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (is_int I32 Signed x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ (if Archi.ptr64 then tlong else tint) ]
    PROP() RETURN (x) SEP().

Definition int_or_ptr_to_ptr_spec :=
  DECLARE _int_or_ptr_to_ptr
  WITH x : val
  PRE [int_or_ptr_type ]
    PROP (isptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ tptr tvoid ]
    PROP() RETURN (x) SEP().

Definition int_to_int_or_ptr_spec :=
  DECLARE _int_to_int_or_ptr
  WITH x : val
  PRE [ (if Archi.ptr64 then tlong else tint) ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP ()
  POST [ int_or_ptr_type ]
    PROP() RETURN (x) SEP().

Definition ptr_to_int_or_ptr_spec :=
  DECLARE _ptr_to_int_or_ptr
  WITH x : val
  PRE [tptr tvoid ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ int_or_ptr_type ]
    PROP() RETURN (x) SEP().

Import rmaps.

Definition PTR_IN_RANGE_TYPE :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

From CertiGraph.CertiGC Require Import GCGraph spatial_gcgraph.  (* for weak_derives *)

Program Definition ptr_in_range_spec :=
  DECLARE _ptr_in_range
  TYPE PTR_IN_RANGE_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type]
    PROP ()
    PARAMS (start; offset_val n start; v)
    GLOBALS ()
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [tint]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    RETURN (Vint (Int.repr (if b then 1 else 0)))
    SEP (P).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl;
    rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  f_equal; f_equal; [|f_equal]; now rewrite derives_nonexpansive_l.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality t.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, approx_idem. reflexivity.
Qed.


Definition abort_with_spec :=
  DECLARE _abort_with
  WITH s: val, str: list byte, sh: share
  PRE [tptr tschar]
    PROP (readable_share sh)
    PARAMS (s)
    GLOBALS ()
    SEP (cstring sh str s)
  POST [ tvoid ]
    PROP (False) RETURN() SEP().

Definition Gprog: funspecs :=
                     [test_int_or_ptr_spec;
                      int_or_ptr_to_int_spec;
                      int_or_ptr_to_ptr_spec;
                      int_to_int_or_ptr_spec;
                      ptr_to_int_or_ptr_spec;
                      ptr_in_range_spec;
                      abort_with_spec].
