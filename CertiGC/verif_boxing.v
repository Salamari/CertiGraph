From VST Require Import floyd.proofauto floyd.VSU.
From CertiGraph.CertiGC Require Import spec_boxing boxing.
Local Open Scope logic.

Axiom body_test_int_or_ptr: semax_body Vprog Gprog f_test_int_or_ptr test_int_or_ptr_spec.

Lemma body_int_to_int_or_ptr:
  semax_body Vprog Gprog f_int_to_int_or_ptr int_to_int_or_ptr_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_int_or_ptr_to_int:
  semax_body Vprog Gprog f_int_or_ptr_to_int int_or_ptr_to_int_spec.
Proof.
  start_function.
  red in H. destruct x; try easy.
  forward.
Qed.

Lemma body_ptr_to_int_or_ptr:
  semax_body Vprog Gprog f_ptr_to_int_or_ptr ptr_to_int_or_ptr_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_int_or_ptr_to_ptr:
  semax_body Vprog Gprog f_int_or_ptr_to_ptr int_or_ptr_to_ptr_spec.
Proof.
  start_function.
  forward.
Qed.

Definition Boxing_internal_specs: funspecs := Gprog.
Definition Boxing_imported_specs:funspecs :=  nil.
Definition Boxing_E : funspecs := nil.

Definition BoxingVSU: @VSU NullExtension.Espec
         Boxing_E Boxing_imported_specs ltac:(QPprog prog) Gprog (fun _ => emp).
  Proof.
    mkVSU prog Boxing_internal_specs.
    - solve_SF_internal body_test_int_or_ptr.
    - solve_SF_internal body_int_or_ptr_to_int.
    - solve_SF_internal body_int_or_ptr_to_ptr.
    - solve_SF_internal body_int_to_int_or_ptr.
    - solve_SF_internal body_ptr_to_int_or_ptr.
Qed.
