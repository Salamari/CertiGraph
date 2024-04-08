Require Import VST.floyd.proofauto VST.floyd.VSU.
From CertiGraph.CertiGC Require Import forward_lemmas
   env_graph_gc
   spec_gc verif_Is_from verif_create_heap verif_create_space
   verif_do_generation verif_do_scan verif_forward verif_forward_roots
   verif_garbage_collect verif_is_ptr verif_make_tinfo verif_resume.

Local Open Scope logic.

Definition GC_E : funspecs := nil.

Definition GC_GP : globals -> mpred := all_string_constants Ers.

Definition GCVSU: @VSU NullExtension.Espec
         GC_E GC_imported_specs ltac:(QPprog gc_stack.prog) 
         spec_gc.GC_ASI GC_GP.
  Proof.
    mkVSU prog GC_Internal.
    - solve_SF_internal body_is_ptr.
    - solve_SF_internal body_forward.
    - solve_SF_internal body_forward_roots.
    - admit. (* forward_remset *)
    - solve_SF_internal body_do_scan.
    - solve_SF_internal body_do_generation.
    - solve_SF_internal body_create_space.
    - solve_SF_internal body_create_heap.
    - solve_SF_internal body_make_tinfo.
    - solve_SF_internal body_resume. 
    - solve_SF_internal body_garbage_collect.
    - intros; apply match_globals.
all: fail.
Admitted.
