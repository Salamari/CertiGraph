Require Import VST.floyd.proofauto VST.floyd.VSU.
From CertiGraph.CertiGC Require Import 
   env_graph_gc
   spec_gc verif_Is_from verif_create_heap verif_create_space
   verif_do_generation verif_do_scan verif_forward verif_forward_roots
   verif_garbage_collect verif_is_ptr verif_make_tinfo verif_resume.

Local Open Scope logic.

Definition GC_imported_specs:funspecs := 
  MallocASI ++
  [spec_boxing.test_int_or_ptr_spec; spec_boxing.int_or_ptr_to_ptr_spec;
   spec_boxing.ptr_to_int_or_ptr_spec].

(*    spec_malloc.MallocASI ++ 
  [spec_boxing.test_int_or_ptr_spec; 
   (*spec_boxing.int_or_ptr_to_int_spec; *)
     spec_boxing.int_or_ptr_to_ptr_spec;
    (* spec_boxing.int_to_int_or_ptr_spec;*)
   spec_boxing.ptr_to_int_or_ptr_spec].
*)

Definition GC_E : funspecs := nil.

Require Import String.

Definition GCVSU: @VSU NullExtension.Espec
         GC_E GC_imported_specs ltac:(QPprog gc_stack.prog) 
         spec_gc.GC_ASI (all_string_constants Ews).
  Proof.
    mkVSU prog GC_Internal.
intros.
unfold Maps.PTree.prev in *; simpl in H.
admit. (* need to take provide vacuous funspecs for,
    garbage_collect_all certicoq_modify export_heap print_heapsize
   reset_heap free_heap *)
    - solve_SF_internal body_is_ptr.
    - admit.  (* Is_from *)
    - admit. (* abort *)
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
    - admit. (* match up the string constants *)
all: fail.
Admitted.
(*
intros. unfold Vardefs; simpl.
unfold all_string_constants; simpl.
unfold InitGPred; simpl.
Intros.


Search cstring.
repeat
match goal with |- context [globvar2pred ?gv (?i, ?v)] =>
  let i' := eval hnf in i in
  let v' := eval hnf in v in
  let x := constr:(init_data_list2pred gv (gvar_init v') (readonly2share (gvar_readonly v')) (gv i')) in
  let x' := eval cbv [gvar_init gvar_readonly readonly2share 
                      init_data_list2pred init_data2pred init_data_size] in x in
  change (globvar2pred gv (i,v)) with x'
end.
Print Ltac do_string2bytes.

repeat change (Int.zero_ext 8 ?x) with x.
simpl Int.zero_ext.
simpl init_data_list2pred.

   (init_data_list2pred gv (gvar_init v') (readonly2share (gvar_readonly v')) (gv i'));
  
end.
unfold gvar_init, gvar_readonly, readonly2share.

cbv [globvar2pred].
repeat change (gvar_volatile _) with false.
cbv match.

simpl gvar_init.
match goal with |- context [globvar2pred ?gv (?i, ?v)] =>

change (globvar2pred _ (_, v___stderrp)) with emp.
rewrite !sepcon_assoc.
apply sepcon_derives. auto.
apply sepcon_derives.
{


match goal with |- context [globvar2pred ?gv (?i, ?v)] =>
  let i' := eval hnf in i in
  let v' := eval hnf in v in 
  change (globvar2pred gv (i,v)) with (globvar2pred gv (i',v'))
 end.

unfold globvar2pred; simpl.


rewrite !sepcon_assoc.
repeat apply sepcon_derives.
admit.  (* stderrp *)
apply derives
f_equal.
unfold globvar2pred.
simpl gvar_volatile; cbv match.
simpl gvar_init.
simpl fst.

entailer!!.
cancel.

 subst p; simpl. apply derives_refl. solve_SF_internal 
    - 
*)
