Require Import VST.floyd.proofauto VST.floyd.VSU.
From CertiGraph.CertiGC Require Import 
   env_graph_gc
   spec_gc verif_Is_from verif_create_heap verif_create_space
   verif_do_generation verif_do_scan verif_forward verif_forward_roots
   verif_garbage_collect verif_is_ptr verif_make_tinfo verif_resume.

Local Open Scope logic.

Definition GC_E : funspecs := nil.

Definition GC_GP : globals -> mpred := all_string_constants Ers.

Lemma init_data_tarray_tuchar: (* move this to vst/floyd/globals_lemmas.v *)
  forall {cs : compspecs} sh (gv : globals) (b : block) (xs : list int) (i : ptrofs),
  Ptrofs.unsigned i + Zlength xs < Ptrofs.modulus ->
  Forall (fun a => Int.unsigned a <= Byte.max_unsigned) xs ->
  init_data_list2pred gv (map Init_int8 xs) sh (Vptr b i)
  |-- data_at sh (tarray tuchar (Zlength xs)) (map Vint xs) (Vptr b i).
Proof. 
  intros.
  replace xs with (map (Int.zero_ext 8) xs). 
  2:{
    clear - H0.
    induction H0; simpl; auto. f_equal; auto.
    apply zero_ext_inrange. simpl. rep_lia.
  }
  clear H0; revert i H; 
  induction xs; intros; simpl.
  - rewrite data_at_zero_array_eq; auto; reflexivity.
  - rewrite Zlength_cons in H.
    specialize (Zlength_nonneg xs); intros L.
    unfold Ptrofs.add. rewrite ! Ptrofs.unsigned_repr; try rep_lia.
    rewrite (split2_data_at_Tarray sh tuchar (Zlength (Int.zero_ext 8 a :: (map (Int.zero_ext 8) xs))) 1
            (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs)) (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs))
            (sublist 0 1 (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs)))
            (sublist 1 (Zlength (Int.zero_ext 8 a :: xs)) (Vint (Int.zero_ext 8 a) :: map Vint (map (Int.zero_ext 8) xs))) (Vptr b i)); try list_solve.

   apply sepcon_derives.
   + fold tuchar. 
     rewrite (data_at_singleton_array_eq sh tuchar (Vint (Int.zero_ext 8 a)))
       by trivial.
     erewrite mapsto_data_at'; auto; trivial.
     rewrite Int.zero_ext_idem by lia. auto.
     red; simpl; intuition auto with *.
     econstructor. reflexivity. simpl; trivial. apply Z.divide_1_l.
   + eapply derives_trans. apply IHxs; clear IHxs.
     * rewrite ! Ptrofs.unsigned_repr; try rep_lia.
     * rewrite Zlength_cons.
       unfold Z.succ. rewrite Z.add_simpl_r. autorewrite with sublist.
       rewrite sublist_pos_cons by lia.
       rewrite sublist_same by list_solve.
       apply derives_refl'. f_equal.
       unfold field_address0. rewrite if_true; simpl; trivial.
       red; intuition auto with *.
       -- reflexivity.
       -- red. rewrite sizeof_Tarray, Z.max_r. simpl sizeof; rep_lia. list_solve.
       -- eapply align_compatible_rec_Tarray; intros.
          econstructor. reflexivity.
          simpl. apply Z.divide_1_l.
Qed. 



Definition ok_initbyte (b: init_data) : bool :=
 match b with
 | Init_int8 i => andb (negb (Z.eqb (Int.intval i) 0)) (andb (Z.leb 0 (Int.intval i)) (Z.ltb (Int.intval i) 128))
 | _ => false 
 end.

#[export] Instance Inhabitant_init_data: Inhabitant init_data := Init_int8 Int.zero.

Lemma globvar2pred_cstring: (* move this to vst/floyd/globals_lemmas.v *)
 forall {cs: compspecs} gv i v,
  headptr (gv i) ->
  0 < Zlength (gvar_init v) < Ptrofs.modulus ->
  Znth (Zlength (gvar_init v)-1) (gvar_init v) = Init_int8 Int.zero ->
  gvar_volatile v = false ->
  forallb ok_initbyte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v)) = true ->
  gvar_info v = tarray tschar (Zlength (gvar_init v)) ->
  (globvar2pred gv (i, v) |--
  cstring (readonly2share (gvar_readonly v)) (map init_data2byte (sublist 0 (Zlength (gvar_init v)-1) (gvar_init v))) (gv i)).
Proof.
intros cs gv i v HEAD BOUND ZERO; intros.
destruct HEAD as [b ?].
destruct v;
unfold globvar2pred; simpl in *.
rewrite H; clear gvar_volatile H.
rename gvar_init into bl0.
set (bl := sublist 0 (Zlength bl0 - 1) bl0) in *.
assert (exists al, map Init_int8 al = bl
         /\ ~In Byte.zero (map (Basics.compose Byte.repr Int.intval) al)). {
  clear - H0. clearbody bl.
  induction bl. exists nil; auto.
  simpl in H0.
  destruct a; try discriminate H0.
  rewrite andb_true_iff in H0. destruct H0.
  destruct (IHbl H0) as [j [H3 H4]].
  exists (i::j); simpl.
  split.
  f_equal. auto.
  contradict H4. destruct H4; auto.
  simpl in H.
  exfalso; clear - H1 H.
  rewrite !andb_true_iff in H; destruct H as [? [? ?]].
  forget (Int.intval i) as j. clear i.
  apply negb_true_iff, Z.eqb_neq in H. 
  apply Z.leb_le in H0. apply Z.ltb_lt in H2.
  assert (Byte.signed (Byte.repr j) = Byte.signed (Byte.zero)) by congruence.
  rewrite Byte.signed_repr in H3 by rep_lia. contradiction.
}
rewrite H2.
destruct H as [al [H3 H3']].
subst bl.
replace bl0 with (map Init_int8 (al ++ [Int.zero])). 
 2:{ rewrite map_app. rewrite H3.
      simpl map. rewrite <- ZERO. list_solve.
}
eapply derives_trans.
apply init_data_tarray_tuchar.
list_solve.
{ rewrite <- H3 in H0. clear - H0.
  apply Forall_app. 
  split;[ | repeat constructor; rewrite Int.unsigned_zero; rep_lia].
  induction al; simpl in *.
  constructor.
  rewrite !andb_true_iff in H0; destruct H0 as [[ ? [??]] ?].
  constructor; auto.
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  change Int.intval with Int.unsigned in *. rep_lia.
}
unfold cstring.
rewrite data_at_tarray_tschar_tuchar.
apply andp_right.
apply prop_right.
replace (map _ _) with (map (Byte.repr oo Int.intval) al); auto.
autorewrite with sublist. rewrite sublist_map.
rewrite sublist_app1 by rep_lia.
rewrite sublist_same by lia.
clear.
induction al; simpl; auto. f_equal; auto.
rewrite !Zlength_map.
assert (map Vubyte (map init_data2byte (map Init_int8 al)) = map Vint al). {
  rewrite <- H3 in H0.
  clear - H0.
  induction al; simpl in *; auto.
  rewrite !andb_true_iff in H0.
  destruct H0 as [[? [? ?]] ?].
  f_equal; auto.
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  unfold Vubyte. f_equal.
  rewrite Byte.unsigned_repr by rep_lia.
  change (Int.intval a) with (Int.unsigned a).
  rewrite Int.repr_unsigned. auto.
}
autorewrite with sublist.
apply derives_refl'.
f_equal.
rewrite sublist_map.
autorewrite with sublist.
rewrite !map_app.
f_equal.
auto.
Qed.


Lemma match_globals: 
  forall gv : globals,
  InitGPred (Vardefs (QPprog gc_stack.prog) ) gv |-- all_string_constants Ers gv.
Proof.
intros.
unfold all_string_constants.
repeat match goal with |- context [gv ?i] => progress (unfold i) end.
set (j := Vardefs _); hnf in j; simpl in j; subst j.
cbv [InitGPred fold_right map Maps.PTree.prev Maps.PTree.prev_append
     globs2pred].
Intros.
rewrite !sepcon_assoc.
apply sepcon_derives.
apply derives_refl.
repeat
match goal with |- context [globvar2pred ?gv (?i, ?v)] =>
  sep_apply (globvar2pred_cstring gv i v); [compute; split; reflexivity | ]
end.
clear.
simpl.
cancel.
Qed.


Ltac SF_vacuous ::= (* update vst/floyd/VSU.v with this new definition *)
 match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
 match goal with H: @eq compspecs _ _ |- _ => rewrite <- H end;
red; red; repeat simple apply conj;
[ reflexivity (* id_in_list ... *)
| repeat apply Forall_cons; (* Forall complete_type fn_vars *)
  try apply Forall_nil; reflexivity
| repeat constructor; simpl; rep_lia (* var_sizes_ok *)
| reflexivity (* fn_callconv ... *)
| split3; [reflexivity | reflexivity | intros; apply semax_vacuous] (* semax_body *)
| eexists; split; compute; reflexivity (* genv_find_func *)
].

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
