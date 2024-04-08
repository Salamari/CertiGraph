From CertiGraph.CertiGC Require Import env_graph_gc spec_gc.
Require Import CertiGraph.msl_ext.ramification_lemmas.
Require Import VST.concurrency.conclib.
Import graph_model List_ext.

Local Open Scope logic.


Lemma change_compspecs_cstring: forall cs1 cs2: compspecs, (* put this in Floyd *)
    @cstring cs1 = @cstring cs2.
Proof.
intros.
extensionality sh s p.
unfold cstring.
f_equal.
set (u := map _ _). clearbody u.
set (n := Zlength _ + _). clearbody n.
unfold data_at.
unfold field_at.
f_equal.
f_equal.
unfold field_compatible.
f_equal; auto.
f_equal; auto.
f_equal; auto.
f_equal; auto.
unfold align_compatible.
destruct p; simpl; auto.
apply prop_ext; split; intro;
(apply align_compatible_rec_Tarray; intros j ?;
 apply align_compatible_rec_Tarray_inv with (i:=j) in H; auto;
 inv H; econstructor; eauto).
Qed.

Ltac forward.change_compspecs cs ::=
    (* remove this when issue #764 is fixed, perhaps in VST 2.15 *)
  match goal with
  | |- context [ ?cs' ] =>
        match type of cs' with
        | compspecs =>
            try (constr_eq cs cs'; fail 1); 
            first [rewrite !(change_compspecs_cstring cs' cs)
                  | change_compspecs' cs' cs];
            repeat change_compspecs' cs cs'
        end
  end.

Ltac solve_store_rule_evaluation ::= 
 (* remove this when issue #[732??] is fixed, perhaps in VST 2.14 *)
  match goal with |- @upd_reptype ?cs ?t ?gfs ?v0 ?v1 = ?B =>
   let rhs := fresh "rhs" in set (rhs := B);
  match type of rhs with ?A =>
   let a := fresh "a" in set (a:=A) in rhs; 
    lazy beta zeta iota delta [reptype reptype_gen] in a;
    cbn in a; subst a
  end;
   let h0 := fresh "h0" in let h1 := fresh "h1" in
   set (h0:=v0 : @reptype cs t); 
   set (h1:=v1 : @reptype cs (@nested_field_type cs t gfs)); 
    (* the next line should have (@update_reptype cs) instead of (update_reptype) *)
   change (@upd_reptype cs t gfs h0 h1 = rhs);
   remember_indexes gfs;
   let j := fresh "j" in match type of h0 with ?J => set (j := J) in h0 end;
   lazy beta zeta iota delta in j; subst j;
   change @upd_reptype with @upd_reptype';
   cbv - [rhs h0 h1 Znth upd_Znth Zlength myfst mysnd];
   change @myfst with @fst;
   change @mysnd with @snd;
   try unfold v1 in h1;
   revert h1; simplify_casts; cbv zeta;
   subst rhs h0; subst_indexes gfs;
  repeat match goal with
            | |- context [fst (@pair ?t1 ?t2 ?A ?B)] => change (fst(@pair t1 t2 A B)) with A
            | |- context [snd(@pair ?t1 ?t2 ?A ?B)] => change (snd(@pair t1 t2 A B)) with B
            | |-  context [@pair ?t1 ?t2 _ _] => 
                      let u1 := eval compute in t1 in
                      let u2 := eval compute in t2 in
                      progress (change_no_check t1 with u1; change_no_check t2 with u2)
            end;
  apply eq_refl
  end.


Ltac inhabited_value T ::= (* remove this when using version of VST 
    in which issue #751 is resolved, presumably VST 2.14. *)
 match T with
 | nat => constr:(O)
 | Z => constr:(0%Z)
 | list ?A => constr:(@nil A)
 | positive => xH
 | bool => false
 | prod ?A ?B => let x := inhabited_value A in
                           let y := inhabited_value B in
                               constr:(pair x y)
 | _ => match goal with
            | x:T |- _ => x 
            | x := _ : T |- _ => x
            | _ => let t := eval unfold T in T in
                   tryif constr_eq t T 
                   then fail 3 "cannot prove that type" T "is inhabited, so cannot compute deadvars.  Fix this by asserting (X:"T") above the line"
                   else inhabited_value t
            end
 end.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by lia.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (roots_outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - red in H1. rewrite Forall_forall in H1.
    rewrite (filter_sum_right_In_iff v roots) in H.
    apply H1 in H. simpl. sep_apply (graph_rep_valid_int_or_ptr _ _ H). entailer!.
Qed.

Lemma weak_derives_strong: forall (P Q: mpred),
    P |-- Q -> P |-- (weak_derives P Q && emp) * P.
Proof.
  intros. cancel. apply andp_right. 2: cancel.
  assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
  apply derives_weak. assumption.
Qed.

Lemma sapi_ptr_val: forall p m n,
    isptr p -> Int.min_signed <= n <= Int.max_signed ->
    (force_val
       (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                        (vint n))) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. rewrite sem_add_pi_ptr_special; [| easy | | easy].
  - simpl. rewrite offset_offset_val. f_equal. fold WORD_SIZE; rep_lia.
  - rewrite isptr_offset_val. assumption.
Qed.

Lemma sapil_ptr_val: forall p m n,
    isptr p ->
    if Archi.ptr64 then
      force_val
        (sem_add_ptr_long int_or_ptr_type (offset_val (WORD_SIZE * m) p)
                          (Vlong (Int64.repr n))) = offset_val (WORD_SIZE * (m + n)) p
    else
      force_val
        (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                         (vint n)) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  simpl. fold WORD_SIZE. rewrite offset_offset_val. f_equal. lia.
Qed.

Lemma data_at_mfs_eq: forall g v i sh nv,
    field_compatible int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv) ->
    0 <= i < Zlength (raw_fields (vlabel g v)) ->
    data_at sh (tarray int_or_ptr_type i) (sublist 0 i (make_fields_vals g v)) nv *
    field_at sh int_or_ptr_type [] (Znth i (make_fields_vals g v))
             (offset_val (WORD_SIZE * i) nv) =
    data_at sh (tarray int_or_ptr_type (i + 1))
            (sublist 0 (i + 1) (make_fields_vals g v)) nv.
Proof.
  intros. rewrite field_at_data_at. unfold field_address.
  rewrite if_true by assumption. simpl nested_field_type.
  simpl nested_field_offset. rewrite offset_offset_val.
  replace (WORD_SIZE * i + 0) with (WORD_SIZE * i)%Z by lia.
  rewrite <- (data_at_singleton_array_eq
                sh int_or_ptr_type _ [Znth i (make_fields_vals g v)]) by reflexivity.
  rewrite <- fields_eq_length in H0.
  rewrite (data_at_tarray_value
             sh (i + 1) i nv (sublist 0 (i + 1) (make_fields_vals g v))
             (make_fields_vals g v) (sublist 0 i (make_fields_vals g v))
             [Znth i (make_fields_vals g v)]).
  - replace (i + 1 - i) with 1 by lia. reflexivity.
  - lia.
  - lia.
  - autorewrite with sublist. reflexivity.
  - reflexivity.
  - rewrite sublist_one; [reflexivity | lia..].
Qed.

Lemma data_at__value_0_size: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 0) p |-- emp.
Proof. intros. rewrite data_at__eq. apply data_at_zero_array_inv; reflexivity. Qed.

Lemma data_at_minus1_address: forall sh v p,
    data_at sh (if Archi.ptr64 then tulong else tuint)
            v (offset_val (- WORD_SIZE) p) |--
            !! (force_val (sem_add_ptr_int (if Archi.ptr64 then tulong else tuint)
                                           Signed p (eval_unop Oneg tint (vint 1))) =
                field_address (if Archi.ptr64 then tulong else tuint) []
                              (offset_val (- WORD_SIZE) p)).
Proof.
  intros. unfold eval_unop. simpl. entailer!.
  unfold field_address. rewrite if_true by assumption. rewrite offset_offset_val.
  simpl. reflexivity.
Qed.

(** BEGIN Things to go into vst/floyd/VSU.v *)

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
  apply List.Forall_app. 
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

Require Import VST.floyd.VSU.

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
 try change (fst (?a,?b)) with a; try change (snd (?a,?b)) with b;
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

Lemma prove_G_justified:
 forall Espec cs V p Imports G,
 let SFF := @SF Espec cs V (QPglobalenv p) (Imports ++ G) in
 let obligations := filter_options (fun (ix: ident * funspec) =>
               match Maps.PTree.get (fst ix) (QP.prog_defs p) with
               | Some (Gfun fd) => Some (SFF (fst ix) fd (snd ix))
               | _ => None
               end) G in
 Forall (fun x => x) obligations ->
 (forall i phi fd, Maps.PTree.get i (QP.prog_defs p) = Some (Gfun fd) ->
  initial_world.find_id i G = Some phi ->
  @SF Espec cs V (QPglobalenv p) (Imports ++ G) i fd phi).
Proof.
intros.
subst SFF.
rewrite Forall_forall in H.
apply H; clear H.
subst obligations.
apply initial_world.find_id_e in H1.
eapply filter_options_in; try eassumption.
simpl.
rewrite H0.
auto.
Qed.


Lemma prove_idlists_equiv: forall al bl : list ident,
  linking.SortPos.sort al = linking.SortPos.sort bl ->
  (forall i, In i al <-> In i bl).
Proof.
intros.
pose proof (linking.SortPos.Permuted_sort al).
pose proof (linking.SortPos.Permuted_sort bl).
rewrite H in H0. 
split; intro.
eapply Permutation_in. eapply Permutation_sym. eassumption.
eapply Permutation_in in H2; [ | eassumption]; auto.
eapply Permutation_in. eapply Permutation_sym.  eassumption.
eapply Permutation_in in H2; [ | eassumption]; auto.
Qed.


Fixpoint skip_less_than (a: positive) (bl: list positive) :=
 match bl with
 | b :: bl' => if Pos.ltb b a then skip_less_than a bl' else bl
 | nil => nil
end.

Fixpoint diff_ident_lists al bl :=
match al, bl with
| _, nil => al
| nil, _ => nil
| a :: al', b ::bl' =>
   if Pos.ltb a b then a :: diff_ident_lists al' bl
   else if Pos.ltb b a 
        then let bl'' := skip_less_than a bl'
              in match bl'' with
                 | b3 :: bl3 => if Pos.eqb a b3 
                     then diff_ident_lists al' bl3
                     else a :: diff_ident_lists al' bl''
                 | nil => a::nil
                 end
        else diff_ident_lists al' bl'
 end.

Ltac ident_diff al bl F :=
     let l := constr:(map string_of_ident 
              (diff_ident_lists (linking.SortPos.sort al) 
                   (linking.SortPos.sort bl))) in
     let l := eval compute in l
     in F l. 
  
Ltac prove_Comp_G_dom :=
lazymatch goal with |- forall i, In i ?A <-> In i ?B =>
  apply prove_idlists_equiv;
  compute; 
  try reflexivity; 
  lazymatch goal with |- ?al = ?bl =>
     ident_diff al bl ltac:(fun l =>
     ident_diff bl al ltac:(fun r => 
      fail "Identifier mismatch!
Present only in" A ":" l "
Present only in" B ":" r))
  end
end.


Ltac mkComponent prog ::=
 hnf;
 match goal with |- Component _ _ ?IMPORTS _ _ _ _ =>
     let i := compute_list IMPORTS in
     let IMP := fresh "IMPORTS" in
     pose (IMP := @abbreviate funspecs i);
     change_no_check IMPORTS with IMP
 end;
 test_Component_prog_computed;
 let p := fresh "p" in
 match goal with |- @Component _ _ _ _ ?pp _ _ _ => set (p:=pp) end;
 let HA := fresh "HA" in 
   assert (HA: PTree_samedom cenv_cs ha_env_cs) by repeat constructor;
 let LA := fresh "LA" in 
   assert (LA: PTree_samedom cenv_cs la_env_cs) by repeat constructor;
 let OK := fresh "OK" in
  assert (OK: QPprogram_OK p)
   by (split; [apply compute_list_norepet_e; reflexivity 
           |  apply (QPcompspecs_OK_i HA LA) ]);
 (* Doing the  set(myenv...), instead of before proving the CSeq assertion,
     prevents nontermination in some cases  *)
 pose (myenv:= (QP.prog_comp_env (QPprogram_of_program prog ha_env_cs la_env_cs)));
 assert (CSeq: _ = compspecs_of_QPcomposite_env myenv 
                     (proj2 OK))
   by (apply compspecs_eq_of_QPcomposite_env; reflexivity);
 subst myenv;
 change (QPprogram_of_program prog ha_env_cs la_env_cs) with p in CSeq;
 clear HA LA;
 exists OK;
  [ check_Comp_Imports_Exports
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Externs++Imports"
  | apply compute_list_norepet_e; reflexivity || fail "Duplicate funspec among the Exports"
  | apply compute_list_norepet_e; reflexivity
  | apply forallb_isSomeGfunExternal_e; reflexivity
  | prove_Comp_G_dom (*intros; simpl; split; trivial; try solve [lookup_tac]*)
  | let i := fresh in let H := fresh in 
    intros i H; first [ solve contradiction | simpl in H];
    repeat (destruct H; [ subst; reflexivity |]); try contradiction
  | apply prove_G_justified;
    repeat apply Forall_cons; [ .. | apply Forall_nil];
    try SF_vacuous
  | finishComponent
  | first [ solve [intros; apply derives_refl] | solve [intros; reflexivity] | solve [intros; simpl; cancel] | idtac]
  ].


Definition Vprog_equiv (V' V: varspecs) := 
  fold_right (fun v => Maps.PTree.set (fst v) (snd v)) (Maps.PTree.empty type) V = 
  fold_right (fun v => Maps.PTree.set (fst v) (snd v)) (Maps.PTree.empty type) V'.

Lemma semax_body_permute_Vprog:
  forall V V' G F IS,
  Vprog_equiv V' V ->
  semax_body V' G F IS -> semax_body V G F IS.
Proof.
unfold semax_body; intros.
replace (func_tycontext F V G nil) with (func_tycontext F V' G nil); auto.
clear H0.
unfold func_tycontext, make_tycontext.
f_equal; auto.
unfold make_tycontext_g.
f_equal.
auto.
Qed.

Ltac Vprogs_domain_eq :=
 lazymatch goal with |- ?m = ?m' => 
   let x := constr:(Maps.PTree.map1 (fun _ => tt) m = Maps.PTree.map1 (fun _ => tt) m') in
   let x := eval compute in x in
   reflexivity
 end.

Ltac apply_semax_body P :=
lazymatch goal with |- semax_body ?V ?G ?F (?I, ?S) =>
  lazymatch type of P with semax_body ?V' ?G' ?F' ?IS =>
    let IS' := eval hnf in IS in 
    let I' := constr:(fst IS') in 
    let I' := eval red in I' in
    let I := eval simpl in I in
    (tryif unify I I' then idtac
     else fail 1 "You have provided a semax_body proof for" I' " but required is a semax_body proof for" I);
    (tryif change G with G' then idtac
     else fail 1 "Lemma" P "has a Gprog argument of" G' "but you have provided" G);
    (tryif change F with F' then idtac
     else fail 1 "Lemma" P "has a fundef argument of" F' "but you have provided" F);
    let S2 := constr:(snd IS) in 
    (tryif change (I,S) with IS then idtac
     else fail 1 "Lemma" P "has a funspec argument of" S "but you have provided" S);
    (tryif constr_eq V V' then idtac
     else ((apply (semax_body_permute_Vprog V V'); 
               [ compute; Vprogs_domain_eq; reflexivity 
               | ] ) 
           || (let a := constr:(map fst V') in 
            let b := constr:(map fst V) in
            let a' := constr:(map string_of_ident a) in let a' := eval compute in a' in
            let b' := constr:(map string_of_ident b) in let b' := eval compute in b' in
            ident_diff a b ltac:(fun l => 
            ident_diff b a ltac:(fun r =>
            fail 1 "Lemma" P "has a Vprog argument of" V' "but you have provided" V "
Present only in" V' ":" l "
Present only in" V ":" r "
(if those lists are both empty then the domains are the same but the types differ)")))));
    exact P
  end
end.

Ltac solve_SF_internal P ::=
  apply SF_internal_sound; eapply _SF_internal;
   [  reflexivity 
   | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
   | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
   | reflexivity
   | match goal with OK: QPprogram_OK _, CSeq: @eq compspecs _ _ |- _ =>
       rewrite <- CSeq;
       clear CSeq OK
     end;
     apply_semax_body P
   | eexists; split; 
       [ fast_Qed_reflexivity || fail "Lookup for a function identifier in QPglobalenv failed"
       | fast_Qed_reflexivity || fail "Lookup for a function pointer block in QPglobalenv failed"
   ]    ].


(** END Things to go into vst/floyd/VSU.v *)
