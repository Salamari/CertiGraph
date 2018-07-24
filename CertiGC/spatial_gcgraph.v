Require Import VST.veric.compcert_rmaps.
Require Export VST.progs.conclib.
Require Import VST.msl.shares.
Require Export VST.msl.wand_frame.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.ramification_lemmas.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.CertiGC.GCGraph.
Require Export RamifyCoq.CertiGC.env_graph_gc.
Require Import RamifyCoq.msl_ext.iter_sepcon.

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  data_at sh tuint (Z2val header) (offset_val (- WORD_SIZE) p) *
  data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p.

Definition vertex_rep (sh: share) (g: LGraph) (v: VType): mpred :=
  vertex_at sh (vertex_address g v) (make_header g v) (make_fields_vals g v).

Definition generation_rep (g: LGraph) (gen: nat): mpred :=
  iter_sepcon (map (fun x => (gen, x))
                   (nat_inc_list (nth_gen g gen).(number_of_vertices)))
              (vertex_rep (nth_sh g gen) g).

Definition graph_rep (g: LGraph): mpred :=
  iter_sepcon (nat_inc_list (length g.(glabel).(g_gen))) (generation_rep g).

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  let len := Zlength (live_roots_indices fi) in
  data_at
    sh (tarray tuint (len + 2))
    (map Z2val (fun_word_size fi :: len :: live_roots_indices fi)) p.

Definition space_rest_rep (sp: space): mpred :=
  if (Val.eq sp.(space_start) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(total_space) - sp.(used_space)))
                (offset_val (WORD_SIZE * used_space sp) sp.(space_start)).

Definition heap_rest_rep (hp: heap): mpred :=
  iter_sepcon hp.(spaces) space_rest_rep.

Definition space_tri (sp: space): (reptype space_type) :=
  let s := sp.(space_start) in (s, (offset_val (WORD_SIZE * sp.(used_space)) s,
                                    offset_val (WORD_SIZE * sp.(total_space)) s)).

Definition heap_struct_rep (sh: share) (sp_reps: list (reptype space_type)) (h: val):
  mpred := data_at sh heap_type sp_reps h.

Definition thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_start) in
  let n_lim := offset_val (WORD_SIZE * nursery.(total_space)) p in
  data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(used_space)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, n_lim))
          :: map space_tri (tl ti.(ti_heap).(spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition single_outlier_rep (p: GC_Pointer) :=
  EX sh: share, !!(readable_share sh) &&
                  (data_at_ sh (tptr tvoid) (GC_Pointer2val p) * TT).

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map single_outlier_rep outlier).

Lemma vertex_head_address_eq: forall g gen num,
  offset_val (- WORD_SIZE) (vertex_address g (gen, num)) =
  offset_val (WORD_SIZE * (previous_vertices_size g gen num)) (gen_start g gen).
Proof.
  intros. unfold vertex_address, vertex_offset. simpl. rewrite offset_offset_val.
  f_equal. rewrite Z.add_opp_r, Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_simpl_r.
Qed.

Lemma vertex_rep_isptr: forall sh g v,
    vertex_rep sh g v |-- !! (isptr (gen_start g (vgeneration v))).
Proof.
  intros. destruct v as [gen num]. unfold vertex_rep, vertex_at.
  rewrite vertex_head_address_eq. simpl. rewrite data_at_isptr. Intros.
  apply prop_right. unfold offset_val in H.
  destruct (gen_start g gen); try contradiction. exact I.
Qed.

Lemma vertex_rep_memory_block: forall sh g v,
    vertex_rep sh g v |--
               memory_block sh (WORD_SIZE * vertex_size g v)
               (offset_val (- WORD_SIZE) (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  destruct v as [gen num]. unfold vertex_rep, vertex_at. simpl in H.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  remember (gen_start g gen). destruct v; try contradiction.
  remember (previous_vertices_size g gen num).
  assert (0 <= z) by (rewrite Heqz; apply pvs_ge_zero).
  unfold vertex_size. entailer. rewrite <- fields_eq_length.
  destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H3 as [_ [_ [? _]]]. simpl in H3. rewrite <- H4 in H3.
  remember (previous_vertices_size g gen num).
  remember (Zlength (make_fields_vals g (gen, num))). rewrite (Z.add_comm z0).
  rewrite Z.mul_add_distr_l with (m := 1). rewrite Z.mul_1_r.
  simpl offset_val. remember (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * z))).
  rewrite <- (Ptrofs.repr_unsigned i0). remember (Ptrofs.unsigned i0) as ofs.
  assert (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1))) = Ptrofs.repr (ofs + 4)). {
    rewrite WORD_SIZE_eq in *. rewrite Z.mul_add_distr_l, Z.mul_1_r.
    rewrite <- ptrofs_add_repr, <- Ptrofs.add_assoc.
    rewrite Ptrofs.add_unsigned. rewrite <- Heqi0. rewrite <- Heqofs. f_equal.
  } assert (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1)))) =
            ofs + 4). {
    rewrite H6, Ptrofs.unsigned_repr_eq. apply Z.mod_small.
    destruct (Ptrofs.unsigned_range i0). rewrite <- Heqofs in *. omega.
  } rewrite H6. assert (0 <= z0) by (subst z0; apply Zlength_nonneg).
  rewrite memory_block_split; [| rep_omega..].
  sep_apply (data_at_memory_block
               sh tuint (Vint (Int.repr (make_header g (gen, num))))
               (Vptr b (Ptrofs.repr ofs))).
  simpl sizeof. rewrite WORD_SIZE_eq. apply cancel_left.
  sep_apply (data_at_memory_block
               sh (tarray int_or_ptr_type z0) (make_fields_vals g (gen, num))
               (Vptr b (Ptrofs.repr (ofs + 4)))). simpl sizeof. rewrite Z.max_r; auto.
Qed.

Lemma iter_sepcon_vertex_rep_ptrofs: forall g gen b i sh num,
    Vptr b i = gen_start g gen ->
    iter_sepcon (map (fun x : nat => (gen, x)) (nat_inc_list num)) (vertex_rep sh g)
                |-- !! (WORD_SIZE * previous_vertices_size g gen num +
                        Ptrofs.unsigned i < Ptrofs.modulus).
Proof.
  intros. induction num. 1: entailer.
  rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
  assert_PROP (WORD_SIZE * previous_vertices_size g gen num +
               Ptrofs.unsigned i < Ptrofs.modulus) by
      (unfold generation_rep in IHnum; sep_apply IHnum; entailer!). clear IHnum.
  simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
  rewrite vertex_head_address_eq. unfold vertex_address, vertex_offset. simpl.
  rewrite <- H. inv_int i. entailer. destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H4 as [_ [_ [? _]]]. simpl in H4. rewrite <- H5 in H4. clear H3 H6 H5.
  rewrite ptrofs_add_repr in *. apply prop_right.
  pose proof (pvs_ge_zero g gen num). rewrite Ptrofs.unsigned_repr_eq in H1.
  rewrite Z.mod_small in H1 by rep_omega. rewrite pvs_S.
  unfold vertex_size. rewrite <- fields_eq_length. rewrite WORD_SIZE_eq in *.
  rewrite Z.mul_add_distr_l, Z.mul_1_r, Z.add_assoc in H4.
  rewrite Ptrofs.unsigned_repr_eq in H4. rewrite Z.mod_small in H4 by rep_omega.
  rep_omega.
Qed.

Lemma generation_rep_ptrofs: forall g gen b i,
    Vptr b i = gen_start g gen ->
    generation_rep g gen |--
                   !! (WORD_SIZE * graph_gen_size g gen +
                       Ptrofs.unsigned i < Ptrofs.modulus).
Proof. intros. apply (iter_sepcon_vertex_rep_ptrofs g gen b i). assumption. Qed.

Lemma generation_rep_memory_block: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
    memory_block (nth_sh g gen) (WORD_SIZE * graph_gen_size g gen)
    (gen_start g gen).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  unfold generation_rep, graph_gen_size.
  remember (number_of_vertices (nth_gen g gen)) as num. clear Heqnum.
  remember (nth_sh g gen) as sh. clear Heqsh. induction num.
  - simpl. rewrite memory_block_zero_Vptr. auto.
  - sep_apply (iter_sepcon_vertex_rep_ptrofs g gen b i sh (S num) Heqv). Intros.
    rename H0 into HS. simpl in HS. unfold generation_rep.
    rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl. unfold generation_rep in IHnum. sep_apply IHnum. rewrite pvs_S, Z.add_comm.
    rewrite <- (Ptrofs.repr_unsigned i) at 2.
    remember (previous_vertices_size g gen num) as zp.
    assert (0 <= zp) by (rewrite Heqzp; apply pvs_ge_zero).
    pose proof (svs_gt_one g (gen, num)) as HS1.
    pose proof (Ptrofs.unsigned_range i) as HS2. rewrite pvs_S in HS.
    rewrite Z.add_comm, Z.mul_add_distr_l, memory_block_split; [|rep_omega..].
    rewrite (Ptrofs.repr_unsigned i). apply cancel_left.
    sep_apply (vertex_rep_memory_block sh g (gen, num)).
    rewrite vertex_head_address_eq, <- Heqzp, <- Heqv. simpl offset_val.
    rewrite <- ptrofs_add_repr, Ptrofs.repr_unsigned. auto.
Qed.

Lemma generation_rep_align_compatible: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
    !! (align_compatible (tarray int_or_ptr_type (graph_gen_size g gen))
                         (gen_start g gen)).
Proof.
  intros. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). Intros.
  unfold generation_rep, graph_gen_size in *.
  remember (number_of_vertices (nth_gen g gen)) as num. clear Heqnum.
  remember (nth_sh g gen) as sh. clear Heqsh. induction num.
  - unfold previous_vertices_size. simpl fold_left. apply prop_right.
    constructor. intros. omega.
  - unfold generation_rep. rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
    rename H0 into HS. rewrite vertex_head_address_eq. entailer!. clear H1 H2 H3 H4.
    destruct H0 as [_ [_ [_ [? _]]]]. rewrite <- Heqv in H0. inv_int i.
    hnf in H0. rewrite ptrofs_add_repr in H0. inv H0. simpl in H1. inv H1.
    simpl in H3. simpl in HS. pose proof (svs_gt_one g (gen, num)).
    pose proof (pvs_ge_zero g gen num). rewrite pvs_S in HS.
    rewrite Ptrofs.unsigned_repr_eq in H3. rewrite Z.mod_small in H3 by rep_omega.
    rewrite Z.add_comm in H3. apply Z.divide_add_cancel_r in H3.
    2: rewrite WORD_SIZE_eq; apply Z.divide_factor_l. constructor. intros.
    rewrite Ptrofs.unsigned_repr_eq. rewrite Z.mod_small by omega. simpl sizeof.
    apply align_compatible_rec_by_value with Mptr. 1: reflexivity. simpl.
    apply Z.divide_add_r; [assumption | apply Z.divide_factor_l].
Qed.

Lemma sizeof_tarray_int_or_ptr: forall n,
    0 <= n -> sizeof (tarray int_or_ptr_type n) = (WORD_SIZE * n)%Z.
Proof. intros. simpl. rewrite Z.max_r by assumption. rep_omega. Qed.

Lemma generation_rep_field_compatible: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
    !! (field_compatible (tarray int_or_ptr_type (graph_gen_size g gen))
                         [] (gen_start g gen)).
Proof.
  intros. pose proof H. apply graph_has_gen_start_isptr in H.
  remember (gen_start g gen). destruct v; try contradiction.
  unfold field_compatible. entailer. unfold size_compatible.
  rewrite sizeof_tarray_int_or_ptr by apply pvs_ge_zero.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). entailer. rewrite Heqv.
  sep_apply (generation_rep_align_compatible g gen H0). entailer!.
Qed.

Lemma generation_rep_data_at_: forall g gen,
    graph_has_gen g gen ->
    generation_rep g gen |--
                   data_at_ (nth_sh g gen)
                   (tarray int_or_ptr_type (graph_gen_size g gen))
                   (gen_start g gen).
Proof.
  intros. sep_apply (generation_rep_field_compatible g gen H). Intros.
  sep_apply (generation_rep_memory_block g gen H).
  rewrite <- sizeof_tarray_int_or_ptr by apply pvs_ge_zero.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma field_compatible_tarray_value:
  forall (n n1 : Z) (p : val),
    0 <= n1 <= n ->
    field_compatible (tarray int_or_ptr_type n1) [] p ->
    field_compatible (tarray int_or_ptr_type (n - n1)) []
                     (offset_val (WORD_SIZE * n1) p) ->
    field_compatible (tarray int_or_ptr_type n) [] p.
Proof.
  intros. unfold field_compatible. simpl. destruct H0 as [? [_ [? [? _]]]].
  destruct H1 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H0.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H1.
  rewrite sizeof_tarray_int_or_ptr in * by omega. rewrite WORD_SIZE_eq in *.
  rewrite ptrofs_add_repr in H1. do 2 rewrite Ptrofs.unsigned_repr in * by rep_omega.
  replace (Z.max 0 (n - n1)) with (n - n1) in H1 by (rewrite Z.max_r; omega).
  assert (ofs + 4 * n < Ptrofs.modulus) by omega. intuition. constructor. intros.
  simpl sizeof. rewrite Ptrofs.unsigned_repr by rep_omega.
  apply align_compatible_rec_by_value with Mptr. 1: reflexivity. simpl.
  apply Z.divide_add_r. 2: apply Z.divide_factor_l. simpl offset_val in H4.
  rewrite ptrofs_add_repr in H4. unfold align_compatible in *.
  rewrite Ptrofs.unsigned_repr in * by rep_omega.
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ H3).
  pose proof (align_compatible_rec_Tarray_inv _ _ _ _ _ H4). simpl sizeof in *.
  rewrite Z.le_lteq in H6. destruct H6.
  - assert (0 <= 0 < n1) by omega. specialize (H9 _ H11).
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H9. 2: reflexivity.
    simpl in H9. rewrite Z.add_0_r in H9. assumption.
  - subst n1. rewrite Z.sub_0_r in H10. specialize (H10 _ H5).
    apply (align_compatible_rec_by_value_inv _ _ Mptr) in H10. 2: reflexivity.
    simpl in H10. rewrite Z.add_0_r, Z.add_comm in H10.
    apply Z.divide_add_cancel_r in H10; [assumption | apply Z.divide_factor_l].
Qed.

Lemma data_at_tarray_value_fold: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray int_or_ptr_type n1) v1 p *
    data_at sh (tarray int_or_ptr_type (n - n1)) v2 (offset_val (WORD_SIZE * n1) p) |--
            data_at sh (tarray int_or_ptr_type n) v p.
Proof.
  intros. rewrite (split2_data_at_Tarray sh int_or_ptr_type n n1 v v' v1 v2);
            [|assumption..]. entailer!. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - pose proof (field_compatible_tarray_value n _ p H H4 H6). clear -H1 H.
    red in H1. red. simpl in *. intuition.
Qed.

Lemma data_at_tarray_value_unfold: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray int_or_ptr_type n) v p |--
            data_at sh (tarray int_or_ptr_type n1) v1 p *
    data_at sh (tarray int_or_ptr_type (n - n1)) v2 (offset_val (WORD_SIZE * n1) p).
Proof.
  intros. sep_apply (data_at_local_facts sh (tarray int_or_ptr_type n) v p).
  Intros. rewrite (split2_data_at_Tarray sh int_or_ptr_type n n1 v v' v1 v2);
            [|assumption..]. cancel. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - clear -H H4. red. red in H4. simpl in *. intuition.
Qed.

Lemma data_at_tarray_value: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray int_or_ptr_type n) v p =
    data_at sh (tarray int_or_ptr_type n1) v1 p *
    data_at sh (tarray int_or_ptr_type (n - n1)) v2 (offset_val (WORD_SIZE * n1) p).
Proof.
  intros. apply pred_ext.
  - apply data_at_tarray_value_unfold with v'; assumption.
  - apply data_at_tarray_value_fold with v'; assumption.
Qed.

Lemma data_at__tarray_value: forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n) p =
    data_at_ sh (tarray int_or_ptr_type n1) p *
    data_at_ sh (tarray int_or_ptr_type (n - n1)) (offset_val (WORD_SIZE * n1) p).
Proof.
  intros. rewrite !data_at__eq.
  apply data_at_tarray_value with (default_val (tarray int_or_ptr_type n));
    [assumption | unfold default_val; simpl; autorewrite with sublist..];
    [omega | reflexivity..].
Qed.

Definition valid_int_or_ptr (x: val) :=
 match x with
 | Vint i => Int.testbit i 0 = true
 | Vptr b z => Ptrofs.testbit z 0 = false
 | _ => False
 end.

Lemma valid_int_or_ptr_ii1:
 forall i, valid_int_or_ptr (Vint (Int.repr (i + i + 1))).
Proof.
intros.
simpl.
rewrite Int.unsigned_repr_eq.
rewrite Zodd_mod.
apply Zeq_is_eq_bool.
replace (i+i) with (2*i)%Z by omega.
rewrite <- Zmod_div_mod; try omega.
- rewrite Z.mul_comm, Z.add_comm, Z_mod_plus_full. reflexivity.
- compute; reflexivity.
- exists (Z.div Int.modulus 2). reflexivity.
Qed.

Lemma four_divided_odd_false: forall z, (4 | z) -> Z.odd z = false.
Proof.
  intros. rewrite Zodd_mod. apply Zdivide_mod in H. rewrite Zmod_divides in H by omega.
  destruct H. replace (4 * x)%Z with (2 * x * 2)%Z in H by omega. subst.
  rewrite Z_mod_mult. unfold Zeq_bool. simpl. reflexivity.
Qed.

Lemma vertex_rep_valid_int_or_ptr: forall sh g v,
    vertex_rep sh g v |-- !! (valid_int_or_ptr (vertex_address g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  unfold vertex_rep, vertex_at, vertex_address.
  remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
  inv_int i. simpl. rewrite !ptrofs_add_repr. entailer!.
  destruct H3 as [_ [_ [_ [? _]]]]. clear -H3. hnf in H3. inv H3.
  1: simpl in H; inversion H. assert (0 <= 0 < Zlength (make_fields_vals g v)). {
    split; [omega|]. rewrite fields_eq_length.
    destruct (raw_fields_head_cons (vlabel g v)) as [r [l [? _]]]. rewrite H.
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). omega.
  } apply H4 in H. rewrite Z.mul_0_r, Z.add_0_r in H. clear H4. inv H. inv H0.
  simpl in H1. apply four_divided_odd_false; assumption.
Qed.

Lemma graph_rep_generation_rep: forall g gen,
    graph_has_gen g gen -> graph_rep g |-- generation_rep g gen * TT.
Proof.
  intros. unfold graph_rep. red in H. rewrite <- nat_inc_list_In_iff in H.
  sep_apply (iter_sepcon_in_true (generation_rep g) _ _ H). apply derives_refl.
Qed.

Lemma generation_rep_vertex_rep: forall g gen index,
    gen_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (nth_sh g gen) g (gen, index) * TT.
Proof.
  intros. unfold generation_rep. remember (number_of_vertices (nth_gen g gen)) as num.
  assert (nth index (map (fun x : nat => (gen, x)) (nat_inc_list num))
              (gen, O) = (gen, index)). {
    change (gen, O) with ((fun x: nat => (gen, x)) O). rewrite map_nth. red in H.
    rewrite nat_inc_list_nth by omega. reflexivity.
  } assert (In (gen, index) (map (fun x : nat => (gen, x)) (nat_inc_list num))). {
    rewrite <- H0. apply nth_In. rewrite map_length, nat_inc_list_length.
    red in H. subst num. assumption.
  } apply (iter_sepcon_in_true (vertex_rep _ g) _ _ H1).
Qed.

Lemma graph_rep_vertex_rep: forall g v,
    graph_has_v g v -> graph_rep g |-- EX sh: share, !!(writable_share sh) &&
                                                       vertex_rep sh g v * TT.
Proof.
  intros. destruct H. sep_apply (graph_rep_generation_rep g (vgeneration v) H).
  red in H0. sep_apply (generation_rep_vertex_rep g (vgeneration v) _ H0).
  Exists (nth_sh g (vgeneration v)). destruct v. simpl. entailer!.
  apply generation_share_writable.
Qed.

Lemma graph_rep_valid_int_or_ptr: forall g v,
    graph_has_v g v -> graph_rep g |-- !! (valid_int_or_ptr (vertex_address g v)).
Proof.
  intros. sep_apply (graph_rep_vertex_rep g v H). Intros sh.
  sep_apply (vertex_rep_valid_int_or_ptr sh g v). entailer!.
Qed.

(* weak derives for use in funspecs *)
Program Definition weak_derives (P Q: mpred): mpred :=
  fun w => predicates_hered.derives (approx (S (level w)) P) (approx (S (level w)) Q).
Next Obligation.
  repeat intro.
  destruct H1.
  apply age_level in H.
  lapply (H0 a0); [|split; auto; omega].
  intro HQ; destruct HQ.
  eexists; eauto.
Defined.

Lemma derives_nonexpansive: forall P Q n,
  approx n (weak_derives P Q) = approx n (weak_derives (approx n P) (approx n Q)).
Proof.
  apply nonexpansive2_super_non_expansive; repeat intro.
  - split; intros ??%necR_level Hshift ? HP;
      destruct (Hshift _ HP); destruct HP; eexists;  eauto; eapply H; auto; omega.
  - split; intros ??%necR_level Hshift ? []; apply Hshift;
      split; auto; apply (H a0); auto; omega.
Qed.

Lemma derives_nonexpansive_l: forall P Q n,
  approx n (weak_derives P Q) = approx n (weak_derives (approx n P) Q).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun P => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? [];
    apply Hshift; split; auto; apply (H a0); auto; omega.
Qed.

Lemma derives_nonexpansive_r: forall P Q n,
  approx n (weak_derives P Q) = approx n (weak_derives P (approx n Q)).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun Q => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? HP;
      destruct (Hshift _ HP); destruct HP;
      eexists;  eauto;
      eapply H; auto; omega.
Qed.

Lemma derives_weak: forall P Q, P |-- Q -> TT |-- weak_derives P Q.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_derives P Q)).
  intros w _ ? [? HP].
  specialize (H _ HP).
  eexists; eauto.
Qed.

Lemma apply_derives: forall P Q, (weak_derives P Q && emp) * P |-- Q.
Proof.
  intros.
  change (predicates_hered.derives ((weak_derives P Q && emp) * P) Q).
  intros ? (? & ? & ? & [Hderives Hemp] & HP).
  destruct (join_level _ _ _ H).
  apply Hemp in H; subst.
  lapply (Hderives a); [|split; auto; omega].
  intro X; destruct X; eauto 7.
Qed.

Definition heap_rest_gen_data_at_ (g: LGraph) (t_info: thread_info) (gen: nat) :=
  data_at_ (nth_sh g gen)
           (tarray int_or_ptr_type
                   (total_space (nth_space t_info gen) - graph_gen_size g gen))
           (offset_val (WORD_SIZE * graph_gen_size g gen) (gen_start g gen)).

Lemma heap_rest_rep_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) =
    iter_sepcon (nat_inc_list (length (g_gen (glabel g))))
                (heap_rest_gen_data_at_ g t_info).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (gt_gs_compatible _ _ H). destruct H as [? [? ?]].
  rewrite <- (firstn_skipn (length (g_gen (glabel g))) (spaces (ti_heap t_info))).
  rewrite iter_sepcon_app_sepcon. rewrite <- map_skipn in H1.
  remember (skipn (length (g_gen (glabel g))) (spaces (ti_heap t_info))).
  assert (iter_sepcon l space_rest_rep = emp). {
    clear Heql. induction l; simpl. 1: reflexivity.
    rewrite IHl by (simpl in H1; apply Forall_tl in H1; assumption).
    rewrite Forall_forall in H1. simpl in H1. unfold space_rest_rep. rewrite if_true.
    - rewrite emp_sepcon; reflexivity.
    - symmetry. apply H1. left; reflexivity.
  } rewrite H3.
  replace (firstn (length (g_gen (glabel g))) (spaces (ti_heap t_info)))
    with (map (nth_space t_info) (nat_inc_list (length (g_gen (glabel g))))).
  - rewrite <- iter_sepcon_map, sepcon_emp.
    apply iter_sepcon_func_strong. intros gen ?.
    unfold space_rest_rep, heap_rest_gen_data_at_. rewrite nat_inc_list_In_iff in H4.
    specialize (H0 _ H4). destruct H0 as [? [? ?]]. rewrite <- H0, if_false.
    + unfold gen_start. rewrite if_true. 2: assumption. rewrite <- H5, <- H6. f_equal.
    + pose proof (start_isptr (nth_gen g gen)).
      destruct (start_address (nth_gen g gen)); try contradiction. intro. inversion H8.
  - unfold nth_space. remember (spaces (ti_heap t_info)) as ls.
    remember (length (g_gen (glabel g))) as m. clear -H2. revert ls H2.
    induction m; intros. 1: simpl; reflexivity. rewrite nat_inc_list_S, map_app.
    rewrite IHm by omega. simpl map. clear IHm. revert ls H2. induction m; intros.
    + destruct ls. 1: simpl in H2; exfalso; omega. simpl. reflexivity.
    + destruct ls. 1: simpl in H2; exfalso; omega.
      simpl firstn at 1. simpl nth. Opaque firstn. simpl. Transparent firstn.
      rewrite IHm by (simpl in H2; omega). simpl. destruct ls; reflexivity.
Qed.

Lemma heap_rest_rep_data_at_: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) |-- heap_rest_gen_data_at_ g t_info gen * TT.
Proof.
  intros. rewrite (heap_rest_rep_iter_sepcon g) by assumption.
  sep_apply (iter_sepcon_in_true (heap_rest_gen_data_at_ g t_info)
                                 (nat_inc_list (length (g_gen (glabel g)))) gen).
  - rewrite nat_inc_list_In_iff. assumption.
  - apply derives_refl.
Qed.

Definition generation_data_at_ g t_info gen :=
  data_at_ (nth_sh g gen)
           (tarray int_or_ptr_type (gen_size t_info gen)) (gen_start g gen).

Lemma gr_hrgda_data_at_: forall g t_info gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    generation_rep g gen *
    heap_rest_gen_data_at_ g t_info gen |-- generation_data_at_ g t_info gen.
Proof.
  intros. sep_apply (generation_rep_data_at_ g gen H).
  unfold heap_rest_gen_data_at_, generation_data_at_.
  remember (nth_sh g gen) as sh.
  rewrite <- (data_at__tarray_value sh _ _ (gen_start g gen)).
  - unfold gen_size. entailer!.
  - unfold graph_gen_size. destruct (gt_gs_compatible _ _ H0 _ H) as [_ [_ ?]].
    rewrite H1. apply space_order.
Qed.

Lemma graph_heap_rest_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                iter_sepcon (nat_inc_list (length (g_gen (glabel g))))
                                (generation_data_at_ g t_info).
Proof.
  intros. unfold graph_rep. rewrite (heap_rest_rep_iter_sepcon _ _ H).
  assert (forall gen,
             In gen (nat_inc_list (length (g_gen (glabel g)))) -> graph_has_gen g gen)
    by (intros; rewrite nat_inc_list_In_iff in H0; assumption).
  remember (length (g_gen (glabel g))). clear Heqn. revert H0. induction n; intros.
  - simpl. rewrite emp_sepcon. apply derives_refl.
  - rewrite nat_inc_list_S. rewrite !iter_sepcon_app_sepcon. simpl.
    rewrite !sepcon_emp. pull_left (generation_rep g n). rewrite <- sepcon_assoc.
    rewrite (sepcon_assoc (generation_rep g n)). sep_apply IHn.
    + intros. apply H0. rewrite nat_inc_list_S, in_app_iff. left; assumption.
    + cancel. sep_apply (gr_hrgda_data_at_ g t_info n); auto.
      apply H0. rewrite nat_inc_list_S, in_app_iff. right. left. reflexivity.
Qed.

Lemma graph_and_heap_rest_data_at_: forall (g: LGraph) (t_info: thread_info) gen,
    graph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                generation_data_at_ g t_info gen * TT.
Proof.
  intros. sep_apply (graph_heap_rest_iter_sepcon _ _ H0).
  sep_apply (iter_sepcon_in_true (generation_data_at_ g t_info)
                                 (nat_inc_list (length (g_gen (glabel g)))) gen);
    [rewrite nat_inc_list_In_iff; assumption | apply derives_refl].
Qed.

Lemma outlier_rep_single_rep: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- single_outlier_rep p * TT.
Proof.
  intros. assert (In p outlier). {
    apply H0. rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff.
    assumption. } unfold outlier_rep.
  apply (in_map single_outlier_rep) in H1. apply fold_right_andp in H1.
  destruct H1 as [Q ?]. rewrite H1. apply andp_left1. cancel.
Qed.

Lemma single_outlier_rep_valid_pointer: forall p,
    single_outlier_rep p |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  sep_apply (data_at__memory_block_cancel sh (tptr tvoid) pp). simpl sizeof.
  sep_apply (memory_block_valid_ptr sh 4 pp);
    [apply readable_nonidentity; assumption | omega | apply derives_refl].
Qed.

Lemma outlier_rep_valid_pointer: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. sep_apply (outlier_rep_single_rep _ _ _ H H0).
  sep_apply (single_outlier_rep_valid_pointer p). cancel.
Qed.

Lemma single_outlier_rep_valid_int_or_ptr: forall p,
    single_outlier_rep p |-- !! (valid_int_or_ptr (GC_Pointer2val p)).
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  clear Heqpp. entailer!. destruct H0 as [? [_ [_ [? _]]]].
  destruct pp; try contradiction. unfold align_compatible in H1. inv H1.
  inv H2. simpl in H3. simpl. apply four_divided_odd_false; assumption.
Qed.

Import Share.

Lemma writable_readable_share_common: forall rsh wsh,
  readable_share rsh -> writable_share wsh ->
  exists sh, nonunit sh /\ join_sub sh rsh /\ join_sub sh wsh.
Proof.
  intros. assert (join (glb Lsh rsh) (glb Rsh rsh) rsh). {
    apply (comp_parts_join comp_Lsh_Rsh).
    - rewrite glb_twice, <- glb_assoc, glb_Lsh_Rsh, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute Rsh), glb_Lsh_Rsh,
      (glb_commute bot), glb_bot, glb_twice. apply bot_join_eq.
  } assert (join (glb Rsh rsh) (glb Rsh (comp rsh)) Rsh). {
    rewrite !(glb_commute Rsh). apply (@comp_parts_join rsh (comp rsh)); auto.
    - rewrite glb_twice, <- glb_assoc, comp2, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute (comp _)), comp2, (glb_commute bot), glb_bot,
      glb_twice. apply bot_join_eq.
  } exists (glb Rsh rsh). split; [|split].
  - red in H. apply nonidentity_nonunit, H.
  - apply join_comm in H1. exists (glb Lsh rsh). assumption.
  - apply join_sub_trans with Rsh; [exists (glb Rsh (comp rsh))|]; assumption.
Qed.

Lemma readable_writable_memory_block_FF: forall rsh wsh m1 m2 p,
    readable_share rsh -> writable_share wsh ->
    0 < m1 <= Ptrofs.max_unsigned -> 0 < m2 <= Ptrofs.max_unsigned ->
    memory_block rsh m1 p * memory_block wsh m2 p |-- FF.
Proof.
  intros.
  destruct (writable_readable_share_common _ _ H H0) as [sh [? [[shr ?] [shw ?]]]].
  rewrite <- (memory_block_share_join _ _ _ _ _ H4).
  rewrite <- (memory_block_share_join _ _ _ _ _ H5).
  rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh m1 p)),
  (sepcon_assoc (memory_block shr m1 p)).
  sep_apply (memory_block_conflict sh _ _ p H3 H1 H2). entailer!.
Qed.

Lemma v_in_range_data_at_: forall v p n sh,
    v_in_range v p (WORD_SIZE * n) ->
    data_at_ sh (tarray int_or_ptr_type n) p |--
             EX m: Z, !!(0 < m <= Ptrofs.max_unsigned) && memory_block sh m v * TT.
Proof.
  intros. destruct H as [o [? ?]]. rewrite data_at__memory_block. Intros.
  destruct H1 as [? [_ [? _]]]. destruct p; try contradiction. inv_int i.
  simpl offset_val in H0. rewrite ptrofs_add_repr in H0.
  assert (0 <= n)%Z by rep_omega. rewrite sizeof_tarray_int_or_ptr by assumption.
  simpl in H2. rewrite Ptrofs.unsigned_repr in H2 by rep_omega.
  rewrite Z.max_r in H2 by assumption. rewrite WORD_SIZE_eq in *.
  assert (4 * n = o + (4 * n - o))%Z by omega. remember (4 * n - o) as m.
  rewrite H5 in *. rewrite (memory_block_split sh b ofs o m) by omega.
  clear Heqm n H5 H3. assert (0 < m <= Ptrofs.max_unsigned) by rep_omega.
  rewrite <- H0. Exists m. entailer!.
Qed.

Lemma single_outlier_rep_memory_block_FF: forall gp p n wsh,
    writable_share wsh -> v_in_range (GC_Pointer2val gp) p (WORD_SIZE * n) ->
    single_outlier_rep gp * data_at_ wsh (tarray int_or_ptr_type n) p |-- FF.
Proof.
  intros. unfold single_outlier_rep. Intros rsh. remember (GC_Pointer2val gp) as ggp.
  clear gp Heqggp. rename ggp into gp.
  sep_apply (v_in_range_data_at_ _ _ _ wsh H0). Intros m.
  sep_apply (data_at__memory_block_cancel rsh (tptr tvoid) gp). simpl sizeof.
  rewrite <- sepcon_assoc.
  sep_apply (readable_writable_memory_block_FF _ _ 4 m gp H1 H); auto;
    [rep_omega | entailer].
Qed.

Lemma graph_and_heap_rest_v_in_range_iff: forall g t_info gen v,
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> graph_has_v g v ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
    !! (v_in_range (vertex_address g v) (gen_start g gen)
                   (WORD_SIZE * gen_size t_info gen) <-> vgeneration v = gen).
Proof.
  intros. unfold iff. rewrite and_comm. apply prop_and_right.
  - intros. rewrite <- H2. apply graph_thread_v_in_range; assumption.
  - rewrite prop_impl, <- imp_andp_adjoint; Intros.
    destruct (Nat.eq_dec (vgeneration v) gen). 1: apply prop_right; assumption.
    sep_apply (graph_heap_rest_iter_sepcon _ _ H).
    pose proof (graph_thread_v_in_range _ _ _ H H1). destruct H1.
    assert (NoDup [vgeneration v; gen]) by
        (constructor; [|constructor; [|constructor]]; intro HS;
         simpl in HS; destruct HS; auto).
    assert (incl [vgeneration v; gen] (nat_inc_list (length (g_gen (glabel g))))) by
        (apply incl_cons; [|apply incl_cons];
         [rewrite nat_inc_list_In_iff; assumption..| apply incl_nil]).
    sep_apply (iter_sepcon_incl_true (generation_data_at_ g t_info) H5 H6); simpl.
    rewrite sepcon_emp. unfold generation_data_at_.
    remember (nth_sh g (vgeneration v)) as sh1. remember (nth_sh g gen) as sh2.
    sep_apply (v_in_range_data_at_ _ _ _ sh1 H3). Intros m1.
    sep_apply (v_in_range_data_at_ _ _ _ sh2 H2). Intros m2.
    remember (vertex_address g v) as p.
    rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh2 m2 p)),
    (sepcon_assoc TT).
    sep_apply (readable_writable_memory_block_FF sh2 sh1 m2 m1 p); auto.
    + apply writable_readable. subst. apply generation_share_writable.
    + subst. apply generation_share_writable.
    + entailer!.
Qed.

Lemma graph_gen_ramif_stable: forall g gen,
    graph_has_gen g gen ->
    graph_rep g |-- generation_rep g gen * (generation_rep g gen -* graph_rep g).
Proof.
  intros. unfold graph_rep. remember (nat_inc_list (length (g_gen (glabel g)))).
  apply iter_sepcon_ramif_stable_1. subst l. rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma gen_vertex_ramif_stable: forall g gen index,
    gen_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (nth_sh g gen) g (gen, index) *
    (vertex_rep (nth_sh g gen) g (gen, index) -* generation_rep g gen).
Proof.
  intros. unfold generation_rep. remember (nth_sh g gen) as sh.
  apply iter_sepcon_ramif_stable_1.
  change (gen, index) with ((fun x : nat => (gen, x)) index). apply in_map.
  rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma graph_vertex_ramif_stable: forall g v,
    graph_has_v g v ->
    graph_rep g |-- vertex_rep (nth_sh g (vgeneration v)) g v *
    (vertex_rep (nth_sh g (vgeneration v)) g v -* graph_rep g).
Proof.
  intros. destruct H. sep_apply (graph_gen_ramif_stable _ _ H).
  sep_apply (gen_vertex_ramif_stable _ _ _ H0). destruct v as [gen index].
  simpl. cancel. apply wand_frame_ver.
Qed.

Lemma heap_rest_rep_cut: forall (h: heap) i s (H1: 0 <= i < Zlength (spaces h))
                                (H2: has_space (Znth i (spaces h)) s),
    space_start (Znth i (spaces h)) <> nullval ->
    heap_rest_rep h =
    data_at_ (space_sh (Znth i (spaces h))) (tarray int_or_ptr_type s)
             (offset_val (WORD_SIZE * used_space (Znth i (spaces h)))
                         (space_start (Znth i (spaces h)))) *
    heap_rest_rep (cut_heap h i s H1 H2).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (split3_full_length_list
                0 i _ _ H1 (Zminus_0_l_reverse (Zlength (spaces h)))).
  replace (i - 0) with i in H0 by omega. simpl in *.
  remember (firstn (Z.to_nat i) (spaces h)) as l1.
  remember (skipn (Z.to_nat (i + 1)) (spaces h)) as l2.
  assert (Zlength l1 = i). {
    rewrite Zlength_length by omega. subst l1. apply firstn_length_le.
    rewrite Zlength_correct in H1. rep_omega. }
  rewrite H0 at 5. rewrite (upd_Znth_char _ _ _ _ _ H3).
  rewrite H0 at 1. rewrite !iter_sepcon_app_sepcon. simpl.
  remember (data_at_ (space_sh (Znth i (spaces h))) (tarray int_or_ptr_type s)
                     (offset_val (WORD_SIZE * used_space (Znth i (spaces h)))
                                 (space_start (Znth i (spaces h))))) as P.
  rewrite (sepcon_comm P), sepcon_assoc. f_equal.
  rewrite (sepcon_comm _ P), <- sepcon_assoc. f_equal.
  unfold space_rest_rep. simpl. do 2 rewrite if_false by assumption.
  red in H2. subst P. remember (Znth i (spaces h)) as sp.
  rewrite (data_at__tarray_value _ _ _ _ H2). rewrite offset_offset_val.
  replace (total_space sp - used_space sp - s) with
      (total_space sp - (used_space sp + s)) by omega.
  replace (WORD_SIZE * used_space sp + WORD_SIZE * s) with
      (WORD_SIZE * (used_space sp + s))%Z by rep_omega. reflexivity.
Qed.

Lemma data_at__singleton_array_eq:
  forall sh tp p, data_at_ sh (tarray tp 1) p = data_at_ sh tp p.
Proof.
  intros. rewrite data_at__tarray. simpl.
  rewrite data_at__eq, (data_at_singleton_array_eq _ _ (default_val tp)); reflexivity.
Qed.

Lemma field_compatible_int_or_ptr_tuint_iff: forall p,
    field_compatible int_or_ptr_type [] p <-> field_compatible tuint [] p.
Proof.
  intros. unfold field_compatible. simpl.
  intuition; unfold align_compatible in *; destruct p; try constructor; inv H2;
    inv H3; apply align_compatible_rec_by_value with (ch := Mint32); try reflexivity;
      simpl in *; assumption.
Qed.

Lemma data_at__int_or_ptr_tuint: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 1) p = data_at_ sh tuint p.
Proof.
  intros. rewrite data_at__singleton_array_eq, !data_at__memory_block,
          field_compatible_int_or_ptr_tuint_iff. reflexivity.
Qed.

Lemma lacv_generation_rep_not_eq: forall g v to n,
    n <> to -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) n = generation_rep g n.
Proof.
  intros. unfold generation_rep. rewrite lacv_nth_gen by assumption.
  apply iter_sepcon_func_strong. intros. apply list_in_map_inv in H3.
  destruct H3 as [m [? ?]]. unfold nth_sh. rewrite lacv_nth_gen by assumption.
  remember (generation_sh (nth_gen g n)) as sh. unfold vertex_rep. subst x.
  assert (graph_has_v g (n, m)). {
    rewrite nat_inc_list_In_iff in H4.
    destruct (Nat.lt_ge_cases n (length (g_gen (glabel g)))).
    - split; simpl; assumption.
    - exfalso. unfold nth_gen in H4. rewrite nth_overflow in H4 by assumption.
      simpl in H4. omega. } f_equal.
  - apply lacv_vertex_address_old; assumption.
  - apply lacv_make_header_old. intro S; inversion S. contradiction.
  - apply lacv_make_fields_vals_old; assumption.
Qed.

Lemma lacv_icgr_not_eq: forall l g v to,
    ~ In to l -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    iter_sepcon l (generation_rep (lgraph_add_copied_v g v to)) =
    iter_sepcon l (generation_rep g).
Proof.
  intros. induction l; simpl. 1: reflexivity. rewrite IHl.
  - f_equal. apply lacv_generation_rep_not_eq; [|assumption..].
    intro. apply H. left. assumption.
  - intro. apply H. right. assumption.
Qed.

Lemma lacv_generation_rep_eq: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) to =
    vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
              (make_header g v) (make_fields_vals g v) * generation_rep g to.
Proof.
  intros. unfold generation_rep. rewrite lacv_nth_sh by assumption.
  remember (number_of_vertices (nth_gen g to)).
  unfold lgraph_add_copied_v at 1. unfold nth_gen. simpl.
  rewrite cvmgil_eq by assumption. simpl. unfold nth_gen in Heqn. rewrite <- Heqn.
  rewrite nat_inc_list_app, map_app, iter_sepcon_app_sepcon, sepcon_comm.
  simpl nat_seq. change (nth to (g_gen (glabel g)) null_info) with
                     (nth_gen g to) in Heqn. f_equal.
  - simpl. normalize. replace (to, n) with (new_copied_v g to) by
        (unfold new_copied_v; subst n; reflexivity). unfold vertex_rep. f_equal.
    + apply lacv_vertex_address_new. assumption.
    + apply lacv_make_header_new.
    + apply lacv_make_fields_vals_new; assumption.
  - apply iter_sepcon_func_strong. intros. destruct x as [m x].
    apply list_in_map_inv in H3. destruct H3 as [? [? ?]]. inversion H3. subst x0.
    subst m. clear H3. remember (nth_sh g to) as sh. subst n.
    rewrite nat_inc_list_In_iff in H4. unfold vertex_rep.
    assert (graph_has_v g (to, x)) by (split; simpl; assumption).
    rewrite lacv_vertex_address_old, lacv_make_header_old, lacv_make_fields_vals_old;
      [reflexivity | try assumption..].
    unfold new_copied_v. intro. inversion H5. omega.
Qed.

Lemma copied_v_derives_new_g: forall g v to,
    graph_has_gen g to -> no_dangling_dst g -> copy_compatible g -> graph_has_v g v ->
    vertex_at (nth_sh g to) (vertex_address g (new_copied_v g to))
              (make_header g v) (make_fields_vals g v) *
    graph_rep g = graph_rep (lgraph_add_copied_v g v to).
Proof.
  intros. unfold graph_rep. unfold lgraph_add_copied_v at 1. simpl. red in H.
  rewrite cvmgil_length by assumption. remember (length (g_gen (glabel g))).
  assert (n = to + (n - to))%nat by omega. assert (0 < n - to)%nat by omega.
  remember (n - to)%nat as m. rewrite H3, nat_inc_list_app, !iter_sepcon_app_sepcon.
  rewrite (lacv_icgr_not_eq (nat_inc_list to) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_inc_list_In_iff in H5; omega.
  rewrite sepcon_comm, sepcon_assoc. f_equal. assert (m = 1 + (m - 1))%nat by omega.
  rewrite H5, nat_seq_app, !iter_sepcon_app_sepcon.
  assert (nat_seq to 1 = [to]) by reflexivity. rewrite H6. clear H6.
  rewrite (lacv_icgr_not_eq (nat_seq (to + 1) (m - 1)) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_seq_In_iff in H6; omega.
  rewrite sepcon_assoc, sepcon_comm, sepcon_assoc, sepcon_comm. f_equal.
  simpl iter_sepcon. normalize. clear m Heqm H3 H4 H5. subst n.
  rewrite <- lacv_generation_rep_eq; [reflexivity | assumption..].
Qed.

Lemma data_at_tarray_value_split_1: forall sh p (l: list val),
    0 < Zlength l ->
    data_at sh (tarray int_or_ptr_type (Zlength l)) l p =
    data_at sh int_or_ptr_type (hd nullval l) p *
    data_at sh (tarray int_or_ptr_type (Zlength l-1)) (tl l) (offset_val WORD_SIZE p).
Proof.
  intros. rewrite (data_at_tarray_value sh (Zlength l) 1 p l l [hd nullval l] (tl l)).
  - replace (WORD_SIZE * 1)%Z with WORD_SIZE by omega. f_equal.
    rewrite (data_at_singleton_array_eq _ int_or_ptr_type (hd nullval l)); reflexivity.
  - omega.
  - omega.
  - autorewrite with sublist; reflexivity.
  - destruct l. 1: rewrite Zlength_nil in H; omega. simpl. compute. reflexivity.
  - destruct l. 1: rewrite Zlength_nil in H; omega. simpl.
    rewrite sublist_1_cons, Zlength_cons.
    replace (Z.succ (Zlength l) - 1) with (Zlength l) by omega.
    autorewrite with sublist. reflexivity.
Qed.

Lemma mark_copied_vertex_rep: forall sh g v new_v,
    vertex_rep sh (lgraph_mark_copied g v new_v) v =
    data_at sh tuint (Vint (Int.repr 0))
            (offset_val (- WORD_SIZE) (vertex_address g v)) *
    data_at sh int_or_ptr_type (vertex_address g new_v)
             (vertex_address g v) *
    data_at sh (tarray int_or_ptr_type (Zlength (make_fields_vals g v) - 1))
            (tl (make_fields_vals g v)) (offset_val WORD_SIZE (vertex_address g v)).
Proof.
  intros. unfold vertex_rep. rewrite lmc_vertex_address. unfold vertex_at.
  rewrite sepcon_assoc. f_equal.
  - f_equal. unfold make_header. simpl vlabel at 1.
    unfold update_copied_old_vlabel, graph_gen.update_vlabel.
    rewrite if_true by reflexivity. simpl. unfold Z2val. reflexivity.
  - rewrite lmc_make_fields_vals_new, data_at_tarray_value_split_1.
    + simpl hd. f_equal. simpl tl.
      replace (Zlength (vertex_address g new_v :: tl (make_fields_vals g v)) - 1)
        with (Zlength (make_fields_vals g v) - 1). 1: reflexivity.
      transitivity (Zlength (tl (make_fields_vals g v))).
      2: rewrite Zlength_cons; rep_omega.
      assert (0 < Zlength (make_fields_vals g v)) by
          (rewrite fields_eq_length; apply (proj1 (raw_fields_range (vlabel g v)))).
      remember (make_fields_vals g v). destruct l.
      1: rewrite Zlength_nil in H; omega. rewrite Zlength_cons. simpl. omega.
    + rewrite Zlength_cons. rep_omega.
Qed.

Lemma graph_vertex_lmc_ramif: forall g v new_v,
    graph_rep g |-- vertex_rep (nth_sh g (vgeneration v)) g v *
    (vertex_rep (nth_sh g (vgeneration v))
                (lgraph_mark_copied g v new_v) v -*
                graph_rep (lgraph_mark_copied g v new_v)).
Proof.
  intros.
Abort.
