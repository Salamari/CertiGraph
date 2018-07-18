Require Import RamifyCoq.CertiGC.gc_spec.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by omega.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - rewrite Forall_forall in H1. rewrite (filter_sum_right_In_iff v roots) in H.
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
    isptr p ->
    (force_val
       (sem_add_ptr_int
          (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |})
          Signed (offset_val (WORD_SIZE * m) p)
          (vint n))) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. rewrite sem_add_pi_ptr_special.
  - simpl. rewrite offset_offset_val. f_equal. rep_omega.
  - rewrite isptr_offset_val. assumption.
Qed.
  
Lemma data_at__int_or_ptr_tuint: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 1) p |-- data_at_ sh tuint p.
Proof.
  intros. rewrite data_at__singleton_array_eq, !data_at__memory_block. Intros.
  apply andp_right. 2: simpl sizeof; cancel.
  apply prop_right. red in H. red. simpl in *. intuition. red. red in H2.
  destruct p; try contradiction. inversion H2. subst. simpl in H3. inversion H3. subst.
  simpl in H5. apply align_compatible_rec_by_value with (ch := Mint32). 1: reflexivity.
  simpl. assumption.
Qed.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
  unfold forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros.
    assert (Zlength roots = Zlength (live_roots_indices f_info)). {
      rewrite <- (Zlength_map _ _ (flip Znth (ti_args t_info))), <- H3, Zlength_map.
      reflexivity. }
    pose proof (Znth_map _ (root2val g) _ H0). hnf in H0. rewrite H10 in H0.
    rewrite H3, Znth_map in H11 by assumption. unfold flip in H11.
    remember (Znth z roots) as root. rewrite <- H10 in H0. pose proof (Znth_In _ _ H0).
    rewrite <- Heqroot in H12. rewrite H10 in H0. unfold Inhabitant_val in H11.
    assert (forall v, In (inr v) roots -> isptr (vertex_address g v)). {
      intros. destruct H4. unfold vertex_address. rewrite Forall_forall in H14.
      rewrite (filter_sum_right_In_iff v roots) in H13. apply H14 in H13.
      destruct H13. apply graph_has_gen_start_isptr in H13.
      remember (gen_start g (vgeneration v)) as vv. destruct vv; try contradiction.
      simpl. exact I. }
    assert (is_pointer_or_integer (root2val g root)). {
      destruct root as [[? | ?] | ?]; simpl; auto.
      - destruct g0. simpl. exact I.
      - specialize (H13 _ H12). apply isptr_is_pointer_or_integer. assumption. }
    assert (0 <= Znth z (live_roots_indices f_info) < 1024) by
        (apply (fi_index_range f_info), Znth_In; assumption).
    forward; rewrite H11. 1: entailer!.
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP 3 2. sep_apply (root_valid_int_or_ptr _ _ _ _ H12 H4). entailer!. }
    forward_call (root2val g root).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
      as P. pose proof (graph_and_heap_rest_data_at_ _ _ _ H6 H).
    unfold generation_data_at_ in H17. remember (gen_start g from) as fp.
    remember (nth_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H17.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (total_space_tight_range (nth_space t_info from)). assumption. }
    destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. apply semax_if_seq. forward_if.
      1: exfalso; apply H19'; reflexivity.
      forward. Exists g t_info roots. rewrite <- Heqroot. entailer!.
      * simpl. split; [constructor | hnf; intuition].
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H19; assumption.
      forward_call (Vptr b i). gather_SEP 3 6 2. rewrite <- sepcon_assoc.
      rewrite <- HeqP. destruct H4.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H18. Intros. simpl root2val in *.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst. cancel. apply andp_right. 2: cancel.
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak.
        sep_apply (outlier_rep_valid_pointer roots outlier (GCPtr b i) H12 H4).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H18.
      forward_call (fsh, fp, fn, (Vptr b i), P). Intros v. destruct v.
      * rewrite HeqP. Intros. gather_SEP 0 1. sep_apply H17. rewrite Heqfn in v.
        sep_apply (outlier_rep_single_rep _ _ _ H12 H4). Intros. gather_SEP 0 2.
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
        pose proof (generation_share_writable (nth_gen g from)).
        change (generation_sh (nth_gen g from)) with (nth_sh g from) in H18.
        rewrite <- Heqfsh in H18. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H18 v).
        assert_PROP False by entailer!. contradiction.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H18'; reflexivity.
        forward. Exists g t_info roots. rewrite <- Heqroot. entailer!.
        -- split; [|split].
           ++ unfold roots_compatible. split; assumption.
           ++ simpl; constructor.
           ++ hnf; intuition.
        -- unfold thread_info_rep. entailer!.
    + specialize (H13 _ H12). destruct (vertex_address g v) eqn:? ; try contradiction.
      apply semax_if_seq. forward_if.
      2: exfalso; apply Int.one_not_zero in H19; assumption.
      clear H19 H19'. simpl in H14, H16. forward_call (Vptr b i).
      rewrite <- Heqv0 in *. gather_SEP 3 6 2. rewrite <- sepcon_assoc, <- HeqP.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H18. Intros. assert (graph_has_v g v). {
        destruct H4. rewrite Forall_forall in H18. apply H18.
        rewrite <- filter_sum_right_In_iff. assumption. }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst. sep_apply (graph_rep_vertex_rep g v H18).
        Intros shh. unfold vertex_rep, vertex_at. remember (make_fields_vals g v).
        sep_apply (data_at_valid_ptr shh (tarray int_or_ptr_type (Zlength l)) l
                                     (vertex_address g v)).
        - apply readable_nonidentity, writable_readable_share. assumption.
        - subst l. simpl. rewrite fields_eq_length.
          rewrite Z.max_r; pose proof (raw_fields_range (vlabel g v)); omega.
        - rewrite Heqv0; cancel. }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by (entailer; assumption). clear H19. Intros. rewrite <- Heqv0 in *.
      forward_call (fsh, fp, fn, (vertex_address g v), P). Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H6 H18). Intros.
      rewrite <- Heqfp, <- Heqgn, <- Heqfn in H19. destruct vv.
      * Intros. rewrite H19 in v0. clear H19. apply semax_if_seq. forward_if.
        2: exfalso; inversion H19. deadvars!. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H19 H19'. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (nth_sh g from)) by
            (unfold nth_sh; apply writable_readable, generation_share_writable).
        assert_PROP (force_val
                       (sem_add_ptr_int tuint Signed (vertex_address g v)
                                        (eval_unop Oneg tint (vint 1))) =
                     field_address tuint []
                                   (offset_val (- WORD_SIZE) (vertex_address g v))). {
          rewrite WORD_SIZE_eq. entailer!. unfold field_address.
          rewrite if_true by assumption. simpl. rewrite offset_offset_val.
          reflexivity. } forward.
        gather_SEP 0 1. replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v) by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H18).
        apply semax_if_seq. forward_if; rewrite make_header_int_rep_mark_iff in H21.
        -- deadvars!. localize [vertex_rep (nth_sh g (vgeneration v)) g v].
           rewrite v0. unfold vertex_rep, vertex_at. Intros.
           unfold make_fields_vals at 2. rewrite H21.
           assert (0 <= 0 < Zlength (make_fields_vals g v)). {
             split. 1: omega. rewrite fields_eq_length.
             apply (proj1 (raw_fields_range (vlabel g v))). }
           assert (is_pointer_or_integer
                     (vertex_address g (copied_vertex (vlabel g v)))). {
             apply isptr_is_pointer_or_integer. unfold vertex_address.
             rewrite isptr_offset_val.
             apply graph_has_gen_start_isptr, H8; assumption. }
           forward. rewrite Znth_0_cons. gather_SEP 0 1.
           replace_SEP 0 (vertex_rep (nth_sh g (vgeneration v)) g v). {
             unfold vertex_rep, vertex_at. unfold make_fields_vals at 3.
             rewrite H21. entailer!. }
           unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H18).
           thaw FR. forward. forward. rewrite <- Heqroot.
           rewrite if_true by reflexivity. rewrite H21.
           Exists g (upd_thread_info_arg
                       t_info
                       (Znth z (live_roots_indices f_info))
                       (vertex_address g (copied_vertex (vlabel g v))) H15)
                  (upd_bunch z f_info roots (inr (copied_vertex (vlabel g v)))).
           unfold thread_info_rep. simpl. entailer!. split; split.
           ++ apply upd_fun_thread_arg_compatible. assumption.
           ++ specialize (H8 _ H18 H21).
              apply upd_roots_compatible; assumption.
           ++ apply fr_v_in_forwarded; [reflexivity | assumption].
           ++ hnf. intuition.
        -- forward. thaw FR. freeze [0; 1; 2; 3; 4; 5] FR.
           rewrite make_header_Wosize by (apply not_true_is_false; assumption).
           assert (0 <= Z.of_nat to < 12). {
             clear -H H7. destruct H as [_ [_ ?]]. red in H7.
             pose proof (spaces_size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_omega. }
           assert (0 < Z.of_nat to) by omega. unfold heap_struct_rep.
           remember (Znth (Z.of_nat to) (spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_start sp_to)). {
             destruct (gt_gs_compatible _ _ H _ H7) as [? _]. subst sp_to.
             rewrite nth_space_Znth in H24. rewrite <- H24. apply start_isptr. }
           remember ((space_start (heap_head (ti_heap t_info)),
                      (Vundef,
                       offset_val
                         (WORD_SIZE * total_space (heap_head (ti_heap t_info)))
                         (space_start (heap_head (ti_heap t_info)))))
                       :: map space_tri (tl (spaces (ti_heap t_info)))).
           assert (Znth (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_pos_cons by assumption.
             rewrite map_tl, Znth_tl by omega.
             replace (Z.of_nat to - 1 + 1) with (Z.of_nat to) by omega.
             rewrite Znth_map by (rewrite spaces_size; rep_omega). reflexivity. }
           unfold Inhabitant_pair, Inhabitant_val, Inhabitant in H25.
           forward; rewrite H25; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val by assumption. Opaque Znth. forward. Transparent Znth.
           rewrite sapi_ptr_val by assumption. rewrite H25. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (raw_fields (vlabel g v))) with (vertex_size g v) by
               (unfold vertex_size; omega). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (spaces (ti_heap t_info))) by
               (rewrite spaces_size; rep_omega).
           assert (Hh: has_space (Znth (Z.of_nat to) (spaces (ti_heap t_info)))
                                 (vertex_size g v)). {
             red. split. 1: pose proof (svs_gt_one g v); omega.
             transitivity (unmarked_gen_size g (vgeneration v)).
             - apply single_unmarked_le; [|apply not_true_is_false]; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_start (Znth (Z.of_nat to) (spaces (ti_heap t_info))) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_start sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      (ti_heap t_info) (Z.of_nat to) (vertex_size g v) Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR. gather_SEP 4 5 7.
           replace_SEP 0 (thread_info_rep sh (cut_thread_info t_info _ _ Hi Hh) ti).
           ++ entailer. unfold thread_info_rep. simpl ti_heap. cancel.
              rewrite heap_head_cut_thread_info by omega. cancel.
              rewrite upd_Znth_cons by omega. rewrite !map_tl. unfold cut_heap.
              simpl spaces. rewrite <- upd_Znth_map. unfold cut_space.
              unfold space_tri at 3. simpl total_space. simpl space_start.
              simpl used_space. rewrite <- upd_Znth_tl. 2: omega. 2: {
                intro Hs. apply map_eq_nil in Hs.
                apply (heap_spaces_nil (ti_heap t_info)). rewrite Hs. reflexivity. }
              replace (Z.of_nat to - 1 + 1) with (Z.of_nat to) by omega.
              unfold cut_thread_info, heap_struct_rep. simpl ti_heap_p. entailer!.
           ++ sep_apply (graph_vertex_ramif_stable _ _ H18). Intros.
              freeze [1; 2; 3; 4; 5] FR. deadvars!. rewrite v0.
              remember (nth_sh g from) as shv.
              assert (writable_share (space_sh sp_to)). {
                destruct (gt_gs_compatible _ _ H _ H7) as [_ [? _]]. subst sp_to.
                rewrite nth_space_Znth in H26. rewrite <- H26.
                apply generation_share_writable. }
              remember (space_sh sp_to) as sht.
              rewrite (data_at__tarray_value _ _ 1). 2: unfold vertex_size; rep_omega.
              Intros.
              remember (offset_val (WORD_SIZE * used_space sp_to) (space_start sp_to)).
              sep_apply (data_at__int_or_ptr_tuint sht v1).
              assert_PROP
                (force_val (sem_add_ptr_int
                              tuint Signed
                              (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                          (space_start sp_to))
                              (eval_unop Oneg tint (vint 1))) =
                 field_address tuint [] v1). {
                subst v1. rewrite WORD_SIZE_eq. entailer!. unfold field_address.
                rewrite if_true by assumption. simpl. rewrite offset_offset_val.
                f_equal. omega. }
              forward. sep_apply (field_at_data_at_cancel
                                    sht tuint (Z2val (make_header g v)) v1).
              subst v1. rewrite offset_offset_val.
              replace (vertex_size g v - 1) with (Zlength (raw_fields (vlabel g v)))
                by (unfold vertex_size; omega).
              replace (WORD_SIZE * used_space sp_to + WORD_SIZE * 1) with
                  (WORD_SIZE * (used_space sp_to + 1))%Z by rep_omega.
              remember (offset_val (WORD_SIZE * (used_space sp_to + 1))
                                   (space_start sp_to)) as nv.
              thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j. deadvars!.
              remember (Zlength (raw_fields (vlabel g v))) as n.
              assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
              forward_for_simple_bound
                n
                (EX i: Z,
                 PROP ( )
                 LOCAL (temp _new nv;
                        temp _sz (vint n);
                        temp _v (vertex_address g v))
                 SEP (vertex_rep shv g v;
                      data_at sht (tarray int_or_ptr_type i)
                              (sublist 0 i (make_fields_vals g v)) nv;
                      data_at_ sht (tarray int_or_ptr_type (n - i))
                               (offset_val (WORD_SIZE * i) nv);
                      FRZL FR))%assert.
              ** pose proof (raw_fields_range (vlabel g v)). subst n.
                 transitivity (two_power_nat 22). 1: omega.
                 compute; intro s; inversion s.
              ** rewrite sublist_nil. replace (n - 0) with n by omega.
                 replace (WORD_SIZE * 0)%Z with 0 by omega.
                 rewrite isptr_offset_val_zero by assumption.
                 rewrite data_at_zero_array_eq;
                   [|reflexivity | assumption | reflexivity]. entailer!.
              ** unfold vertex_rep, vertex_at. Intros.
                 rewrite fields_eq_length, <- Heqn. forward.
                 --- entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H8 H9 H18).
                     rewrite Forall_forall in H40. apply H40, Znth_In.
                     rewrite fields_eq_length. assumption.
                 --- rewrite (data_at__tarray_value _ _ 1) by omega. Intros.
                     rewrite data_at__singleton_array_eq.
                     assert_PROP
                       (force_val
                          (sem_add_ptr_int int_or_ptr_type Signed nv (vint i)) =
                        field_address int_or_ptr_type []
                                      (offset_val (WORD_SIZE * i) nv)). {
                       assert_PROP
                         (field_compatible int_or_ptr_type []
                                           (offset_val (WORD_SIZE * i) nv)) by
                           (sep_apply (data_at__local_facts
                                        sht int_or_ptr_type
                                        (offset_val (WORD_SIZE * i) nv)); entailer!).
                       unfold field_address. rewrite if_true by assumption.
                       entailer!. }
                     gather_SEP 0 1. replace_SEP 0 (vertex_rep shv g v) by
                         (unfold vertex_rep, vertex_at;
                          rewrite fields_eq_length; entailer!). forward.
                     rewrite offset_offset_val.
                     replace (n - i - 1) with (n - (i + 1)) by omega.
                     replace (WORD_SIZE * i + WORD_SIZE * 1) with
                         (WORD_SIZE * (i + 1))%Z by rep_omega.
                     admit.
              ** admit.
      * apply semax_if_seq. forward_if. 1: exfalso; apply H20'; reflexivity.
        rewrite H19 in n. forward. rewrite <- Heqroot. rewrite if_false by assumption.
        Exists g t_info roots. simpl. entailer!.
        -- split; [constructor; assumption | hnf; intuition].
        -- unfold thread_info_rep. entailer!.
Abort.
