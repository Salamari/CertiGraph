Require Import RamifyCoq.CertiGC.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep. destruct (Val.eq (ti_heap_p t_info) nullval).
  1: hnf in e; exfalso; tauto. clear n. Intros. unfold heap_struct_rep. forward. 
  unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by unfold fun_info_rep; entailer!.
  forward_if True; [forward; entailer!|exfalso; destruct t_info; simpl in *; tauto|].
  Intros. remember (ti_heap_p t_info) as h. remember (ti_heap t_info) as th.
  assert_PROP (isptr (space_start (heap_head th))). {
    destruct H as [? [? ?]]. rewrite <- Heqh in *. rewrite <- Heqth in *.
    unfold graph_rep. remember (glabel g) as ginfo. destruct ginfo.
    1: exfalso; apply H1; rewrite <- H; reflexivity. simpl in * |-.
    pose proof (spaces_size th). remember (spaces th). destruct l. 1: inversion H4.
    rewrite map_cons in H3. rewrite Forall_forall in H2. simpl in H2.
    assert (generation_space_compatible g (O, g0, s)) by (apply H2; left; reflexivity).
    destruct H5 as [? [? ?]]. pose proof (start_isptr g0). rewrite H5 in H8.
    entailer!. assert (heap_head (ti_heap t_info) = s). {
      destruct (ti_heap t_info) eqn:? . simpl in Heql. unfold heap_head. simpl.
      destruct spaces; inversion Heql. reflexivity.
    } rewrite H17. assumption.
  } forward. rewrite Znth_0_cons. forward. rewrite Znth_0_cons. forward_if True.
  - remember (space_start (heap_head (ti_heap t_info))).
    destruct v0; try (simpl in Heqv0; exfalso; assumption). unfold denote_tc_samebase.
    simpl. entailer!.
  - unfold all_string_constants. Intros.
    forward_call ((gv ___stringlit_10),
                  (map init_data2byte (gvar_init v___stringlit_10)), rsh).
    exfalso; assumption.
  - simpl in H3. remember (space_start (heap_head th)).
    destruct v; try (simpl in Heqv; exfalso; assumption). simpl in H3.
    if_tac in H3. 2: exfalso; apply H4; reflexivity.
    forward. entailer!.
  - forward. forward.
    
Abort.
