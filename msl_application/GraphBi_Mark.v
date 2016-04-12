Require Import RamifyCoq.lib.Ensembles_ext.
Require Import Coq.Lists.List.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.Coqlib2.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.relation_list.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.msl_ext.iter_sepcon.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.dag.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.Graph_Mark.
Require Import RamifyCoq.msl_application.GraphBi.
Require Import Coq.Logic.Classical.
Import RamifyCoq.msl_ext.seplog.OconNotation.

Open Scope logic.

Section SpatialGraph_Mark_Bi.

Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
Context {sSGG_Bi: sSpatialGraph_Graph_Bi bool unit}.

Local Coercion Graph_LGraph: Graph >-> LGraph.
Local Coercion LGraph_SGraph: LGraph >-> SGraph.
Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Notation Graph := (@Graph pSGG_Bi bool unit).

(* TODO: move this lemma into Graph_Mark.v. *)
Lemma vlabel_eq: forall (g1 g2: Graph) x1 x2, (WeakMarkGraph.marked g1 x1 <-> WeakMarkGraph.marked g2 x2) -> vlabel g1 x1 = vlabel g2 x2.
Proof.
  intros.
  simpl in H.
  destruct H.
  destruct (vlabel g1 x1), (vlabel g2 x2); try congruence.
  + tauto.
  + symmetry; tauto.
Qed.

Lemma mark_null_refl: forall (g: Graph), mark null g g.
Proof. intros. apply mark_invalid_refl, invalid_null. Qed.

Lemma mark_vgamma_true_refl: forall (g: Graph) root d l r, vgamma g root = (d, l, r) -> d = true -> mark root g g.
Proof.
  intros.
  apply mark_marked_root_refl.
  inversion H.
  simpl; congruence.
Qed.

Lemma Graph_gen_true_mark1: forall (G: Graph) (x: addr) l r,
  vgamma G x = (false, l, r) ->
  vvalid G x ->
  mark1 x (G: LabeledGraph _ _ _ _) (Graph_gen G x true: LabeledGraph _ _ _ _).
Proof.
  intros.
  split; [| split; [| split]].
  + reflexivity.
  + simpl.
    unfold update_vlabel.
    destruct_eq_dec x x; congruence.
  + intros.
    simpl.
    unfold update_vlabel; simpl.
    destruct_eq_dec x n'; [congruence |].
    simpl in H2.
    auto.
  + intros.
    simpl in H2 |- *.
    unfold update_vlabel in H2; simpl in H2.
    destruct_eq_dec x n'; [congruence |].
    auto.
Qed.

Lemma left_weak_valid: forall (G G1: Graph) (x l r: addr),
  vgamma G x = (false, l, r) ->
  vvalid G x ->
  mark1 x G G1 ->
  @weak_valid _ _ _ _ G1 (maGraph _) l.
Proof.
  intros.
  destruct H1 as [? _].
  eapply weak_valid_si; [symmetry; exact H1 |].
  eapply gamma_left_weak_valid; eauto.
Qed.

Lemma right_weak_valid: forall (G G1 G2: Graph) (x l r: addr),
  vgamma G x = (false, l, r) ->
  vvalid G x ->
  mark1 x G G1 ->
  mark l G1 G2 ->
  @weak_valid _ _ _ _ G2 (maGraph _) r.
Proof.
  intros.
  destruct H1 as [? _].
  destruct H2 as [_ ?].
  eapply weak_valid_si; [symmetry; transitivity G1; [exact H1 | exact H2] |].
  eapply gamma_right_weak_valid; eauto.
Qed.

(* TODO: resume gx in all 4 files. *)
Lemma root_stable_ramify: forall (g: Graph) (x: addr),
  vvalid g x ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x (vgamma g x) *
      (vertex_at x (vgamma g x) -* reachable_vertices_at x g)).
Proof. intros; apply va_reachable_root_stable_ramify; auto. Qed.

Lemma root_update_ramify: forall (g: Graph) (x: addr) (lx: bool),
  vvalid g x ->
  @derives pred _
    (reachable_vertices_at x g)
    (vertex_at x (vgamma g x) *
      (vertex_at x (vgamma (Graph_gen g x lx) x) -* reachable_vertices_at x (Graph_gen g x lx))).
Proof. intros; apply va_reachable_root_update_ramify; auto. Qed.

Lemma graph_ramify_left: forall {RamUnit: Type} (g g1: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  @derives pred _
    (reachable_vertices_at x g1)
    (reachable_vertices_at l g1 *
      (ALL a: RamUnit * Graph,
        !! (mark l g1 (snd a)) -->
        (reachable_vertices_at l (snd a) -* reachable_vertices_at x (snd a)))).
Proof.
  intros.
  apply (mark_list_mark_ramify g g1 _ _ nil _ (r :: nil)); auto.
  + admit.
  + simpl.
    eapply gamma_step_list; eauto.
  + split_relation_list ((lg_gg g1) :: nil); auto.
    reflexivity.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H2; destruct H2.
    apply reachable_foot_valid in H2; auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H3; destruct H3.
    apply reachable_foot_valid in H3.
    destruct H2 as [_ [? _]].
    rewrite <- H2; auto.
Qed.

Lemma graph_ramify_right: forall {RamUnit: Type} (g g1 g2: Graph) x l r,
  vvalid g x ->
  vgamma g x = (false, l, r) ->
  mark1 x g g1 ->
  mark l g1 g2 ->
  (reachable_vertices_at x g2: pred) |-- reachable_vertices_at r g2 *
   (ALL a: RamUnit * Graph,
     !! (mark r g2 (snd a)) -->
     (reachable_vertices_at r (snd a) -* reachable_vertices_at x (snd a))).
Proof.
  intros.
  apply (mark_list_mark_ramify g g2 _ _ (l :: nil) _ nil); auto.
  + admit.
  + simpl.
    eapply gamma_step_list; eauto.
  + split_relation_list ((lg_gg g1) :: nil); auto.
    unfold mark_list. simpl map.
    split_relation_list (@nil (LabeledGraph _ _ bool unit)); auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H3; destruct H3.
    apply reachable_foot_valid in H3; auto.
  + unfold Included, Ensembles.In; intros.
    apply vvalid_vguard.
    rewrite Intersection_spec in H4; destruct H4.
    apply reachable_foot_valid in H4.
    destruct H3 as [_ [? _]].
    rewrite <- H3; auto.
Qed.

Lemma mark1_mark_left_mark_right: forall (g1 g2 g3 g4: Graph) root l r,
  vvalid g1 root ->
  vgamma g1 root = (false, l, r) ->
  mark1 root g1 g2 ->
  mark l g2 g3 ->
  mark r g3 g4 ->
  mark root g1 g4.
Proof.
  intros.
  apply (mark1_mark_list_mark root (l :: r :: nil)); auto.
  + intros; simpl.
    inversion H0.
    unfold Complement, Ensembles.In.
    rewrite H5; congruence.
  + hnf; intros.
    apply gamma_step with (y := n') in H0; auto.
    rewrite H0; simpl.
    pose proof eq_sym_iff n' l.
    pose proof eq_sym_iff n' r.
    tauto.
  + split_relation_list ((lg_gg g2) :: nil); eauto.
    unfold mark_list.
    simpl map.
    split_relation_list ((lg_gg g3) :: nil); eauto.
Qed.

End SpatialGraph_Mark_Bi.


