(*Described a pure undirected graph that can be represented by an adjacency matrix*)
Require Import CertiGraph.lib.EnumEnsembles.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import CertiGraph.lib.Coqlib.
Require Import CertiGraph.lib.EquivDec_ext.
Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Import CertiGraph.graph.graph_gen.
Require Import CertiGraph.graph.graph_relation.
Require Import CertiGraph.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import CertiGraph.graph.undirected_graph.
Require Import CertiGraph.graph.AdjMatGraph.
Require Import CertiGraph.priq.priq_arr_utils.

Local Open Scope logic.
Local Open Scope Z_scope.

(*Move this*)
Lemma Permutation_Zlength:
  forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Lemma incl_nil:
forall {A: Type} (l: list A), incl l nil -> l = nil.
Proof.
induction l; intros. auto. assert (In a nil). apply H. left; auto. contradiction.
Qed.

Section MATRIXUGRAPH.

Instance V_EqDec: EqDec V eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec E eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec z z0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Context {inf: Z} {size: Z}.

(* I suggest using AdjMat's soundess and adding 
   your further restrictions to it.
   See MathDijkGraph for an example 
 *)
Class AdjMatUSoundness (g: LabeledGraph V E DV DE DG) := {
  size_rep: 0 <= size <= Int.max_signed;
  inf_rep: 0 <= inf <= Int.max_signed; 
  vert_representable: forall v, vvalid g v <-> 0 <= v < size;
  (* so essentially evalid and strong_evalid have been collapsed *)
  edge_strong_evalid: forall e, evalid g e -> vvalid g (src g e) /\ vvalid g (dst g e);
  edge_weight_representable: forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed;
  edge_weight_not_inf: forall e, evalid g e -> elabel g e < inf; (*no reason to have <>*)
  invalid_edge_weight: forall e, ~ evalid g e -> elabel g e = inf;
  src_fst: forall e, evalid g e -> src g e = fst e;
  dst_snd: forall e, evalid g e -> dst g e = snd e;
  fin: FiniteGraph g;
  undirected_edge_rep: forall e, evalid g e -> src g e <= dst g e;
}.

(*Hm, was wondering if I could incorporate "soundness" in*)
(* done? *)
Definition MatrixUGraph := (GeneralGraph V E DV DE DG (fun g => AdjMatUSoundness g)).


Definition sound_MatrixUGraph (g: MatrixUGraph) := (@sound_gg _ _ _ _ _ _ _ _ g).

(* There is already a whole set of such getters in
   AdjMatGraph. I suggest just using those.
   Add more getters for any custom restictions
   you place. If your lemmas are provable
   from AdjMat's soundless, you can move them up 
   to that file.
 *)
Instance Finite_MatrixUPGraph (g: MatrixUGraph): FiniteGraph g.
Proof. apply (@fin g (sound_MatrixUGraph g)). Qed.

Lemma vert_bound:
forall (g: MatrixUGraph) v, vvalid g v <-> 0 <= v < size.
Proof.
intros. apply (@vert_representable g (sound_MatrixUGraph g)).
Qed.

Lemma MatrixUGraph_VList:
forall (g: MatrixUGraph), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
intros. rewrite VList_vvalid. rewrite vert_bound.
rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
Qed.

Lemma evalid_form: (*useful for a = (u,v) etc*)
forall (g: MatrixUGraph) e, evalid g e -> e = (src g e, dst g e).
Proof.
intros. rewrite (@src_fst _ (sound_MatrixUGraph g) e) by auto.
rewrite (@dst_snd _ (sound_MatrixUGraph g) e) by auto.
destruct e; simpl; auto.
Qed.

Lemma evalid_strong_evalid:
forall (g: MatrixUGraph) e, evalid g e -> strong_evalid g e.
Proof.
intros; split. auto. apply (@edge_strong_evalid _ (sound_MatrixUGraph g) e); auto.
Qed.

Lemma evalid_vvalid:
forall (g: MatrixUGraph) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply evalid_strong_evalid in H. destruct H.
rewrite (@src_fst _ (sound_MatrixUGraph _)), (@dst_snd _ (sound_MatrixUGraph _)) in H0 by auto.
simpl in H0; auto.
Qed.

Lemma evalid_adjacent:
forall (g: MatrixUGraph) u v, evalid g (u,v) -> adjacent g u v.
Proof.
intros. exists (u,v); split. apply evalid_strong_evalid; auto.
rewrite (@src_fst _ (sound_MatrixUGraph _)), (@dst_snd _ (sound_MatrixUGraph _)) by auto.
left; simpl; auto.
Qed.

Lemma evalid_inf_iff:
forall (g: MatrixUGraph) e, evalid g e <-> elabel g e < inf.
Proof.
intros; split; intros. apply (@edge_weight_not_inf _ (sound_MatrixUGraph g)); auto.
destruct (evalid_dec g e). auto. apply (@invalid_edge_weight _ (sound_MatrixUGraph g)) in n. lia.
Qed.

Lemma weight_representable:
forall (g: MatrixUGraph) e, Int.min_signed <= elabel g e <= Int.max_signed.
Proof.
intros. destruct (evalid_dec g e).
apply (@edge_weight_representable g (sound_MatrixUGraph g) e). auto.
apply (@invalid_edge_weight g (sound_MatrixUGraph g) e) in n. rewrite n.
pose proof (@inf_rep g (sound_MatrixUGraph g)). split.
set (i:=Int.min_signed); compute in i; subst i. lia.
apply H.
Qed.

Lemma weight_inf_bound:
forall (g: MatrixUGraph) e, elabel g e <= inf.
Proof.
intros. destruct (evalid_dec g e).
apply Z.lt_le_incl. apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e). auto.
apply (@invalid_edge_weight g (sound_MatrixUGraph g)) in n. lia.
Qed.

Lemma adj_edge_form:
forall (g: MatrixUGraph) u v a b, adj_edge g (u,v) a b -> a <= b -> (u = a /\ v = b).
Proof.
intros. destruct H. assert (src g (u,v) <= dst g (u,v)).
apply (@undirected_edge_rep g (sound_MatrixUGraph g)). apply H.
rewrite (@src_fst g (sound_MatrixUGraph g)), (@dst_snd g (sound_MatrixUGraph g)) in *.
simpl in *. destruct H1. auto. destruct H1; subst u; subst v. lia.
all: apply H.
Qed.

(****************Edgeless graph again*****************)

Section EDGELESS_MUGRAPH.

Context {inf_bound: 0 <= inf <= Int.max_signed}.
Context {size_bound: 0 <= size <= Int.max_signed}.

Definition edgeless_lgraph: LabeledGraph V E DV DE DG :=
@Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG
  (@Build_PreGraph V E V_EqDec E_EqDec (fun v => 0 <= v < size) (fun e => False) fst snd)
  (fun v => tt) (fun e => inf) tt. (*<--- different from edgeless_WEdgeGraph because of the default value*)

Instance AdjMatUSound_edgeless:
  AdjMatUSoundness edgeless_lgraph.
Proof.
constructor.
all: simpl; intros; try contradiction.
+lia.
+lia.
+lia.
+auto.
+constructor; unfold EnumEnsembles.Enumerable.
(*vertices*)
exists (nat_inc_list (Z.to_nat size)); split. apply nat_inc_list_NoDup.
simpl. intros. rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by lia. split; intros; lia.
destruct H. rewrite H. unfold Z.max; simpl. split; lia.
rewrite Z.max_l by lia. split; auto.
(*edges*)
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_graph: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    edgeless_lgraph (AdjMatUSound_edgeless).

Lemma edgeless_graph_vvalid:
  forall k, vvalid edgeless_graph k <-> 0 <= k < size.
Proof. simpl. intros; split; intros; auto. Qed.

Lemma edgeless_graph_evalid:
  forall e, ~ evalid edgeless_graph e.
Proof.
intros. unfold edgeless_graph; simpl. auto.
Qed.

Lemma edgeless_graph_EList:
  EList edgeless_graph = nil.
Proof.
  intros. unfold edgeless_graph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Lemma edgeless_partial_lgraph:
  forall (g: MatrixUGraph), is_partial_lgraph edgeless_graph g.
Proof.
intros. split. unfold is_partial_graph.
split. intros. simpl. simpl in H. rewrite vert_bound. auto.
split. intros. pose proof (edgeless_graph_evalid e). contradiction.
split. intros. pose proof (edgeless_graph_evalid e). contradiction.
intros. pose proof (edgeless_graph_evalid e). contradiction.
split. unfold preserve_vlabel; intros. destruct vlabel; destruct vlabel. auto.
unfold preserve_elabel; intros. pose proof (edgeless_graph_evalid e). contradiction.
Qed.

Lemma uforest'_edgeless_graph:
  uforest' edgeless_graph.
Proof.
split; intros.
(*no self-loops*)
apply edgeless_graph_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_graph_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_graph_evalid in H; contradiction.
(*main forest definition*)
unfold unique_simple_upath; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

Lemma edgeless_graph_disconnected:
forall u v, u <> v -> ~ connected edgeless_graph u v.
Proof.
unfold not; intros.
destruct H0 as [p [? [? ?]]].
destruct p. inversion H1.
destruct p. inversion H1; inversion H2. subst u; subst v. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0.
pose proof (edgeless_graph_evalid x). contradiction.
Qed.

End EDGELESS_MUGRAPH.

(**************ADDING AN EDGE****************)

Section ADD_EDGE_MUGRAPH.

Context {g: MatrixUGraph}.
Context {u v: V} {vvalid_u: vvalid g u} {vvalid_v: vvalid g v} {uv_smaller: u <= v}.
Context {w: DE} {w_rep: Int.min_signed <= w < inf}.

Definition MatrixUGraph_adde':=
  labeledgraph_add_edge g (u,v) u v w.

Instance Fin_MatrixUGraph_adde':
  FiniteGraph (MatrixUGraph_adde').
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
(*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc. destruct (in_dec E_EqDec (u,v) (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists ((u,v)::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Instance AdjMatUSound_adde':
  AdjMatUSoundness MatrixUGraph_adde'.
Proof.
constructor; simpl.
+apply (@size_rep g (sound_MatrixUGraph g)).
+apply (@inf_rep g (sound_MatrixUGraph g)).
+apply (@vert_representable g (sound_MatrixUGraph g)).
+unfold addValidFunc, updateEdgeFunc; intros. unfold equiv_dec. destruct (E_EqDec (u,v) e).
  split; auto.
  unfold complement, equiv in c. destruct H. apply (@edge_strong_evalid g (sound_MatrixUGraph g) e H).
  symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  pose proof (@inf_rep g (sound_MatrixUGraph g)). lia.
  unfold complement, equiv in c. destruct H. apply (@edge_weight_representable g (sound_MatrixUGraph g) e H).
  symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. lia.
  destruct H. apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c. symmetry in H; contradiction.
+unfold addValidFunc, update_elabel, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0. exfalso; apply H; auto.
  destruct (evalid_dec g e). exfalso; apply H; auto. apply (@invalid_edge_weight g (sound_MatrixUGraph g) e n).
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  destruct H. apply (@src_fst g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c; symmetry in H; contradiction.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  unfold equiv in e0; subst e. simpl; auto.
  destruct H. apply (@dst_snd g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c; symmetry in H; contradiction.
+apply Fin_MatrixUGraph_adde'.
+unfold addValidFunc, updateEdgeFunc, equiv_dec; intros. destruct (E_EqDec (u,v) e).
  lia. destruct H. apply (@undirected_edge_rep g (sound_MatrixUGraph g) e H).
  unfold complement, equiv in c. symmetry in H; contradiction.
Qed.

Definition MatrixUGraph_adde: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    MatrixUGraph_adde' (AdjMatUSound_adde').

Lemma adde_vvalid:
  vvalid g v <-> vvalid MatrixUGraph_adde v.
Proof.
intros. simpl. split; auto.
Qed.

Lemma adde_evalid_or:
  forall e, evalid MatrixUGraph_adde e <-> (evalid g e \/ e = (u,v)).
Proof. unfold MatrixUGraph_adde; simpl; unfold addValidFunc. intros; split; auto. Qed.

(*all the Elist stuff are useless by themselves, because (@fin .. sound_matrx) clashes with Fin for some reason*)
Lemma adde_EList_new:
  ~ evalid g (u,v) -> Permutation ((u,v)::(EList g)) (EList MatrixUGraph_adde).
Proof.
intros. apply NoDup_Permutation. apply NoDup_cons. rewrite EList_evalid; auto. apply NoDup_EList. apply NoDup_EList.
intros; split; intros. rewrite EList_evalid, adde_evalid_or. destruct H0.
right; symmetry; auto. left; rewrite EList_evalid in H0; auto.
rewrite EList_evalid, adde_evalid_or in H0. destruct H0. right; rewrite EList_evalid; auto. left; symmetry; auto.
Qed.

Lemma adde_EList_old:
  forall e, In e (EList g) -> In e (EList MatrixUGraph_adde).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
apply H1. rewrite adde_evalid_or. left; rewrite <- EList_evalid; apply H.
Qed.

Lemma adde_EList_rev:
  forall l, ~ evalid g (u,v) ->
    Permutation ((u,v)::l) (EList MatrixUGraph_adde) ->
    Permutation l (EList g).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_Perm_EList in H0. apply NoDup_cons_1 in H0; auto.
apply NoDup_EList.
intros; split; intros. assert (In x (EList MatrixUGraph_adde)).
apply (Permutation_in (l:=(u,v)::l)). auto. right; auto.
apply EList_evalid in H2. apply adde_evalid_or in H2. destruct H2.
rewrite EList_evalid; auto.
subst x. assert (NoDup ((u,v)::l)). apply NoDup_Perm_EList in H0; auto.
apply NoDup_cons_2 in H2. contradiction.
destruct (E_EqDec x (u,v)). unfold equiv in e. subst x. apply EList_evalid in H1; contradiction.
unfold complement, equiv in c.
apply adde_EList_old in H1.
apply (Permutation_in (l':=(u,v)::l)) in H1. destruct H1. symmetry in H1; contradiction. auto.
apply Permutation_sym; auto.
Qed.

Lemma adde_src_new:
  src MatrixUGraph_adde (u,v) = u.
Proof.
apply (@src_fst _ (sound_MatrixUGraph _)). apply add_edge_evalid.
Qed.

Lemma adde_dst_new:
  dst MatrixUGraph_adde (u,v) = v.
Proof.
apply (@dst_snd _ (sound_MatrixUGraph _)). apply add_edge_evalid.
Qed.

Lemma adde_src_old:
  forall e', (u,v) <> e' -> src MatrixUGraph_adde e' = src g e'.
Proof.
unfold MatrixUGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e; contradiction. auto.
Qed.

Lemma adde_src:
  forall e', evalid g e' -> src MatrixUGraph_adde e' = src g e'.
Proof.
intros. rewrite (@src_fst _ (sound_MatrixUGraph _)). rewrite (@src_fst _ (sound_MatrixUGraph _)). auto.
auto. apply add_edge_preserves_evalid; auto.
Qed.

Lemma adde_dst_old:
  forall e', (u,v) <> e' -> dst MatrixUGraph_adde e' = dst g e'.
Proof.
unfold MatrixUGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e; contradiction. auto.
Qed.

Lemma adde_dst:
  forall e', evalid g e' -> dst MatrixUGraph_adde e' = dst g e'.
Proof.
intros. rewrite (@dst_snd _ (sound_MatrixUGraph _)). rewrite (@dst_snd _ (sound_MatrixUGraph _)). auto.
auto. apply add_edge_preserves_evalid; auto.
Qed.

Corollary adde_strong_evalid_new:
  strong_evalid MatrixUGraph_adde (u,v).
Proof.
split. apply add_edge_evalid. rewrite adde_src_new, adde_dst_new. simpl; auto.
Qed.

Lemma adde_strong_evalid_old:
  forall e', (u,v) <> e' ->
  evalid g e' ->
  strong_evalid MatrixUGraph_adde e'.
Proof.
intros. split. apply add_edge_preserves_evalid. apply H0.
apply (@edge_strong_evalid _ (sound_MatrixUGraph _)). apply add_edge_preserves_evalid. apply H0.
Qed.

Lemma adde_elabel_new:
  elabel MatrixUGraph_adde (u,v) = w.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec. auto.
unfold complement, equiv in c. contradiction.
Qed.

Lemma adde_elabel_old:
  forall e, e <> (u,v) -> elabel MatrixUGraph_adde e = elabel g e.
Proof.
intros. simpl. unfold update_elabel, equiv_dec. destruct E_EqDec.
unfold equiv in e0. symmetry in e0; contradiction.
auto.
Qed.

Lemma adde_partial_graph:
  forall (g': MatrixUGraph), is_partial_graph g g' -> evalid g' (u,v) -> is_partial_graph MatrixUGraph_adde g'.
Proof.
intros. destruct H as [? [? [? ?]]].
split. intros. simpl. apply H. auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
apply H1; auto. subst e; auto.
split. intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H2. apply adde_src. auto. auto. rewrite adde_src in H5 by auto. simpl in H5; auto.
subst e. rewrite (@src_fst _ (sound_MatrixUGraph g')).
rewrite (@src_fst _ (sound_MatrixUGraph MatrixUGraph_adde)). auto.
apply add_edge_evalid. auto.
intros. rewrite adde_evalid_or in H4. destruct H4.
rewrite <- H3. apply adde_dst. auto. auto. rewrite adde_dst in H5 by auto. simpl in H5; auto.
subst e. rewrite (@dst_snd _ (sound_MatrixUGraph g')).
rewrite (@dst_snd _ (sound_MatrixUGraph MatrixUGraph_adde)). auto.
apply add_edge_evalid. auto.
Qed.

Lemma adde_partial_lgraph:
  forall (g': MatrixUGraph), is_partial_lgraph g g' -> evalid g' (u,v) -> w = elabel g' (u,v) -> is_partial_lgraph MatrixUGraph_adde g'.
Proof.
intros. split. apply adde_partial_graph. apply H. auto.
split. unfold preserve_vlabel; intros.
destruct vlabel. destruct vlabel. auto.
unfold preserve_elabel; intros.
destruct H. destruct H3. unfold preserve_elabel in H4.
destruct (E_EqDec e (u,v)).
unfold equiv in e0. subst e. rewrite adde_elabel_new. rewrite H1. auto.
unfold complement, equiv in c. apply add_edge_evalid_rev in H2. rewrite adde_elabel_old.
rewrite <- H4. all: auto.
Qed.

End ADD_EDGE_MUGRAPH.

Section REMOVE_EDGE_MUGRAPH.

Context {g: MatrixUGraph}.
Context {e: E} {evalid_e: evalid g e}.

Definition MatrixUGraph_eremove':=
  @Build_LabeledGraph V E V_EqDec E_EqDec DV DE DG (pregraph_remove_edge g e)
  (vlabel g)
  (fun e0 => if E_EqDec e0 e then inf else elabel g e0 )
  (glabel g).

Instance Fin_MatrixUGraph_eremove':
  FiniteGraph (MatrixUGraph_eremove').
Proof.
constructor; unfold EnumEnsembles.Enumerable; simpl.
(*vertices*)exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
(*case e already inside*)
exists (remove E_EqDec e (EList g)). split. apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff, EList_evalid; auto. split; auto.
Qed.

Instance AdjMatUSound_eremove':
  AdjMatUSoundness MatrixUGraph_eremove'.
Proof.
constructor; simpl.
++apply (@size_rep g (sound_MatrixUGraph g)).
++apply (@inf_rep g (sound_MatrixUGraph g)).
++apply (@vert_representable g (sound_MatrixUGraph g)).
++unfold removeValidFunc; intros. destruct H. apply evalid_strong_evalid in H. apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). auto.
  pose proof (@inf_rep _ (sound_MatrixUGraph g)). split. apply (Z.le_trans _ 0).
  pose proof Int.min_signed_neg. lia. lia. lia.
  apply (@edge_weight_representable g (sound_MatrixUGraph g) e0). apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). destruct H. hnf in e1. contradiction.
  apply (@edge_weight_not_inf g (sound_MatrixUGraph g) e0). apply H.
++unfold removeValidFunc; intros. destruct (E_EqDec e0 e). auto.
  apply (@invalid_edge_weight g (sound_MatrixUGraph g) e0). unfold not; intros; apply H. split; auto.
++unfold removeValidFunc; intros. destruct H.
  apply (@src_fst g (sound_MatrixUGraph g) e0 H).
++unfold removeValidFunc; intros. destruct H.
  apply (@dst_snd g (sound_MatrixUGraph g) e0 H).
++apply Fin_MatrixUGraph_eremove'.
++unfold removeValidFunc; intros. destruct H.
  apply (@undirected_edge_rep g (sound_MatrixUGraph g) e0 H).
Qed.

Definition MatrixUGraph_eremove: MatrixUGraph :=
  @Build_GeneralGraph V E V_EqDec E_EqDec DV DE DG AdjMatUSoundness
    MatrixUGraph_eremove' (AdjMatUSound_eremove').

Lemma eremove_EList:
  forall l, Permutation (e::l) (EList g) -> Permutation l (EList MatrixUGraph_eremove).
Proof.
intros. assert (Hel: NoDup (e::l)). apply NoDup_Perm_EList in H; auto.
apply NoDup_Permutation.
apply NoDup_cons_1 in Hel; auto.
apply NoDup_EList.
intros. rewrite EList_evalid. simpl. unfold removeValidFunc. rewrite <- EList_evalid. split; intros.
split. apply (Permutation_in (l:=(e::l))). apply H. right; auto.
unfold not; intros. subst e. apply NoDup_cons_2 in Hel. contradiction.
destruct H0. apply Permutation_sym in H. apply (Permutation_in (l':=(e::l))) in H0. 2: auto.
destruct H0. symmetry in H0; contradiction. auto.
Qed.

Lemma eremove_EList_rev:
  forall l, evalid g e -> Permutation l (EList (MatrixUGraph_eremove)) -> Permutation (e::l) (EList g).
Proof.
intros. assert (~ In e (EList MatrixUGraph_eremove)).
rewrite EList_evalid. simpl. unfold removeValidFunc, not; intros. destruct H1. contradiction.
assert (~ In e l). unfold not; intros.
apply (Permutation_in (l':= (EList MatrixUGraph_eremove))) in H2. contradiction. auto.
apply NoDup_Permutation. apply NoDup_cons; auto. apply NoDup_Perm_EList in H0; auto.
apply NoDup_EList.
intros; split; intros. apply EList_evalid. destruct H3. subst x. auto.
apply (Permutation_in (l':= (EList MatrixUGraph_eremove))) in H3; auto.
rewrite EList_evalid in H3. simpl in H3. unfold removeValidFunc in H3. apply H3.
destruct (E_EqDec x e). unfold equiv in e0. subst x. left; auto.
unfold complement, equiv in c. right.
assert (evalid MatrixUGraph_eremove x).
simpl. unfold removeValidFunc. rewrite EList_evalid in H3. split; auto.
rewrite <- EList_evalid in H4.
apply (Permutation_in (l:= (EList MatrixUGraph_eremove))). apply Permutation_sym; auto. apply H4.
Qed.

End REMOVE_EDGE_MUGRAPH.

(**************MST****************)

Definition minimum_spanning_forest (t g: MatrixUGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': MatrixUGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

Lemma partial_lgraph_spanning_equiv:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> labeled_spanning_uforest t2 g -> Permutation (EList t1) (EList t2).
Proof.
intros. apply NoDup_Permutation.
apply NoDup_EList. apply NoDup_EList.
intros. repeat rewrite EList_evalid. split; intros.
apply H. auto.
destruct (evalid_dec t1 x). auto. exfalso.
pose proof (trivial_path1 t2 x (evalid_strong_evalid t2 x H2)). destruct H3.
assert (connected t1 (src t2 x) (dst t2 x)).
apply H0. apply H1. exists (src t2 x :: dst t2 x :: nil); auto.
destruct H5 as [p ?].
apply connected_by_upath_exists_simple_upath in H5. clear p.
destruct H5 as [p [? ?]].
assert (exists l, fits_upath t1 l p). apply connected_exists_list_edges in H5; auto.
destruct H7 as [l ?].
assert (~ In x l). unfold not; intros. apply (fits_upath_evalid t1 p l) in H8; auto.
assert (fits_upath t2 l p).
apply (fits_upath_transfer' p l t1 t2) in H7; auto.
  intros; split; intros. apply H. auto. rewrite vert_bound in *; auto.
  intros. apply H. apply (fits_upath_evalid t1 p l); auto.
  intros. apply H. auto. apply evalid_strong_evalid; auto.
  intros. apply H. auto. apply evalid_strong_evalid; auto.
assert (p = (src t2 x :: dst t2 x :: nil)). assert (unique_simple_upath t2). apply H1.
unfold unique_simple_upath in H10. apply (H10 (src t2 x) (dst t2 x)).
split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
apply connected_exists_list_edges'. intros. rewrite vert_bound. apply (valid_upath_vvalid t1) in H11.
rewrite vert_bound in H11; auto. apply H6.
exists l. auto.
apply H5. apply H5.
split. apply H3. apply NoDup_cons.
unfold not; intros. destruct H11. 2: contradiction.
symmetry in H11. assert (src t2 x <> dst t2 x). apply H1. auto. contradiction.
apply NoDup_cons. unfold not; intros; contradiction. apply NoDup_nil.
apply H3.
assert (x :: nil = l). apply (uforest'_unique_lpath p (x::nil) l t2).
apply H1. split. apply valid_upath_exists_list_edges'. exists l; auto. apply H6.
rewrite H10; auto. auto.
rewrite <- H11 in H8. apply H8. left; auto.
Qed.

Corollary partial_lgraph_spanning_sum_LE:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> labeled_spanning_uforest t2 g -> sum_DE Z.add t1 0 = sum_DE Z.add t2 0.
Proof.
intros. assert (Permutation (EList t1) (EList t2)).
apply (partial_lgraph_spanning_equiv t1 t2 g); auto.
unfold sum_DE. apply fold_left_comm.
intros. lia.
unfold DEList.
replace (map (elabel t1) (EList t1)) with (map (elabel g) (EList t1)).
replace (map (elabel t2) (EList t2)) with (map (elabel g) (EList t2)).
apply Permutation_map; auto.
apply map_ext_in. intros. symmetry; apply H1. rewrite EList_evalid in H3; auto.
apply map_ext_in. intros. symmetry; apply H0. rewrite EList_evalid in H3; auto.
Qed.

Corollary partial_lgraph_spanning_mst:
forall (t1 t2 g: MatrixUGraph), is_partial_lgraph t1 t2 -> labeled_spanning_uforest t1 g
  -> minimum_spanning_forest t2 g -> minimum_spanning_forest t1 g.
Proof.
intros. split. auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t2 0) _ ).
apply Z.eq_le_incl. apply (partial_lgraph_spanning_sum_LE t1 t2 g); auto. apply H1.
apply H1; auto.
Qed.

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_DE_equiv:
  forall (g: MatrixUGraph) (l: list E),
  Permutation (EList g) l -> sum_DE Z.add g 0 = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

(*
Lemma msf_swap_edges:
forall (t g: MatrixUGraph) (a b: E), minimum_spanning_forest t g -> evalid g a -> ~evalid t a ->
  evalid t b -> elabel g a <= elabel g b
  -> minimum_spanning_uforest MatrixUGraph_adde (MatrixUGraph_eremove b) a) g.
*)

Lemma connected_dec:
forall (g: MatrixUGraph) u v, connected g u v \/ ~ connected g u v.
Proof.
intros. tauto.
Qed.

Lemma exists_labeled_spanning_uforest_pre:
forall (l: list E) (g: MatrixUGraph), Permutation l (EList g) -> exists (t: MatrixUGraph), labeled_spanning_uforest t g.
Proof.
induction l; intros.
(*nil case*)
exists (@edgeless_graph (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g))).
split. split. apply edgeless_partial_lgraph. split. apply uforest'_edgeless_graph.
unfold spanning; intros. destruct (V_EqDec u v).
hnf in e. subst v. split; intros; apply connected_refl.
apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
apply connected_vvalid in H0. rewrite vert_bound in *. apply H0.
unfold complement, equiv in c. split; intros. exfalso. destruct H0.
unfold connected_by_path in H0. destruct H0. destruct H1. destruct x. inversion H1.
destruct x. inversion H1. inversion H2. subst v0. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0.
rewrite <- EList_evalid in H0. rewrite <- H in H0. contradiction.
pose proof (@edgeless_graph_disconnected (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g)) u v c).
contradiction.
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel. destruct vlabel. auto.
pose proof (@edgeless_graph_evalid (@inf_rep g (sound_MatrixUGraph g)) (@size_rep g (sound_MatrixUGraph g)) e).
contradiction.
(*inductive step*)
set (u:=src g a). set (v:=dst g a).
assert (connected g u v). apply adjacent_connected. exists a.
unfold u; unfold v; apply strong_evalid_adj_edge.
apply evalid_strong_evalid. rewrite <- EList_evalid, <- H. left; auto.
set (remove_a:=(@MatrixUGraph_eremove g a)).
assert (Ha_evalid: evalid g a). { rewrite <- EList_evalid. apply (Permutation_in (l:=(a::l))).
  apply H. left; auto. }
specialize IHl with remove_a.
destruct IHl as [t ?]. {
unfold remove_a. pose proof (@eremove_EList g a Ha_evalid l H).
apply NoDup_Permutation. assert (NoDup (a::l)). apply (Permutation_NoDup (l:=EList g)).
apply Permutation_sym; auto. apply NoDup_EList. apply NoDup_cons_1 in H2; auto.
apply NoDup_EList.
intros. rewrite EList_evalid. split; intros.
pose proof (Permutation_in (l:=l) (l':=_) x H1 H2). rewrite EList_evalid in H3; auto.
apply Permutation_sym in H1.
apply (Permutation_in (l:=_) (l':=l) x H1). rewrite EList_evalid; auto.
}
assert (Htg: is_partial_lgraph t g). {
  destruct H1. destruct H2. destruct H1. destruct H4. split.
  split. intros. apply H1 in H6. auto.
  split. intros. destruct H1. destruct H7. apply H7. auto.
  split. intros. apply H1 in H7. simpl in H7. auto. auto.
  intros. apply H1 in H7. simpl in H7. auto. auto.
  unfold preserve_vlabel, preserve_elabel; split; intros.
  destruct vlabel. destruct vlabel. auto.
  rewrite H3 by auto. simpl. destruct (E_EqDec e a). unfold equiv in e0.
  subst e. assert (evalid remove_a a). apply H1; auto.
  simpl in H7. unfold removeValidFunc in H7. destruct H7; contradiction.
  auto.
}
destruct (connected_dec remove_a u v).
(*already connected*)
++
exists t. destruct H1.  destruct H3. destruct H1. destruct H5.
split. split.
(*partial_graph*)
apply Htg.
(*uforest*)
split. auto.
(*spanning*)
unfold spanning in *. intros. rewrite <- H6. split; intros.
{(*---------->*)
destruct H7 as [p ?].
apply (connected_by_upath_exists_simple_upath) in H7. destruct H7 as [p' [? ?]]. clear p.
assert (exists l, fits_upath g l p'). apply (connected_exists_list_edges g p' u0 v0); auto.
destruct H9 as [l' ?]. destruct (in_dec E_EqDec a l').
**(*yes: split the path*)
assert (NoDup l'). apply (simple_upath_list_edges_NoDup g p' l'); auto.
apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. subst l'. fold u in H11. fold v in H11.
assert (~ In a l1). unfold not; intros.
apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14. apply H14.
apply in_or_app. left; left; auto.
assert (~ In a l2). unfold not; intros.
apply NoDup_app_r in H10. apply (NoDup_app_not_in E (a::nil) l2 H10 a).
left; auto. auto.
destruct H11; destruct H11.
****
apply (connected_trans _ u0 u). exists p1. split.
apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ u v). auto.
exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
****
apply (connected_trans _ u0 v). exists p1. split.
apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ v u). apply connected_symm; auto.
exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
**(*no: fits_upath_transfer*)
exists p'. split. apply (remove_edge_valid_upath _ a p' l'); auto. apply H7. apply H7.
} { (*<---*)
destruct H7 as [p [? ?]]. exists p. split.
apply remove_edge_unaffected in H7; auto. auto.
}
(*labels*)
apply Htg.
++
assert (vvalid g u /\ vvalid g v). apply connected_vvalid in H0; auto. destruct H3.
assert (u <= v). apply (@undirected_edge_rep g (sound_MatrixUGraph g)). auto.
set (w:= elabel g a).
assert (Int.min_signed <= w < inf). split.
unfold w; apply (@edge_weight_representable g (sound_MatrixUGraph g)). auto.
unfold w; apply (@edge_weight_not_inf g (sound_MatrixUGraph g)). auto.
rewrite vert_bound in H3, H4. rewrite <- (vert_bound t) in H3, H4.
assert (Ha: a = (u,v)). unfold u, v; apply evalid_form; auto. rewrite Ha in *.
set (adde_a:=@MatrixUGraph_adde t u v H3 H4 H5 w H6).
exists adde_a. split. split.
apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto.
split.
(*uforest*)
apply add_edge_uforest'; auto. apply H1.
unfold not; intros.
apply (is_partial_lgraph_connected t remove_a) in H7. contradiction.
split. apply H1. apply H1.
(*spanning*)
unfold spanning; intros. assert (Ht_uv: ~ evalid t (u,v)). unfold not; intros.
assert (evalid remove_a (u,v)). apply H1; auto.
simpl in H8. rewrite Ha in H8. unfold removeValidFunc in H8. destruct H8; contradiction.
split; intros.
{ (*-->*) destruct H7 as [p ?]. apply connected_by_upath_exists_simple_upath in H7.
destruct H7 as [p' [? ?]]. clear p.
assert (exists l', fits_upath g l' p'). apply connected_exists_list_edges in H7; auto.
destruct H9 as [l' ?]. assert (NoDup l'). apply simple_upath_list_edges_NoDup in H9; auto.
destruct (in_dec E_EqDec a l').
**
apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. fold u in H11. fold v in H11. subst l'.
assert (~ In a l1). unfold not; intros. apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14.
apply H14. apply in_or_app. left; left; auto.
assert (~ In a l2). unfold not; intros. apply NoDup_app_r in H10.
apply (NoDup_app_not_in E (a::nil) l2 H10 a). left; auto. auto.
destruct H11; destruct H11.
****
apply (connected_trans _ u0 u). apply add_edge_connected; auto.
apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ u v). apply adjacent_connected.
exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
apply add_edge_connected; auto. apply H1. exists p2. split.
apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
****
apply (connected_trans _ u0 v). apply add_edge_connected; auto.
apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
apply (connected_trans _ v u). apply adjacent_connected. apply adjacent_symm.
exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
apply add_edge_connected; auto. apply H1. exists p2. split.
apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
**
apply add_edge_connected; auto.
apply H1. exists p'. split. 2: apply H7.
apply (remove_edge_valid_upath g a p' l'); auto. apply H7.
} {
apply (is_partial_lgraph_connected adde_a g).
apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto. auto.
}
(*labels*)
unfold preserve_vlabel, preserve_elabel; split; intros.
destruct vlabel; destruct vlabel; auto.
simpl. unfold update_elabel, equiv_dec.
destruct (E_EqDec (u,v) e). hnf in e0. subst e. unfold w; rewrite Ha; auto.
apply Htg. simpl in H7. unfold addValidFunc in H7. destruct H7. apply H7.
unfold complement, equiv in c. symmetry in H7; contradiction.
Qed.

Corollary exists_labeled_spanning_uforest:
forall (g: MatrixUGraph), exists (t: MatrixUGraph), labeled_spanning_uforest t g.
Proof.
intros. apply (exists_labeled_spanning_uforest_pre (EList g)). apply Permutation_refl.
Qed.

Lemma partial_graph_incl:
forall (t g: MatrixUGraph), is_partial_graph t g -> incl (EList t) (EList g).
Proof.
unfold incl; intros. rewrite EList_evalid in *. apply H; auto.
Qed.

(***************FIND LEMMAS*******)
Lemma find_app_In1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1 l2: list A) v ans, In v l1 -> find (l1++l2) v ans = find l1 v ans.
Proof.
induction l1; intros. contradiction.
destruct (EA v a). hnf in e. subst a.
simpl.
destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
destruct H. symmetry in H; contradiction.
simpl. destruct (EA a v). symmetry in e; contradiction.
rewrite IHl1; auto.
Qed.

Lemma find_accum_add1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans1 ans2, find l v (ans1+ans2) = ans1 + find l v ans2.
Proof.
induction l; intros.
simpl. auto.
simpl. destruct (EA a v). auto.
replace (1+(ans1+ans2)) with (ans1 + (1+ans2)) by lia. apply IHl.
Qed.

Lemma find_app_notIn1:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, ~ In v l1 -> find (l1++l2) v ans = Zlength l1 + find l2 v ans.
Proof.
induction l1; intros. rewrite app_nil_l, Zlength_nil. lia.
assert (~ In v l1). unfold not; intros; apply H. right; auto.
simpl. destruct (EA a v). hnf in e; subst a. exfalso. apply H. left; auto.
rewrite Zlength_cons. rewrite IHl1; auto.
rewrite <- Z.add_1_r, <- Z.add_assoc. rewrite find_accum_add1. auto.
Qed.

Corollary find_notIn:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ~ In v l -> find l v ans = Zlength l + ans.
Proof.
intros. replace l with (l++nil). rewrite find_app_notIn1. simpl.
rewrite app_nil_r; auto.
auto. apply app_nil_r.
Qed.

Corollary find_notIn_0:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v, ~ In v l -> find l v 0 = Zlength l.
Proof. intros. rewrite find_notIn by auto. rewrite Z.add_0_r; auto. Qed.

Lemma find_In_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, In v l -> find l v ans < Zlength l + ans.
Proof.
induction l; intros. contradiction.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
assert (find l v ans < Zlength l + ans). apply IHl. destruct H. contradiction. auto.
lia.
Qed.

Lemma find_ubound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find l v ans <= Zlength l + ans.
Proof.
induction l; intros. rewrite Zlength_nil; simpl; lia.
rewrite Zlength_cons.
simpl. destruct (EA a v).
pose proof (Zlength_nonneg l); lia.
rewrite Z.add_succ_l. rewrite find_accum_add1, Z.add_1_l.
specialize IHl with v ans.
lia.
Qed.

Lemma find_cons:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, find (v::l) v ans = ans.
Proof.
intros. simpl. destruct (EA v v). auto. unfold RelationClasses.complement, Equivalence.equiv in c; contradiction.
Qed.

Lemma find_lbound:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) v ans, ans <= find l v ans.
Proof.
induction l; intros. simpl. lia.
simpl. destruct (EA a v). lia.
rewrite find_accum_add1. specialize IHl with v ans; lia.
Qed.

Lemma find_app_le:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l1: list A) l2 v ans, find l1 v ans <= find (l1++l2) v ans.
Proof.
induction l1; intros.
rewrite app_nil_l. simpl. apply find_lbound.
simpl. destruct (EA a v). lia.
do 2 rewrite find_accum_add1. specialize IHl1 with l2 v ans. lia.
Qed.

Lemma find_eq:
forall {A:Type} {EA: EquivDec.EqDec A eq} (l: list A) x y acc, NoDup l -> In x l -> In y l -> find l x acc = find l y acc -> x = y.
Proof.
induction l; intros. contradiction.
destruct H0; destruct H1.
++
subst x; subst y. auto.
++
subst x. rewrite find_cons in H2.
simpl in H2. destruct (EA a y). hnf in e; subst y. apply NoDup_cons_2 in H; contradiction.
rewrite find_accum_add1 in H2. pose proof (find_lbound l y acc). lia.
++
subst y. rewrite find_cons in H2.
simpl in H2. destruct (EA a x). hnf in e; subst x. apply NoDup_cons_2 in H; contradiction.
rewrite find_accum_add1 in H2. pose proof (find_lbound l x acc). lia.
++
simpl in H2. destruct (EA a x). hnf in e; subst x. apply NoDup_cons_2 in H; contradiction.
destruct (EA a y). hnf in e; subst y. apply NoDup_cons_2 in H; contradiction.
do 2 rewrite find_accum_add1 in H2. apply (IHl x y acc).
apply NoDup_cons_1 in H; auto. auto. auto. lia.
Qed.

Lemma NoDup_incl_ordered_powerlist:
forall (l: list E), NoDup l -> exists L,
  (forall l', (NoDup l' /\ incl l' l /\ (forall x y, In x l' -> In y l' -> (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0)))
  <-> In l' L).
Proof.
induction l; intros.
exists (nil::nil). intros; split; intros. destruct H0 as [? [? ?]]. destruct l'. left; auto.
assert (In e (e::l')). left; auto. apply H1 in H3; contradiction.
destruct H0. subst l'. split. apply NoDup_nil. split. unfold incl; intros; auto.
intros. simpl. lia.
contradiction.
(*inductive step*)
assert (~ In a l). apply NoDup_cons_2 in H; auto. apply NoDup_cons_1 in H.
destruct (IHl H) as [L ?]. clear IHl.
assert (forall l', In l' L -> ~ In a l').
intros. apply H1 in H2. destruct H2 as [? [? ?]]. unfold not; intros. apply H3 in H5. contradiction.
exists (L ++ map (fun l' => (a::l')) L).
intros; split; intros.
**
destruct H3 as [? [? ?]]. apply in_or_app.
destruct (in_dec E_EqDec a l').
****
right.
(*then l' must be of form (a::l'')*)
destruct l'. contradiction.
destruct (E_EqDec e a).
******
hnf in e0. subst e.
apply in_map. apply H1.
split. apply NoDup_cons_1 in H3; auto.
split. unfold incl; intros. assert (In a0 (a::l)). apply H4. right; auto.
destruct H7. subst a0. apply NoDup_cons_2 in H3. contradiction. auto.
intros.
assert (find (a :: l') x 0 <= find (a :: l') y 0 <-> find (a :: l) x 0 <= find (a :: l) y 0). apply H5.
right; auto. right; auto.
apply NoDup_cons_2 in H3.
simpl in H8.
destruct (E_EqDec a x). hnf in e. subst x. contradiction.
destruct (E_EqDec a y). hnf in e. subst y. contradiction.
replace 1 with (1+0) in H8 by lia. repeat rewrite find_accum_add1 in H8.
split; intros. lia. lia.
******
unfold complement, equiv in c.
assert (find (e :: l') e 0 <= find (e :: l') a 0 <-> find (a :: l) e 0 <= find (a :: l) a 0). apply H5.
left; auto. auto. simpl in H6.
destruct (E_EqDec e e). 2: { unfold complement, equiv in c0; contradiction. }
destruct (E_EqDec a a). 2: { unfold complement, equiv in c0; contradiction. }
clear e0 e1.
destruct (E_EqDec e a). hnf in e0; contradiction.
destruct (E_EqDec a e). hnf in e0; symmetry in e0; contradiction.
clear c0 c1.
assert (0 <= find l' a 1). { apply (Z.le_trans 0 1). lia. apply find_lbound. }
apply H6 in H7. assert (1 <= 0). { apply (Z.le_trans 1 (find l e 1)). apply find_lbound. auto. }
lia.
****
left. apply H1. split. auto. split. unfold incl; intros. assert (In a0 (a::l)). apply H4; auto.
destruct H7. subst a0. contradiction. auto.
intros. assert (find l' x 0 <= find l' y 0 <-> find (a :: l) x 0 <= find (a :: l) y 0). apply H5; auto.
simpl in H8. destruct (E_EqDec a x). hnf in e. subst x. contradiction.
destruct (E_EqDec a y). hnf in e. subst y. contradiction.
replace 1 with (1+0) in H8 by lia. do 2 rewrite find_accum_add1 in H8.
split; intros. apply H8 in H9. lia.
apply H8. lia.
**
apply in_app_or in H3. destruct H3.
****
apply H1 in H3. destruct H3 as [? [? ?]].
split. auto. split. unfold incl; intros. right. apply H4. auto.
intros.
assert (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0). apply H5; auto.
simpl.
destruct (E_EqDec a x). hnf in e; subst x. apply H4 in H6; contradiction.
destruct (E_EqDec a y). hnf in e; subst y. apply H4 in H7; contradiction.
replace 1 with (1+0) by lia. do 2 rewrite (find_accum_add1).
split; intros. apply H8 in H9. lia. lia.
****
apply list_in_map_inv in H3. destruct H3 as [lx [? ?]]. subst l'. rename lx into l'.
assert (~ In a l'). apply H2; auto. apply H1 in H4. destruct H4 as [? [? ?]].
split. apply NoDup_cons; auto.
split. unfold incl; intros. destruct H7. subst a0. left; auto.
right. apply H5. auto.
intros. destruct H7.
subst x. simpl. destruct (E_EqDec a a). 2: { unfold complement, equiv in c; contradiction. }
destruct (E_EqDec a y). lia. split; intros. apply (Z.le_trans 0 1). lia. apply find_lbound. apply (Z.le_trans 0 1). lia. apply find_lbound.
destruct H8. subst y. simpl.
destruct (E_EqDec a a). 2: { unfold complement, equiv in c; contradiction. }
destruct (E_EqDec a x). lia. split; intros.
assert (1 <= 0). apply (Z.le_trans 1 (find l' x 1)). apply find_lbound. lia. lia.
assert (1 <= 0). apply (Z.le_trans 1 (find l x 1)). apply find_lbound. lia. lia.
assert (find l' x 0 <= find l' y 0 <-> find l x 0 <= find l y 0). apply H6; auto. simpl.
destruct (E_EqDec a x). hnf in e; subst x; contradiction.
destruct (E_EqDec a y). hnf in e; subst y; contradiction.
replace 1 with (1+0) by lia. repeat rewrite find_accum_add1.
split; intros; lia.
Qed.

Lemma exists_Zmin:
  forall {A:Type} (l: list A) (f: A -> Z), l <> nil -> exists a, In a l /\ (forall b, In b l -> f a <= f b).
Proof.
induction l; intros. contradiction.
destruct l. exists a. split. left; auto. intros. destruct H0. subst b. lia. contradiction.
assert (exists a : A, In a (a0 :: l) /\ (forall b : A, In b (a0 :: l) -> f a <= f b)). apply IHl. unfold not; intros. inversion H0.
destruct H0 as [a' [? ?]].
destruct (Z.le_ge_cases (f a) (f a')).
exists a. split. left; auto. intros. destruct H3. subst a; lia. apply H1 in H3. lia.
exists a'. split. right; auto. intros. destruct H3. subst b; lia. apply H1 in H3; lia.
Qed.

Lemma test2:
forall l' l, NoDup l -> NoDup l' -> incl l' l -> exists lsorted, Permutation lsorted l' /\
(forall a b, In a lsorted -> In b lsorted -> (find lsorted a 0 <= find lsorted b 0 <-> find l a 0 <= find l b 0)).
Proof.
induction l'; intros l Hl; intros.
exists nil. split. apply perm_nil. intros. contradiction.
assert (exists lsorted : list E,
         Permutation lsorted l' /\
         (forall a b : E, In a lsorted -> In b lsorted -> find lsorted a 0 <= find lsorted b 0 <-> find l a 0 <= find l b 0)).
apply IHl'. auto. apply NoDup_cons_1 in H; auto. unfold incl; intros. apply H0. right; auto. clear IHl'.
destruct H1 as [lsorted [? ?]].
assert (Ha: ~ In a lsorted). unfold not; intros. apply (Permutation_in (l':=l')) in H3. 2: auto.
apply NoDup_cons_2 in H; contradiction.
assert (Hsorted_NoDup: NoDup lsorted). apply (Permutation_NoDup (l:=l')). apply Permutation_sym; auto. apply NoDup_cons_1 in H; auto.
(*split the list*)
set (k:= find l a 0) in *.
assert (exists l1 l2, lsorted = l1++l2 /\ (forall x, In x l1 -> find l x 0 < find l a 0) /\ (forall x, In x l2 -> find l a 0 <= find l x 0)). {
clear H1.
induction lsorted. exists nil; exists nil. split. rewrite app_nil_r; auto.
split; intros; contradiction.
destruct (Z.lt_ge_cases (find l a0 0) (find l a 0)); rename H1 into Ha0.
++
assert (exists l1 l2 : list E,
              lsorted = l1 ++ l2 /\
              (forall x : E, In x l1 -> find l x 0 < find l a 0) /\ (forall x : E, In x l2 -> find l a 0 <= find l x 0)). {
apply IHlsorted. 2: { unfold not; intros. apply Ha. right; auto. }
2: { apply NoDup_cons_1 in Hsorted_NoDup; auto. }
intros. split; intros.
apply H2. right; auto. right; auto.
apply NoDup_cons_2 in Hsorted_NoDup.
simpl. destruct (E_EqDec a0 a1). hnf in e; subst a0; contradiction.
destruct (E_EqDec a0 b). hnf in e; subst a0; contradiction.
replace 1 with (1+0) by lia. do 2 rewrite find_accum_add1. lia.
apply H2 in H4. 2: right; auto. 2: right; auto.
simpl in H4. apply NoDup_cons_2 in Hsorted_NoDup.
destruct (E_EqDec a0 a1). hnf in e; subst a0; contradiction.
destruct (E_EqDec a0 b). hnf in e; subst a0; contradiction.
replace 1 with (1+0) in H4 by lia. do 2 rewrite find_accum_add1 in H4. lia.
} clear IHlsorted.
destruct H1 as [l1 [l2 [? [? ?]]]].
exists (a0::l1). exists l2. split. simpl. rewrite H1; auto.
split; intros. destruct H5. subst x; auto. apply H3; auto.
apply H4; auto.
++
exists nil. exists (a0::lsorted). split. auto.
split; intros. contradiction.
destruct H1. subst x. auto.
apply (Z.le_trans _ (find l a0 0)). auto.
apply H2. left; auto. right; auto.
rewrite find_cons. apply find_lbound.
}
destruct H3 as [l1 [l2 [? [? ?]]]]. subst lsorted.
exists (l1++a::l2).
split. { apply NoDup_Permutation. apply NoDup_app_inv. apply NoDup_app_l in Hsorted_NoDup; auto.
apply NoDup_cons. unfold not; intros; apply Ha. apply in_or_app; right; auto.
apply NoDup_app_r in Hsorted_NoDup; auto.
unfold not; intros. destruct H6. subst x. apply Ha. apply in_or_app; left; auto.
assert (~ In x l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
auto.
split; intros. apply in_app_or in H3; destruct H3. right. apply (Permutation_in (l:=l1++l2)); auto. apply in_or_app; left; auto.
destruct H3. subst x. left; auto. right. apply (Permutation_in (l:=l1++l2)); auto. apply in_or_app; right; auto.
apply in_or_app. destruct H3. subst x. right; left; auto.
apply (Permutation_in (l':=l1++l2)) in H3. 2: apply Permutation_sym; auto.
apply in_app_or in H3; destruct H3. left; auto. right; right; auto.
}
intros. apply in_app_or in H3. apply in_app_or in H6. specialize H2 with a0 b.
destruct H3; destruct H6.
**
rewrite (find_app_In1 l1 (a::l2)) by auto. rewrite find_app_In1 by auto.
rewrite find_app_In1 in H2 by auto. rewrite find_app_In1 in H2 by auto.
apply H2. apply in_or_app. left; auto. apply in_or_app; left; auto.
**
rewrite find_app_In1 by auto.
assert (~ In b l1). unfold not; intros. destruct H6. subst b. apply Ha. apply in_or_app; left; auto.
assert (~ In b l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
rewrite find_app_notIn1 by auto.
destruct H6. subst b. split; intros. apply Z.le_lteq. left; apply H4; auto.
apply (Z.le_trans _ (Zlength l1 + 0)). apply find_ubound. pose proof (find_lbound (a::l2) a 0); lia.
split; intros. apply (Z.le_trans _ (find l a 0)). apply Z.le_lteq. left; apply H4; auto. apply H5; auto.
apply (Z.le_trans _ (Zlength l1 + 0)). apply find_ubound. pose proof (find_lbound (a::l2) b 0); lia.
**
assert (~ In a0 l1). unfold not; intros. destruct H3. subst a0. apply Ha. apply in_or_app; left; auto.
assert (~ In a0 l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
(*this is false*)
rewrite find_app_notIn1 by auto. rewrite find_app_In1 by auto.
split; intros. assert (find l1 b 0 < Zlength l1 + 0). apply find_In_ubound; auto. rewrite Z.add_0_r in H9.
assert (0 <= find (a::l2) a0 0). apply find_lbound. lia.
destruct H3. subst a0.
****
assert (find l b 0 < find l a 0). apply H4; auto. lia.
****
assert (find l b 0 < find l a0 0). apply (Z.lt_le_trans _ (find l a 0)). apply H4; auto. apply H5; auto. lia.
**
assert (~ In a0 l1). unfold not; intros. destruct H3. subst a0. apply Ha. apply in_or_app; left; auto.
assert (~ In a0 l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
assert (~ In b l1). unfold not; intros. destruct H6. subst b. apply Ha. apply in_or_app; left; auto.
assert (~ In b l2). apply (NoDup_app_not_in E l1 l2); auto. contradiction.
rewrite find_app_notIn1 by auto. rewrite find_app_notIn1 by auto.
rewrite find_app_notIn1 in H2 by auto. rewrite find_app_notIn1 in H2 by auto.
destruct H3; destruct H6.
****
subst a0. subst b. split; intros; lia.
****
subst a0. rewrite find_cons. split; intros. apply H5; auto. pose proof (find_lbound (a::l2) b 0); lia.
****
subst b. rewrite find_cons. (*falseness*)
split; intros.
assert (0 < find (a::l2) a0 0). simpl. destruct (E_EqDec a a0).
hnf in e. subst a0. exfalso; apply Ha. apply in_or_app; right; auto.
pose proof (find_lbound l2 a0 1). lia.
lia.
apply Z.le_lteq in H6. destruct H6.
assert (find l a 0 <= find l a0 0). apply H5; auto. lia.
assert (incl l' l). unfold incl; intros. apply H0. right; auto.
apply (find_eq l a0 a 0) in H6. subst a0. rewrite find_cons; lia.
auto. apply H9. apply (Permutation_in (l:= (l1++l2))); auto. apply in_or_app; right; auto.
apply H0. left; auto.
**** rewrite <- H2.
2: apply in_or_app; right; auto. 2: apply in_or_app; right; auto.
simpl.
destruct (E_EqDec a a0). hnf in e; subst a0. exfalso; apply Ha. apply in_or_app; right; auto.
destruct (E_EqDec a b). hnf in e; subst b. exfalso; apply Ha. apply in_or_app; right; auto.
replace 1 with (1+0) by lia. do 2 rewrite find_accum_add1. split; intros; lia.
Qed.

Lemma exists_dec:
forall (g: MatrixUGraph) l, (exists (t: MatrixUGraph), labeled_spanning_uforest t g /\ Permutation l (EList t)) \/
  ~ (exists (t: MatrixUGraph), labeled_spanning_uforest t g /\ Permutation l (EList t)).
Proof.
intros. tauto.
Qed.

Lemma partial_lgraph_elabel_map:
forall (t g: MatrixUGraph) l, is_partial_lgraph t g -> incl l (EList t) ->
  map (elabel t) l = map (elabel g) l.
Proof.
induction l; intros. simpl; auto.
simpl. replace (elabel g a) with (elabel t a). rewrite IHl; auto.
apply incl_cons_inv in H0; auto.
apply H. rewrite <- EList_evalid. apply H0. left; auto.
Qed.

Lemma exists_msf:
forall (g: MatrixUGraph), exists (t: MatrixUGraph), minimum_spanning_forest t g.
Proof.
intros. pose proof (NoDup_incl_ordered_powerlist (EList g) (NoDup_EList g)).
destruct H as [L ?].
(*now what I need is the subset of L that exists t, labeled_spanning_uforest t g ...*)
destruct (list_decidable_prop_reduced_list
  (fun l' => NoDup l' /\ incl l' (EList g) /\ (forall x y, In x l' -> In y l' ->
      (find l' x 0 <= find l' y 0 <-> find (EList g) x 0 <= find (EList g) y 0)))
  (fun l => (exists (t: MatrixUGraph), labeled_spanning_uforest t g /\ Permutation l (EList t)))
  L
).
apply exists_dec.
intros; split; intros. rewrite <- H in H0. destruct H0 as [? [? ?]].
split. apply H0. split. apply H1. apply H2.
rewrite <- H. auto.
rename x into Lspan.
assert (Lspan <> nil). unfold not; intros. {
destruct (exists_labeled_spanning_uforest g) as [t ?].
destruct (test2 (EList t) (EList g)) as [lt ?]. apply NoDup_EList. apply NoDup_EList.
apply partial_graph_incl. apply H2. destruct H3.
assert (In lt Lspan). apply H0. split. split. apply (Permutation_NoDup (l:=EList t)).
apply Permutation_sym; auto. apply NoDup_EList.
split. unfold incl; intros. apply (Permutation_in (l':=EList t)) in H5; auto.
apply (partial_graph_incl t g) in H5; auto. apply H2. apply H4.
exists t. split; auto.
rewrite H1 in H5; contradiction.
}
pose proof (exists_Zmin Lspan (fun l => fold_left Z.add (map (elabel g) l) 0) H1).
destruct H2 as [lmin [? ?]].
apply H0 in H2. destruct H2. destruct H2 as [? [? ?]]. destruct H4 as [msf [? ?]].
exists msf. unfold minimum_spanning_forest. split. apply H4. intros.
destruct (test2 (EList t') (EList g)) as [lt' ?]. apply NoDup_EList. apply NoDup_EList.
apply partial_graph_incl. apply H8. destruct H9.
rewrite (sum_DE_equiv msf lmin). 2: apply Permutation_sym; auto.
rewrite (sum_DE_equiv t' lt'). 2: apply Permutation_sym; auto.
replace (map (elabel msf) lmin) with (map (elabel g) lmin).
replace (map (elabel t') lt') with (map (elabel g) lt').
apply H3. apply H0. split. split.
apply (Permutation_NoDup (l:=EList t')). apply Permutation_sym; auto. apply NoDup_EList.
split. unfold incl; intros. apply (Permutation_in (l':=EList t')) in H11; auto.
apply (partial_graph_incl t' g) in H11. auto. apply H8.
apply H10. exists t'. split; auto.
symmetry; apply partial_lgraph_elabel_map. split. apply H8. apply H8.
apply Permutation_incl; auto.
symmetry; apply partial_lgraph_elabel_map. split. apply H4. apply H4.
apply Permutation_incl; auto.
Qed.

Lemma msf_if_le_msf:
forall (t g: MatrixUGraph), labeled_spanning_uforest t g ->
  (forall t', minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
  minimum_spanning_forest t g.
Proof.
intros. unfold minimum_spanning_forest. split. auto.
intros. destruct (exists_msf g) as [msf ?].
apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
apply H2. auto.
Qed.

Corollary msf_if_le_msf':
forall (t t' g: MatrixUGraph), labeled_spanning_uforest t g ->
  minimum_spanning_forest t' g -> sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
  minimum_spanning_forest t g.
Proof.
intros. apply msf_if_le_msf; auto.
intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
apply H0. apply H2.
Qed.

End MATRIXUGRAPH.
