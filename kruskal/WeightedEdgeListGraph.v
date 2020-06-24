(*Looted from msl_application/DijkstraArrayGraph
Should try abstracting it if possible from an EdgeListGraph*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import VST.msl.seplog.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
(*Require Import RamifyCoq.msl_application.ArrayGraph.*) (*I probably need this to transform this graph to the ArrayGraph?*)
Require Import RamifyCoq.graph.FiniteGraph.
Require Import compcert.lib.Coqlib.
Require Import RamifyCoq.kruskal.undirected_graph.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

Local Open Scope logic.
Local Open Scope Z_scope.

Instance Z_EqDec : EqDec Z eq. Proof. hnf. intros. apply Z.eq_dec. Defined.

Definition is_null_Z: DecidablePred Z := existT (fun P : Z -> Prop => forall a : Z, {P a} + {~ P a}) (fun x : Z => x < 0) (fun a : Z => Z_lt_dec a 0).

(*
 Concretizing the EdgelistGraph with array-specific types.
 |  V  |    E    |    DV   |  DE |  DG  | soundness |
 |-----|---------|---------|-----|------|-----------| 
 |  Z  |  Z * Z  |    ?    |  Z  | unit |  Finite   |
 *)

Definition VType : Type := Z. (*0...V-1*)
Definition EType : Type := VType * VType.
Definition LE : Type := Z. (*weight*)
Definition LV: Type := unit. (*I don't think we need this*)
Definition LG: Type := unit.

Instance V_EqDec: EqDec VType eq.
Proof. hnf. apply Z.eq_dec. Qed.

Instance E_EqDec: EqDec EType eq.
Proof.
  hnf. intros [x] [y].
  destruct (equiv_dec x y).
  - hnf in e. destruct (Z.eq_dec v v0); subst.
    + left; reflexivity.
    + right. intro. apply n. inversion H. reflexivity.
  - right; intro; apply c; inversion H; reflexivity.
Defined.

Definition WEdgeListGraph := LabeledGraph VType EType LV LE LG.

Lemma WEdgeListGraph_no_vlabel:
  forall (g: WEdgeListGraph) v, vlabel g v = tt.
Proof. intros. destruct vlabel. auto.
Qed.

Class Fin (g: WEdgeListGraph) :=
  { fin: FiniteGraph g; }.

Definition FiniteWEdgeListGraph := (GeneralGraph VType EType LV LE LG (fun g => Fin g)).

(* Later, we'll need ways to fish out the LG from the GG, 
   and we'll need to show that the specialized 
   LG you have is, at heart, an LG 
 *)
Definition FiniteWEdgeListGraph_WEdgeListGraph
           (g: FiniteWEdgeListGraph) : WEdgeListGraph := lg_gg g.
Local Coercion FiniteWEdgeListGraph_WEdgeListGraph: FiniteWEdgeListGraph >-> WEdgeListGraph.
Local Identity Coercion WEdgeListGraph_LabeledGraph: WEdgeListGraph >-> LabeledGraph.

(* This is the main thing you needed: an existing instance of 
   how to drag out FiniteGraph properties from your 
   existing GeneralGraph
 *)
Instance finGraph (g: FiniteWEdgeListGraph): FiniteGraph g := @fin g (@sound_gg _ _ _ _ _ _ _ _ g).
(* Nice. Now your definitions will be cleaner. *)

Definition vertex_valid (g: WEdgeListGraph): Prop :=
  forall v, vvalid g v -> 0 <= v < Int.max_signed.

Definition edge_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> (vvalid g (src g e) /\ vvalid g (dst g e)).

Definition weight_valid (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> Int.min_signed <= elabel g e <= Int.max_signed. (*< IFTY*)

Definition src_edge (g : WEdgeListGraph): Prop :=
  forall e, evalid g e -> src g e = fst e.

Definition dst_edge (g: WEdgeListGraph): Prop :=
  forall e, evalid g e -> dst g e = snd e.

Definition sound_weighted_edge_graph (g: WEdgeListGraph): Prop :=
  vertex_valid g /\ edge_valid g /\ weight_valid g /\ src_edge g /\ dst_edge g.

(*because it keeps appearing*)
Lemma sound_src:
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> fst e = src g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_dst:
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> snd e = dst g e.
Proof. intros. symmetry. apply H. auto. Qed.

Lemma sound_strong_evalid: (*literally the definition of edge_valid*)
  forall (g: WEdgeListGraph) e, sound_weighted_edge_graph g -> evalid g e -> strong_evalid g e.
Proof.
intros. split. auto. apply H. auto.
Qed.

Corollary sound_uv_vvalid:
  forall (g: WEdgeListGraph) u v, sound_weighted_edge_graph g -> evalid g (u,v) -> vvalid g u /\ vvalid g v.
Proof.
intros. apply sound_strong_evalid in H0; auto. destruct H0.
destruct H as [? [? [? [? ?]]]].
rewrite H4, H5 in H1; auto.
Qed.

Definition numV (g: FiniteWEdgeListGraph) : Z := Zlength (VList g).
Definition numE (g: FiniteWEdgeListGraph) : Z := Zlength (EList g).

Lemma numE_pos: forall g, 0 <= numE g.
Proof. intros. unfold numE. apply Zlength_nonneg. Qed.

Definition edge_to_wedge (g: WEdgeListGraph) e : LE * EType := (elabel g e, e).

Definition graph_to_wedgelist (g: FiniteWEdgeListGraph) : list (LE * EType) :=
  map (edge_to_wedge g) (EList g).

Lemma g2wedgelist_numE:
  forall g,
    Zlength (graph_to_wedgelist g) = numE g.
Proof.
  intros. unfold numE, graph_to_wedgelist.
  rewrite Zlength_map. trivial.
Qed.

Lemma NoDup_g2wedgelist:
  forall g, NoDup (graph_to_wedgelist g).
Proof.
intros. apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective; intros. inversion H. auto. apply NoDup_EList.
Qed.

Lemma g2wedgelist_evalid:
  forall g w, In w (graph_to_wedgelist g) -> evalid g (snd w).
Proof.
intros. apply list_in_map_inv in H. destruct H; destruct H.
apply EList_evalid in H0. unfold edge_to_wedge in H. inversion H. simpl. auto.
Qed.

Lemma sound_g2wedgelist_repable:
  forall g w, In w (graph_to_wedgelist g) -> sound_weighted_edge_graph g -> 
    Int.min_signed <= fst w <= Int.max_signed /\
            Int.min_signed <= fst (snd w) <= Int.max_signed /\
            Int.min_signed <= snd (snd w) <= Int.max_signed.
Proof.
intros. unfold graph_to_wedgelist in H.
apply list_in_map_inv in H. unfold edge_to_wedge in H. destruct H; destruct H.
destruct H0 as [? [? [? [? ?]]]].
subst w; simpl. split. apply H3. apply EList_evalid in H1; auto.
apply EList_evalid in H1. replace (fst x) with (src g x). replace (snd x) with (dst g x).
apply H2 in H1. destruct H1. unfold vertex_valid in H0. apply H0 in H. apply H0 in H1.
simpl. set (i:=Int.min_signed); compute in i; subst i.
split; lia.
apply H5; auto. apply H4; auto.
Qed.

(*******************SPECIFIC TYPES OF GRAPHS********************)
(*Example of a WEdgeListGraph (returned by init_empty_graph*)
Definition empty_WEdgeListGraph : WEdgeListGraph :=
  (empty_labeledgraph (fun e => fst e) (fun e => snd e) (tt: LV) (0: LE) (tt: LG)).

(* Okay, so you have an empty LabeledGraph above. 
   Now we'll use that to construct a relevant 
   empty GeneralGraph.
 *)

(* First we need an instance to show that such an 
   empty LabeledGraph would satisfy the soundness condition
   of the GeneralGraph. 
 *)
Definition empty_WEdgeListGraph_finite:
  FiniteGraph empty_WEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Instance Fin_empty_WEdgeListGraph:
  Fin empty_WEdgeListGraph.
Proof.
  constructor.
  apply empty_WEdgeListGraph_finite.
Qed.

(* Next we can build an empty GeneralGraph 
   using the two pieces above
 *)
Definition empty_FiniteWEdgeListGraph : FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
                      (WEdgeListGraph_LabeledGraph empty_WEdgeListGraph) Fin_empty_WEdgeListGraph.

(* and now a quick fact about the new GeneralGraph *)
Definition empty_FiniteWEdgeListGraph_finite:
  FiniteGraph empty_FiniteWEdgeListGraph.
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split; intros; simpl.
apply NoDup_nil. reflexivity. apply NoDup_nil. reflexivity.
Qed.

Lemma empty_WEdgeListGraph_sound:
  sound_weighted_edge_graph empty_WEdgeListGraph.
Proof.
  repeat split; contradiction.
Qed.

(* Tada, these are all cleaner! *)
Lemma empty_WEdgeListGraph_VList: VList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold VList.
  destruct finiteV.
  destruct a.
  unfold proj1_sig.
  destruct x; [trivial | exfalso].
  assert (In v (v::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Lemma empty_WEdgeListGraph_EList: EList empty_FiniteWEdgeListGraph = nil.
Proof.
  unfold EList.
  destruct finiteE.
  destruct a.
  unfold proj1_sig. 
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply i in H.
  contradiction.
Qed.

Corollary empty_WEdgeListGraph_numV: numV empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numV. rewrite empty_WEdgeListGraph_VList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_numE: numE empty_FiniteWEdgeListGraph = 0.
Proof.
unfold numE. rewrite empty_WEdgeListGraph_EList. apply Zlength_nil.
Qed.

Corollary empty_WEdgeListGraph_graph_to_wedgelist:
  graph_to_wedgelist empty_FiniteWEdgeListGraph = nil.
Proof.
unfold graph_to_wedgelist. rewrite empty_WEdgeListGraph_EList. reflexivity.
Qed.

(**********Edgeless graph with V vertices*************)
(*Built off empty WEdgelessGraph*)
(*This is a really roundabout way...*)
(*Skipping an arbitrary list of vertices, because we need NoDup, and our design forbids the skipping of vertices anyway *)

Definition Zseq (z: Z) : list Z :=
map Z.of_nat (seq 0%nat (Z.to_nat z)).

Lemma Zseq_NoDup:
forall z, NoDup (Zseq z).
Proof.
unfold Zseq; intros. destruct z; simpl; try apply NoDup_nil.
apply FinFun.Injective_map_NoDup.
unfold FinFun.Injective. apply Nat2Z.inj.
apply seq_NoDup.
Qed.

Lemma Zseq_In:
forall z x, In x (Zseq z) <-> 0 <= x < z.
Proof.
intros; unfold Zseq; simpl; split; intros.
+ destruct x; destruct z; try inversion H.
  lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H. rewrite in_seq in H0. lia.
  apply Coqlib.list_in_map_inv in H. destruct H. destruct H.
  assert (Z.neg p < 0) by (apply Pos2Z.neg_is_neg). assert (0 <= Z.of_nat x) by (apply Nat2Z.is_nonneg). lia.
+ destruct x; destruct z; try lia.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p))) 0%nat). rewrite in_seq.
  simpl. lia. rewrite <- positive_nat_Z.
  apply (in_map Z.of_nat (seq 0 (Z.to_nat (Z.pos p0))) (Pos.to_nat p)). rewrite in_seq. lia.
Qed.

Corollary Zseq_Zlength:
forall z, 0 <= z -> Zlength (Zseq z) = z.
Proof.
intros. unfold Zseq. rewrite (Zlength_map nat Z Z.of_nat (seq 0 (Z.to_nat z))).
rewrite Zlength_correct. rewrite seq_length.
apply Z2Nat.id. lia.
Qed.

Definition edgeless_WEdgeLGraph (z: Z): WEdgeListGraph :=
@Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG
  (@Build_PreGraph VType EType V_EqDec E_EqDec (fun v => 0 <= v < z) (fun e => False) fst snd)
  (fun v => tt) (fun e => 0) tt.

Instance Fin_edgeless_WEdgeLGraph (z: Z):
  Fin (edgeless_WEdgeLGraph z).
Proof.
constructor. constructor; unfold EnumEnsembles.Enumerable.
exists (Zseq z); split. apply Zseq_NoDup.
unfold edgeless_WEdgeLGraph. simpl. intros. apply Zseq_In.
exists nil. simpl. split. apply NoDup_nil. intros; split; intros; auto.
Qed.

Definition edgeless_WEdgeGraph (z: Z): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (edgeless_WEdgeLGraph z)) (Fin_edgeless_WEdgeLGraph z).

Lemma edgeless_WEdgeGraph_vvalid:
forall v k, 0 <= k < v <-> vvalid (edgeless_WEdgeGraph v) k.
Proof.
simpl. intros; split; intros; auto.
Qed.

Lemma edgeless_WEdgeGraph_Permutation:
forall v, Permutation (VList (edgeless_WEdgeGraph v)) (Zseq v).
Proof.
intros. apply NoDup_Permutation. apply NoDup_VList. apply Zseq_NoDup.
intros; rewrite Zseq_In. unfold VList; destruct finiteV; simpl.
destruct a. rewrite H0. rewrite edgeless_WEdgeGraph_vvalid. split; auto.
Qed.

Lemma Permutation_Zlength:
forall {A: Type} (l l': list A), Permutation l l' -> Zlength l = Zlength l'.
Proof.
intros. assert (length l = length l'). apply Permutation_length. apply H.
repeat rewrite Zlength_correct. rewrite H0. auto.
Qed.

Lemma edgeless_WEdgeGraph_numV:
forall v, 0 <= v -> numV (edgeless_WEdgeGraph v) = v.
Proof.
unfold numV. intros.
assert (Zlength (VList (edgeless_WEdgeGraph v)) = Zlength (Zseq v)).
apply Permutation_Zlength. apply edgeless_WEdgeGraph_Permutation.
rewrite H0. rewrite Zseq_Zlength. auto. apply H.
Qed.

Lemma edgeless_WEdgeGraph_evalid:
forall v e, ~ evalid (edgeless_WEdgeGraph v) e.
Proof.
intros. unfold edgeless_WEdgeGraph; simpl. auto.
Qed.

Lemma edgeless_WEdgeGraph_EList:
forall v, EList (edgeless_WEdgeGraph v) = nil.
Proof.
  intros. unfold edgeless_WEdgeGraph, EList.
  destruct finiteE. simpl in *.
  destruct a.
  destruct x; [trivial | exfalso].
  assert (In e (e::x)) by (apply in_eq).
  apply (H0 e). apply H1.
Qed.

Corollary edgeless_WEdgeGraph_numE:
forall v, numE (edgeless_WEdgeGraph v) = 0.
Proof.
unfold numE. intros. rewrite edgeless_WEdgeGraph_EList. apply Zlength_nil.
Qed.

Lemma edgeless_WEdgeGraph_sound:
  forall z, 0 <= z <= Int.max_signed -> sound_weighted_edge_graph (edgeless_WEdgeGraph z).
Proof.
intros. split. unfold vertex_valid; intros. apply edgeless_WEdgeGraph_vvalid in H0. lia.
split. unfold edge_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_WEdgeGraph_EList in H0. contradiction.
split. unfold weight_valid; intros. rewrite <- EList_evalid in H0. rewrite edgeless_WEdgeGraph_EList in H0. contradiction.
split. unfold src_edge; intros. simpl; auto.
split.
Qed.

Corollary graph_to_wedgelist_edgeless_WEdgeGraph:
forall v, graph_to_wedgelist (edgeless_WEdgeGraph v) = nil.
Proof.
unfold graph_to_wedgelist; intros. rewrite edgeless_WEdgeGraph_EList. auto.
Qed.

Lemma uforest_edgeless_WEdgeGraph:
forall z, sound_uforest (edgeless_WEdgeGraph z).
Proof.
split; intros.
(*no self-loops*)
apply edgeless_WEdgeGraph_evalid in H; contradiction.
split; intros.
(*only one edge between two vertices*)
destruct H. destruct H. destruct H.
apply edgeless_WEdgeGraph_evalid in H; contradiction.
(*no rubbish edges*)
split; intros.
apply edgeless_WEdgeGraph_evalid in H; contradiction.
(*main forest definition*)
unfold uforest; intros. destruct H0 as [? [? ?]].
destruct p1. inversion H3. destruct p1.
inversion H3. inversion H4. subst u; subst v.
destruct H2 as [? [? ?]]. destruct p2. inversion H5.
destruct p2. inversion H5. subst v. auto.
destruct H2. destruct H2. destruct H2. destruct H2. simpl in H2. contradiction.
destruct H0. destruct H0. destruct H0. destruct H0. simpl in H0. contradiction.
Qed.

(***********ADDING A SINGLE EDGE************)

(*Trivial lemmas to make life simple*)
(*These should probably be in FiniteGraph*)

(*These are specific here because it needs Z.eq_dec*)
Lemma VList_In_dec:
  forall (g: FiniteWEdgeListGraph) v, In v (VList g) \/ ~ In v (VList g).
Proof.
intros. destruct (in_dec Z.eq_dec v (VList g)); [left; auto | right; auto].
Qed.

Lemma EList_In_dec:
  forall (g: FiniteWEdgeListGraph) e, In e (EList g) \/ ~ In e (EList g).
Proof.
intros. destruct (in_dec E_EqDec e (EList g)); [left; auto | right; auto].
Qed.

Corollary FiniteWEdgeListGraph_vvalid_dec:
  forall (g: FiniteWEdgeListGraph) v, vvalid g v \/ ~ vvalid g v.
Proof.
  intros. destruct (VList_In_dec g v); [ left; rewrite <- VList_vvalid; apply H | right; rewrite <- VList_vvalid; apply H].
Qed.

Corollary FiniteWEdgeListGraph_evalid_dec:
  forall (g: FiniteWEdgeListGraph) e, evalid g e \/ ~ evalid g e.
Proof.
  intros. destruct (EList_In_dec g e); [ left; rewrite <- EList_evalid; apply H | right; rewrite <- EList_evalid; apply H].
Qed.

(**Adding is necessary for the kruskal algorithm**)
Definition WEdgeListGraph_adde (g: WEdgeListGraph) (e: EType) (w: LE):=
  labeledgraph_add_edge g e (fst e) (snd e) w.

Instance Fin_WEdgeListGraph_adde (g: FiniteWEdgeListGraph) (e: EType) (w: LE) :
  Fin (WEdgeListGraph_adde g e w).
Proof.
unfold WEdgeListGraph_adde. unfold labeledgraph_add_edge.
constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold addValidFunc.
destruct (in_dec E_EqDec e (EList g)).
(*case e already inside*)
exists (EList g). split. apply NoDup_EList. intros; split; intros. left. apply EList_evalid in H; auto.
destruct H. apply EList_evalid; auto. rewrite H; auto.
(*case e not inside*)
exists (e::(EList g)). split. apply NoDup_cons. auto. apply NoDup_EList.
intros; split; intros.
destruct H. right; rewrite H; auto. left; rewrite <- EList_evalid; apply H.
destruct H. rewrite <- EList_evalid in H. apply in_cons. apply H.
rewrite H. simpl. left; auto.
Qed.

Definition FiniteWEdgeListGraph_adde (g: FiniteWEdgeListGraph) (e: EType) (w: LE): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (WEdgeListGraph_adde g e w))
    (Fin_WEdgeListGraph_adde g e w).

Lemma FiniteWEdgeListGraph_adde_vvalid:
  forall (g: FiniteWEdgeListGraph)  e w v, vvalid g v <-> vvalid (FiniteWEdgeListGraph_adde g e w) v.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. split; auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_numV:
  forall (g: FiniteWEdgeListGraph)  e w, numV (FiniteWEdgeListGraph_adde g e w) = numV g.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. unfold numV. simpl. unfold VList.
destruct finiteV. destruct finiteV. simpl. simpl in a.
destruct a. destruct a0. assert (Permutation x x0). apply NoDup_Permutation; auto.
intros. rewrite H0. rewrite H2. split; auto.
apply Permutation_Zlength. auto.
Qed.

(*should add an EList1 where e is already in g, but it's not necessary atm*)
Lemma FiniteWEdgeListGraph_adde_EList2:
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> Permutation (e::(EList g)) (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros.
unfold FiniteWEdgeListGraph_adde. simpl. unfold pregraph_add_edge.
set (l:=e::EList g). unfold EList. destruct finiteE. simpl.
destruct a. unfold addValidFunc in H1. simpl in H1.
apply NoDup_Permutation. unfold l. apply NoDup_cons. rewrite EList_evalid. auto. apply NoDup_EList. auto.
intros; split; intros. apply H1. destruct H2. right; auto. left. rewrite <- EList_evalid. apply H2.
apply H1 in H2. unfold l. destruct H2.
right. apply EList_evalid. auto.
left. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_EList2':
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> Permutation ((EList g)+::e) (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. pose proof (FiniteWEdgeListGraph_adde_EList2 g e w).
apply (Permutation_trans (l:=EList g +:: e) (l':=e::EList g)).
apply Permutation_app_comm. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_EList_in:
  forall (g: FiniteWEdgeListGraph) e w e', In e' (EList g) -> In e' (EList (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold EList. destruct finiteE. simpl. destruct a.
unfold FiniteWEdgeListGraph_adde in H1. simpl in H1. unfold addValidFunc in H1. apply H1.
left. apply EList_evalid in H. apply H.
Qed.

Lemma adde_elabel1:
  forall (g: FiniteWEdgeListGraph) e w, elabel (FiniteWEdgeListGraph_adde g e w) e = w.
Proof.
intros. simpl. unfold update_elabel. unfold equiv_dec. destruct E_EqDec. auto.
unfold complement in c. unfold equiv in c. contradiction.
Qed.

Lemma adde_elabel2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> elabel (FiniteWEdgeListGraph_adde g e w) e' = elabel g e'.
Proof.
intros. simpl. unfold update_elabel. unfold equiv_dec. destruct E_EqDec.
contradiction. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid1:
  forall (g: FiniteWEdgeListGraph) e w, evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. right; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid2:
  forall (g: FiniteWEdgeListGraph) e w e', evalid g e' -> evalid (FiniteWEdgeListGraph_adde g e w) e'.
Proof.
intros. unfold FiniteWEdgeListGraph_adde. simpl. unfold addValidFunc. left; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid2':
  forall (g: FiniteWEdgeListGraph) e w e', e' <> e -> evalid (FiniteWEdgeListGraph_adde g e w) e' -> evalid g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. destruct H0. auto. contradiction.
Qed.

Lemma FiniteWEdgeListGraph_adde_evalid_or:
  forall (g: FiniteWEdgeListGraph) e w e', evalid (FiniteWEdgeListGraph_adde g e w) e' -> (evalid g e' \/ e' = e).
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc. intros. apply H.
Qed.

Lemma FiniteWEdgeListGraph_adde_src1:
  forall (g: FiniteWEdgeListGraph) e w, src (FiniteWEdgeListGraph_adde g e w) e = fst e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Lemma FiniteWEdgeListGraph_adde_dst1:
  forall (g: FiniteWEdgeListGraph) e w, dst (FiniteWEdgeListGraph_adde g e w) e = snd e.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc; unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct E_EqDec. auto. unfold complement, equiv in c; contradiction.
Qed.

Corollary FiniteWEdgeListGraph_adde_src1':
  forall (g: FiniteWEdgeListGraph) u v w, src (FiniteWEdgeListGraph_adde g (u,v) w) (u,v) = u.
Proof. intros. apply FiniteWEdgeListGraph_adde_src1. Qed.

Lemma FiniteWEdgeListGraph_adde_dst1':
  forall (g: FiniteWEdgeListGraph) u v w, dst (FiniteWEdgeListGraph_adde g (u,v) w) (u,v) = v.
Proof. intros. apply FiniteWEdgeListGraph_adde_dst1. Qed.

Lemma FiniteWEdgeListGraph_adde_src2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> src (FiniteWEdgeListGraph_adde g e w) e' = src g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e0; contradiction. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_dst2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> dst (FiniteWEdgeListGraph_adde g e w) e' = dst g e'.
Proof.
unfold FiniteWEdgeListGraph_adde; simpl; unfold addValidFunc, updateEdgeFunc; intros.
unfold equiv_dec. destruct E_EqDec. unfold equiv in e0; contradiction. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_strong_evalid1:
  forall (g: FiniteWEdgeListGraph) e w,
  vvalid g (fst e) -> vvalid g (snd e) ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e.
Proof.
intros. split. apply FiniteWEdgeListGraph_adde_evalid1.
split; apply FiniteWEdgeListGraph_adde_vvalid.
rewrite FiniteWEdgeListGraph_adde_src1. auto.
rewrite FiniteWEdgeListGraph_adde_dst1. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_strong_evalid1':
  forall (g: FiniteWEdgeListGraph) u v w,
  vvalid g u -> vvalid g v ->
  strong_evalid (FiniteWEdgeListGraph_adde g (u,v) w) (u,v).
Proof.
intros. apply FiniteWEdgeListGraph_adde_strong_evalid1; simpl; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_strong_evalid2:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' ->
  strong_evalid g e' ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e'.
Proof.
intros. split. apply FiniteWEdgeListGraph_adde_evalid2. apply H0.
do 2 rewrite <- FiniteWEdgeListGraph_adde_vvalid. split.
rewrite FiniteWEdgeListGraph_adde_src2. apply H0. auto.
rewrite FiniteWEdgeListGraph_adde_dst2. apply H0. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_strong_evalid_rev:
  forall (g: FiniteWEdgeListGraph) e w e', e <> e' ->
  strong_evalid (FiniteWEdgeListGraph_adde g e w) e' -> strong_evalid g e'.
Proof.
intros. destruct H0. destruct H1.
split. apply FiniteWEdgeListGraph_adde_evalid2' in H0; auto.
split. rewrite FiniteWEdgeListGraph_adde_src2 in H1; auto.
rewrite FiniteWEdgeListGraph_adde_dst2 in H2; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_g2wedgelist_1:
  forall (g: FiniteWEdgeListGraph) e w, In (w, e) (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. unfold edge_to_wedge.
replace (w, e) with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e).
apply in_map. apply EList_evalid. apply FiniteWEdgeListGraph_adde_evalid1.
unfold edge_to_wedge. rewrite adde_elabel1. auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_e2w:
forall (g: FiniteWEdgeListGraph) e w e', e <> e' -> edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e' = edge_to_wedge g e'.
Proof.
intros. unfold edge_to_wedge; simpl. unfold update_elabel; simpl.
unfold equiv_dec. destruct E_EqDec. contradiction. auto.
Qed.

Corollary FiniteWEdgeListGraph_adde_g2wedgelist_2:
  forall (g: FiniteWEdgeListGraph) e w e', e<>e' -> evalid g e' -> In (elabel g e', e') (graph_to_wedgelist (FiniteWEdgeListGraph_adde g e w)).
Proof.
intros. unfold graph_to_wedgelist. replace (elabel g e', e') with (edge_to_wedge (FiniteWEdgeListGraph_adde g e w) e').
apply in_map. apply EList_evalid. apply FiniteWEdgeListGraph_adde_evalid2. auto.
apply FiniteWEdgeListGraph_adde_e2w; auto.
Qed.

Lemma FiniteWEdgeListGraph_adde_numE:
  forall (g: FiniteWEdgeListGraph) e w, ~ evalid g e -> numE (FiniteWEdgeListGraph_adde g e w) = numE g + 1.
Proof.
intros. unfold numE.
pose proof (FiniteWEdgeListGraph_adde_EList2 g e w H).
rewrite <- (Permutation_Zlength _ _ H0). apply Zlength_cons.
Qed.

Lemma FiniteWEdgeListGraph_adde_sound:
  forall (g: FiniteWEdgeListGraph) e w, sound_weighted_edge_graph g ->
    vvalid g (fst e) -> vvalid g (snd e) -> Int.min_signed <= w <= Int.max_signed ->
    sound_weighted_edge_graph (FiniteWEdgeListGraph_adde g e w).
Proof.
intros. split.
unfold vertex_valid; intros. apply H. simpl in H3. apply H3.
split. unfold edge_valid; intros. simpl in H3. destruct H3.
simpl. unfold updateEdgeFunc. unfold equiv_dec.
destruct E_EqDec; [split; auto | apply H; apply H3].
subst e0. simpl; unfold updateEdgeFunc.
unfold equiv_dec. destruct E_EqDec. split; auto. unfold complement, equiv in c; contradiction.
split. unfold weight_valid; intros. simpl in H3. unfold addValidFunc in H3.
simpl. unfold update_elabel. unfold equiv_dec.
destruct (E_EqDec e e0). apply H2.
destruct H3. apply H. apply H3. rewrite H3 in c. unfold complement in c.
assert (equiv e e). apply Equivalence.equiv_reflexive_obligation_1. contradiction.
split. unfold src_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H. unfold addValidFunc in H3. destruct H3. auto. unfold complement, equiv in c. subst e0; contradiction.
unfold dst_edge; simpl. unfold updateEdgeFunc. intros.
unfold equiv_dec. destruct (E_EqDec e e0). unfold equiv in e1; rewrite e1; auto.
apply H. unfold addValidFunc in H3. destruct H3. auto. unfold complement, equiv in c. subst e0; contradiction.
Qed.

(*****************************CONNECTEDNESS*************************)

Lemma sound_adj_edge_form:
forall (g: FiniteWEdgeListGraph) e u v, sound_weighted_edge_graph g -> adj_edge g e u v -> (e = (u,v) \/ e = (v,u)).
Proof.
intros. destruct H0. rewrite <- sound_src in H1. rewrite <- sound_dst in H1.
rewrite (surjective_pairing e). destruct H1; destruct H1; subst u; subst v; auto.
auto. apply H0. auto. apply H0.
Qed.

Lemma adde_adj_edge:
forall (g: FiniteWEdgeListGraph) e w e' u v,
  sound_weighted_edge_graph g ->
  adj_edge g e' u v -> adj_edge (FiniteWEdgeListGraph_adde g e w) e' u v.
Proof.
unfold adj_edge; intros. destruct (E_EqDec e e').
(*e=e'*)
unfold equiv in e0. subst e'. split.
apply FiniteWEdgeListGraph_adde_strong_evalid1.
replace (fst e) with (src g e). apply H0. apply H. apply H0.
replace (snd e) with (dst g e). apply H0. apply H. apply H0.
rewrite FiniteWEdgeListGraph_adde_src1.
rewrite FiniteWEdgeListGraph_adde_dst1.
destruct H0. destruct H0.
rewrite (sound_src g e); auto. rewrite (sound_dst g e); auto.
(*e<>e'*)
unfold complement, equiv in c. destruct H0. split.
apply FiniteWEdgeListGraph_adde_strong_evalid2; auto.
rewrite FiniteWEdgeListGraph_adde_src2; auto.
rewrite FiniteWEdgeListGraph_adde_dst2; auto.
Qed.

Lemma adde_adj_edge_rev:
forall (g: FiniteWEdgeListGraph) e w e' u v,
  sound_weighted_edge_graph g -> e <> e' ->
  adj_edge (FiniteWEdgeListGraph_adde g e w) e' u v -> adj_edge g e' u v .
Proof.
unfold adj_edge; intros. destruct H1.
split.
apply FiniteWEdgeListGraph_adde_strong_evalid_rev in H1; auto.
rewrite FiniteWEdgeListGraph_adde_src2 in H2; auto.
rewrite FiniteWEdgeListGraph_adde_dst2 in H2; auto.
Qed.

Lemma adde_valid_upath:
forall (g: FiniteWEdgeListGraph) e w p,
  sound_weighted_edge_graph g ->
  valid_upath g p -> valid_upath (FiniteWEdgeListGraph_adde g e w) p.
Proof.
induction p; intros. auto.
destruct p. auto.
split. destruct H0. destruct H0. exists x.
apply adde_adj_edge; auto.
apply IHp. auto. apply H0.
Qed.

Lemma adde_connected_by_path:
forall (g: FiniteWEdgeListGraph) e w p u v,
  sound_weighted_edge_graph g -> connected_by_path g p u v ->
  connected_by_path (FiniteWEdgeListGraph_adde g e w) p u v.
Proof.
unfold connected_by_path; intros.
split. apply adde_valid_upath. auto.
apply H0. apply H0.
Qed.

Corollary adde_connected:
forall (g: FiniteWEdgeListGraph) e w u v,
  sound_weighted_edge_graph g ->
  connected g u v -> connected (FiniteWEdgeListGraph_adde g e w) u v.
Proof.
intros. destruct H0 as [p ?]. exists p.
apply adde_connected_by_path; auto.
Qed.

Lemma adde_fits_upath:
forall (g: FiniteWEdgeListGraph) e w p l,
sound_weighted_edge_graph g ->
fits_upath g l p -> fits_upath (FiniteWEdgeListGraph_adde g e w) l p.
Proof.
induction p; intros. destruct l; auto.
destruct l. auto. destruct p. auto.
split. destruct H0. apply adde_adj_edge; auto.
apply IHp. apply H. apply fits_upath_cons in H0. apply H0.
Qed.

(*Not used*)
Lemma adde_connected_e:
forall (g:FiniteWEdgeListGraph) e w,
  sound_weighted_edge_graph g -> vvalid g (fst e) -> vvalid g (snd e) ->
  connected (FiniteWEdgeListGraph_adde g e w) (fst e) (snd e).
Proof.
intros. exists ((fst e)::(snd e)::nil). split. 2: auto.
split. exists e. split. apply FiniteWEdgeListGraph_adde_strong_evalid1; auto.
rewrite FiniteWEdgeListGraph_adde_src1, FiniteWEdgeListGraph_adde_dst1. left; auto.
simpl; auto.
Qed.

Lemma adde_fits_upath':
forall (g: FiniteWEdgeListGraph) e w p l,
fits_upath (FiniteWEdgeListGraph_adde g e w) l p ->
~ In e l ->
fits_upath g l p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; auto.
destruct l. auto.
assert (Heq_e: e <> e0). unfold not; intros. assert (In e (e0::l)). left; rewrite H1; auto. contradiction.
assert (HIn_e: ~ In e l). unfold not; intros. assert (In e (e0::l)). right; auto. contradiction.
clear H0.
destruct H. split. destruct H. destruct H. split. split.
simpl in H. unfold addValidFunc in H. destruct H. apply H. symmetry in H. contradiction.
simpl in H2. unfold updateEdgeFunc in H2. unfold equiv_dec in H2. destruct (E_EqDec e e0).
unfold equiv in e1; contradiction. apply H2.
simpl in H1. unfold updateEdgeFunc in H1. unfold equiv_dec in H1. destruct (E_EqDec e e0).
unfold equiv in e1; contradiction. apply H1.
apply IHp; auto.
Qed.

Lemma adde_unaffected:
forall (g: FiniteWEdgeListGraph) e w p, valid_upath (FiniteWEdgeListGraph_adde g e w) p
  -> (exists l, fits_upath g l p /\ ~ In e l) -> valid_upath g p.
Proof.
intros. destruct H0 as [l ?].
apply valid_upath_exists_list_edges'.
intros. apply (FiniteWEdgeListGraph_adde_vvalid g e w).
apply (valid_upath_vvalid _ _ v) in H. auto. auto.
exists l. destruct H0; auto.
Qed.

Definition bridge (g: FiniteWEdgeListGraph) e u v :=
forall p l, connected_by_path g p u v -> fits_upath g l p -> In e l.

(*Not used*)
Lemma adde_bridge': (*anything that joins u v must contain (u,v)*)
forall (g: FiniteWEdgeListGraph) u v w,
~ connected g u v -> bridge (FiniteWEdgeListGraph_adde g (u,v) w) (u,v) u v.
Proof.
unfold bridge; intros. destruct (in_dec E_EqDec (u,v) l). auto.
(*come to a contradiction that connected g u v*)
assert (connected g u v). exists p.
destruct H0. split. 2: auto.
apply (adde_unaffected g (u,v) w). apply H0.
exists l; split. apply (adde_fits_upath' g (u,v) w); auto. auto.
contradiction.
Qed.

Lemma adde_connected_through_bridge1:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
vvalid g u -> vvalid g v ->
connected g a u -> connected g v b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros. apply (adde_connected g (u,v) w) in H2; auto. apply (adde_connected g (u,v) w) in H3; auto.
destruct H2 as [x [? [? ?]]]. destruct H3 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (FiniteWEdgeListGraph_adde_strong_evalid1 g (u,v) w); auto.
left. split. rewrite FiniteWEdgeListGraph_adde_src1; auto. rewrite FiniteWEdgeListGraph_adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma adde_connected_through_bridge2:
forall (g: FiniteWEdgeListGraph) u v w a b,
sound_weighted_edge_graph g ->
vvalid g u -> vvalid g v ->
connected g a v -> connected g u b
-> connected (FiniteWEdgeListGraph_adde g (u,v) w) a b.
Proof.
intros. apply (adde_connected g (u,v) w) in H2; auto. apply (adde_connected g (u,v) w) in H3; auto.
destruct H2 as [x [? [? ?]]]. destruct H3 as [x0 [? [? ?]]].
exists (x++x0). split.
apply valid_upath_app; auto.
rewrite H5; rewrite H6. unfold adjacent_err. exists (u,v). split.
apply (FiniteWEdgeListGraph_adde_strong_evalid1 g (u,v) w); auto.
right. split. rewrite FiniteWEdgeListGraph_adde_src1; auto. rewrite FiniteWEdgeListGraph_adde_dst1; auto.
split. apply hd_error_app; auto. apply last_err_app; auto.
Qed.

Lemma fits_upath_vertex_src_In:
forall (g: FiniteWEdgeListGraph) p l e, fits_upath g l p -> In e l -> In (src g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1. left; symmetry; apply H1.
right. left. symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.

Lemma fits_upath_vertex_dst_In:
forall (g: FiniteWEdgeListGraph) p l e, fits_upath g l p -> In e l -> In (dst g e) p.
Proof.
induction p; intros. destruct l; auto.
destruct p. destruct l; simpl in H; contradiction.
destruct l. contradiction. destruct H0.
subst e0. destruct H. destruct H. destruct H1.
right. left. symmetry; apply H1.
left; symmetry; apply H1.
right. apply (IHp l). apply H. auto.
Qed.

(*****************************REMOVE EDGES****************************)

Definition WEdgeListGraph_eremove (g: WEdgeListGraph) (e: EType) :=
  @Build_LabeledGraph VType EType V_EqDec E_EqDec LV LE LG (pregraph_remove_edge g e)
  (vlabel g)
  (*(fun e0 => if eq_dec e0 e then ? else elabel g e )*) (elabel g)
  (glabel g)
.

Instance Fin_WEdgeListGraph_eremove (g: FiniteWEdgeListGraph) (e: EType) :
  Fin (WEdgeListGraph_eremove g e).
Proof.
unfold WEdgeListGraph_eremove. unfold pregraph_remove_edge.
constructor. constructor; unfold EnumEnsembles.Enumerable; simpl.
exists (VList g). split. apply NoDup_VList. apply VList_vvalid.
(*edge*)
unfold removeValidFunc.
destruct (in_dec E_EqDec e (EList g)).
(*case e already inside*)
exists (remove E_EqDec e (EList (g))). split.
apply nodup_remove_nodup. apply NoDup_EList.
intros. rewrite remove_In_iff. rewrite EList_evalid. split; auto.
(*case e not inside*)
exists (EList g). split. apply NoDup_EList.
intros; split; intros. split. apply EList_evalid in H; auto.
unfold not; intros; subst x. contradiction.
destruct H. apply EList_evalid. auto.
Qed.

Definition FiniteWEdgeListGraph_eremove (g: FiniteWEdgeListGraph) (e: EType): FiniteWEdgeListGraph :=
  @Build_GeneralGraph VType EType V_EqDec E_EqDec LV LE LG Fin
    (WEdgeListGraph_LabeledGraph (WEdgeListGraph_eremove g e))
    (Fin_WEdgeListGraph_eremove g e).

Lemma eremove_vvalid:
forall (g: FiniteWEdgeListGraph) (e: EType) v, vvalid g v <-> vvalid (FiniteWEdgeListGraph_eremove g e) v.
Proof.
simpl. intros; split; auto.
Qed.

(*Don't bother with defining what happens when e isn't inside*)
Lemma eremove_evalid1:
forall (g: FiniteWEdgeListGraph) e, ~ evalid (FiniteWEdgeListGraph_eremove g e) e.
Proof.
simpl. unfold removeValidFunc, not; intros. destruct H. contradiction.
Qed.

Lemma eremove_evalid2:
forall (g: FiniteWEdgeListGraph) e e', e' <> e -> evalid g e' -> evalid (FiniteWEdgeListGraph_eremove g e) e'.
Proof.
simpl. intros; split; auto.
Qed.

Lemma eremove_sound:
forall (g: FiniteWEdgeListGraph) e, sound_weighted_edge_graph g -> sound_weighted_edge_graph (FiniteWEdgeListGraph_eremove g e).
Proof.
intros. destruct H as [? [? [? [? ?]]]]. split. apply H.
split. unfold edge_valid; simpl; unfold removeValidFunc.
intros. destruct H4. apply H0; auto.
split. unfold weight_valid; simpl; unfold removeValidFunc. intros.
destruct H4. apply H1; auto.
split. unfold src_edge; simpl; unfold removeValidFunc. intros. apply H2. apply H4.
unfold dst_edge; simpl; unfold removeValidFunc. intros. apply H3. apply H4.
Qed.

(*
Lemma eremove_adjacent: (*only if e is the only edge*)
forall (g: FiniteWEdgeListGraph) e, ~ adjacent (FiniteWEdgeListGraph_eremove g e) (src g e) (dst g e).
*)

(*****************************PARTIAL LGRAPH AND MSF**********************)
(*These should be abstracted, but we can deal with it after the kruskal proof is done*)

Definition preserve_vlabel (g1 g2: FiniteWEdgeListGraph) :=
  forall v, vvalid g1 v -> vlabel g1 v = vlabel g2 v.

Definition preserve_elabel (g1 g2: FiniteWEdgeListGraph) :=
  forall e, evalid g1 e -> elabel g1 e = elabel g2 e.

Definition is_partial_lgraph
           (g1 g2: FiniteWEdgeListGraph) :=
  is_partial_graph g1 g2 /\
  preserve_vlabel g1 g2 /\ preserve_elabel g1 g2.

Lemma is_partial_lgraph_refl: forall g,
    is_partial_lgraph g g.
Proof.
intros. split. apply is_partial_graph_refl.
unfold preserve_vlabel, preserve_elabel. split; auto.
Qed.

Lemma is_partial_lgraph_trans: forall g1 g2 g3,
    is_partial_lgraph g1 g2 -> is_partial_lgraph g2 g3 -> is_partial_lgraph g1 g3.
Proof.
  intros. split. apply (is_partial_graph_trans g1 g2 g3). apply H. apply H0.
  destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
  unfold preserve_vlabel, preserve_elabel in *. split; intros.
  rewrite H1, H3; auto. apply H; auto.
  rewrite H2, H4; auto. apply H; auto.
Qed.

Lemma is_partial_lgraph_adjacent:
forall g1 g2 u v, is_partial_lgraph g1 g2 -> adjacent g1 u v -> adjacent g2 u v.
Proof.
intros. destruct H0. destruct H0. destruct H0. destruct H2.
destruct H. destruct H4. destruct H. destruct H6. destruct H7.
exists x. split. split. apply H6; auto.
rewrite <- H7; auto. rewrite <- H8; auto.
rewrite <- H7; auto. rewrite <- H8; auto.
Qed.

Lemma is_partial_lgraph_valid_upath:
forall g1 g2 p, is_partial_lgraph g1 g2 -> valid_upath g1 p -> valid_upath g2 p.
Proof.
intros. induction p. auto. destruct p. simpl. simpl in H0. apply H. apply H0.
destruct H0. split. apply (is_partial_lgraph_adjacent g1 g2); auto. auto.
Qed.

Lemma is_partial_lgraph_connected:
forall g1 g2, is_partial_lgraph g1 g2 ->
forall u v, connected g1 u v -> connected g2 u v.
Proof.
intros. destruct H0 as [p ?]. destruct H0.
exists p. split.
apply (is_partial_lgraph_valid_upath g1 g2); auto. auto.
Qed.

Lemma fits_upath_transfer':
forall p l (g1 g2: FiniteWEdgeListGraph), (forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) -> (forall e, evalid g1 e -> evalid g2 e -> src g1 e = src g2 e) ->
(forall e, evalid g1 e -> evalid g2 e -> dst g1 e = dst g2 e) -> (*this is not quite what I want, hm*)
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. auto. simpl in H3. contradiction.
destruct p. simpl in H3. contradiction.
destruct H3. split.
+ (*adjacent edge*)
  destruct H3. destruct H3. destruct H6. assert (evalid g2 e). apply H0. left. auto.
  split. split. apply H0. left; auto. split.
  apply H in H6. rewrite H1 in H6; auto.
  apply H in H7. rewrite H2 in H7; auto.
  rewrite H1 in H5; auto. rewrite H2 in H5; auto.
+ apply (IHp l g1 g2); auto. intros. apply H0. right; auto.
Qed.

Lemma fits_upath_transfer:
forall p l (g1 g2: FiniteWEdgeListGraph), sound_weighted_edge_graph g1 ->
sound_weighted_edge_graph g2 -> (forall v, vvalid g1 v <-> vvalid g2 v) ->
(forall e, In e l -> evalid g2 e) ->
fits_upath g1 l p -> fits_upath g2 l p.
Proof.
induction p; intros. destruct l. auto. apply H3.
destruct l. destruct p. simpl. auto. simpl in H3. contradiction.
destruct p. simpl in H3. contradiction.
destruct H3. split.
+ (*adjacent edge*)
  destruct H3. destruct H3. destruct H6. assert (evalid g2 e). apply H2. left. auto.
  unfold adj_edge. unfold strong_evalid.
  replace (src g1 e) with (fst e) in *. 2: apply sound_src; auto.
  replace (src g2 e) with (fst e) in *. 2: apply sound_src; auto.
  replace (dst g1 e) with (snd e) in *. 2: apply sound_dst; auto.
  replace (dst g2 e) with (snd e) in *. 2: apply sound_dst; auto.
  split. split. apply H2. left; auto. split.
  apply H1; auto. apply H1; auto. apply H5.
+ apply (IHp l g1 g2); auto. intros. apply H2. right; auto.
Qed.

(*on the issue of partial lgraph and soundness
Partial graph doesn't preserve that an edge is strong_evalid
So (src t1) could warp an edge, even if it was evalid. fst is not inbuilt into my wedgegraphs, so src t1 can do anything it likes
It'll satisfy spanning_uforest as well...
So the question is whether I need to account for the "warped" edges <- Yes I do, because their elabels still count
So I need either:
-spanning_uforest to preserve that every edge is strong evalid
-EList to return only strong_evalid values
-sum_DE to add only edges that are strong evalid
kruskal's returned msf preserves strong_evalid by edge_valid/sound_weighted_edge_graph
I need to assume the same for the other uforest

...Let's deal with this after we're done defining remove_edge
*)

Lemma fold_left_Zadd_diff_accum:
forall (l: list Z) (x y: Z), x <= y -> fold_left Z.add l x <= fold_left Z.add l y.
Proof.
induction l; intros. simpl; auto.
apply IHl. lia.
Qed.

Lemma fold_left_Zadd_comp:
forall (l1 l2: list Z), Zlength l1 = Zlength l2 -> (forall i, 0<=i<Zlength l1 -> Znth i l1 <= Znth i l2)
  -> (forall s, fold_left Z.add l1 s <= fold_left Z.add l2 s).
Proof.
induction l1; intros.
rewrite Zlength_nil in H. symmetry in H. apply Zlength_nil_inv in H. subst l2. lia.
destruct l2. rewrite Zlength_cons in H. rewrite Zlength_nil in H. pose proof (Zlength_nonneg l1). lia.
simpl. assert (a <= z). replace a with (Znth 0 (a::l1)). replace z with (Znth 0 (z::l2)).
apply H0. split. lia. rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia.
auto. auto.
apply (Z.le_trans _ (fold_left Z.add l1 (s + z)) _).
apply fold_left_Zadd_diff_accum. lia.
apply IHl1. do 2 rewrite Zlength_cons in H. lia.
intros. replace (Znth i l1) with (Znth (i+1) (a::l1)).
 replace (Znth i l2) with (Znth (i+1) (z::l2)). apply H0. rewrite Zlength_cons. lia.
all: rewrite (Znth_pos_cons (i+1)) by lia; rewrite Z.add_simpl_r; auto.
Qed.

Definition DEList (g: FiniteWEdgeListGraph): list LE :=
  map (elabel g) (EList g).

Definition sum_LE g : LE :=
  fold_left Z.add (DEList g) 0.

Definition labeled_spanning_uforest (t g: FiniteWEdgeListGraph) :=
  spanning_uforest t g /\
  preserve_vlabel t g /\ preserve_elabel t g.

Lemma spanning_uforest_edge_valid:
forall (t g: FiniteWEdgeListGraph), edge_valid g ->
labeled_spanning_uforest t g -> edge_valid t.
Proof.
unfold edge_valid; intros. destruct H0. destruct H0. destruct H3. apply H3 in H1. apply H1.
Qed.

Lemma spanning_uforest_sound:
forall (t g: FiniteWEdgeListGraph), sound_weighted_edge_graph g ->
labeled_spanning_uforest t g -> sound_weighted_edge_graph t.
Proof.
intros.
split. unfold vertex_valid; intros. apply H. apply H0. auto.
split. unfold edge_valid; intros. apply H0. auto.
split. unfold weight_valid; intros.
destruct H0. destruct H0. destruct H2. rewrite H4 by auto. apply H. apply H0. auto.
destruct H as [? [? [? [? ?]]]]. assert (edge_valid t). apply (spanning_uforest_edge_valid t g); auto.
split. unfold src_edge; intros. rewrite <- H3. apply H0.
auto. apply H5. auto. apply H0. auto.
unfold dst_edge; intros. rewrite <- H4. apply H0.
auto. apply H5. auto. apply H0. auto.
Qed.

Definition minimum_spanning_forest (t g: FiniteWEdgeListGraph) :=
 labeled_spanning_uforest t g /\
  forall (t': FiniteWEdgeListGraph), labeled_spanning_uforest t' g ->
    Z.le (sum_LE t) (sum_LE t').

(*The following are to let us reason about lists instead of graphs*)
Lemma sum_LE_equiv':
  forall (g: FiniteWEdgeListGraph) (l: list EType),
  Permutation (EList g) l -> sum_LE g = fold_left Z.add (map (elabel g) l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
apply Permutation_map. auto.
Qed.

Lemma sum_LE_equiv:
  forall (g: FiniteWEdgeListGraph) (l: list (LE*EType)),
  Permutation (graph_to_wedgelist g) l -> sum_LE g = fold_left Z.add (map fst l) 0.
Proof.
unfold sum_LE, DEList; intros. apply fold_left_comm. intros; lia.
replace (map (elabel g) (EList g)) with (map fst (graph_to_wedgelist g)).
apply Permutation_map. auto.
unfold graph_to_wedgelist. unfold edge_to_wedge.
rewrite map_map. simpl. auto.
Qed.

(*NoDup is probably unnecessary, but convenient*)
Lemma list_same_diff:
forall {A: Type} {EA: EqDec A eq} (l1 l2: list A), NoDup l1 -> NoDup l2 ->
      exists lsame ldiff, NoDup lsame /\ NoDup ldiff /\ Permutation (lsame++ldiff) l1 /\
      incl lsame l2 /\ (forall e, In e ldiff -> ~ In e l2).
Proof.
induction l1; intros. exists nil. exists nil.
  rewrite app_nil_l. split. apply NoDup_nil. split. apply NoDup_nil. split. apply perm_nil.
  split. unfold incl; intros; contradiction. intros. unfold not; intros; contradiction.
  (*By NoDup, a can't already be in l1
  *)
  specialize IHl1 with l2. assert (NoDup l1). apply NoDup_cons_1 in H; auto.
  apply (IHl1 H1) in H0. destruct H0 as [lsame [ldiff [? [? ?]]]].
  destruct (in_dec EA a l2).
  (*yes, then a is in lsame*)
  exists (a::lsame). exists ldiff. split. simpl. apply NoDup_cons. unfold not; intros.
  assert (In a l1). apply (Permutation_in (l:=(lsame++ldiff))). apply H3.
  apply in_or_app. left; auto.
  apply NoDup_cons_2 in H. contradiction.
  auto. split. auto. split. simpl. apply perm_skip. apply H3.
  split. unfold incl; intros. destruct H4. subst a; auto. apply H3; auto. apply H3.
  (*no, then a is in ldiff*)
  exists lsame. exists (a::ldiff). split. auto. split. apply NoDup_cons.
  unfold not; intros. assert (In a l1).
  apply (Permutation_in (l:=(lsame++ldiff))). apply H3.
  apply in_or_app. right; auto.
  apply NoDup_cons_2 in H. contradiction.
  auto. split.
  apply (Permutation_trans (l:=lsame ++ a :: ldiff) (l':=a::ldiff++lsame)).
  apply Permutation_app_comm. apply perm_skip.
  apply (Permutation_trans (l':=lsame ++ ldiff) (l:=ldiff++lsame)).
  apply Permutation_app_comm. apply H3.
  split. apply H3. intros. destruct H4. subst a. auto. apply H3. auto.
Qed.

(*I can't induct directly on a graph or it's EList (have to intros the graph), so
relying on this*)
Lemma exists_element_list:
forall {A B: Type} {A': Inhabitant A} {B': Inhabitant B} (P: A -> B -> Prop) (la: list A),
(forall a, In a la -> exists b, P a b) ->
(exists lb, Zlength lb = Zlength la /\ forall i, 0 <= i < Zlength la -> P (Znth i la) (Znth i lb)).
Proof.
induction la; intros. exists nil. split. auto. intros. rewrite Zlength_nil in H0; lia.
assert (forall a : A, In a la -> exists b : B, P a b). intros. apply H. right; auto.
apply IHla in H0. destruct H0 as [lb ?].
assert (exists b : B, P a b). apply H. left; auto. destruct H1 as [b ?].
exists (b::lb). split. do 2 rewrite Zlength_cons; lia.
intros. rewrite Zlength_cons in H2.
destruct (Z.lt_trichotomy 0 i).
do 2 rewrite Znth_pos_cons by lia. apply H0. lia.
destruct H3. subst i. do 2 rewrite Znth_0_cons. auto. lia.
Qed.

Lemma forest_bridge1:
forall (g: FiniteWEdgeListGraph) u v, sound_weighted_edge_graph g -> sound_uforest g ->
evalid g (u,v) -> bridge g (u,v) u v.
Proof.
unfold bridge; intros.
apply (forest_edge' p l g). auto. apply sound_strong_evalid; auto.
rewrite <- sound_src; auto. rewrite <- sound_dst; auto. auto.
Qed.

(*
Lemma forest_bridges:
if a simple path exists with a fitting list of edges, every edge in that list is a bridge
*)

(*t1: the tree we're comparing
t2: our msf*)
Lemma induct:
forall ldiff lsame (g t1 t2: FiniteWEdgeListGraph), sound_weighted_edge_graph g ->
  labeled_spanning_uforest t1 g -> labeled_spanning_uforest t2 g ->
  Permutation (ldiff++lsame) (EList t1) -> incl lsame (EList t2) ->
  (forall e, In e ldiff -> ~ In e (EList t2)) ->
  exists lmsf, Zlength ldiff = Zlength lmsf /\ Permutation (lmsf++lsame) (EList t2) /\
      forall i, 0 <= i < Zlength lmsf -> bridge t2 (Znth i lmsf) (src t1 (Znth i ldiff)) (dst t1 (Znth i ldiff) (*<-- this condition is probably phrased weirdly, if a simpler version can be found...*)
  ).
Proof.
induction ldiff; intros.
+(*nil case*)
exists nil. split. auto.
rewrite app_nil_l in H2; rewrite app_nil_l.
assert (sound_weighted_edge_graph t1). apply (spanning_uforest_sound t1 g); auto.
assert (sound_weighted_edge_graph t2). apply (spanning_uforest_sound t2 g); auto.
assert (NoDup lsame). apply Permutation_sym in H2; apply Permutation_NoDup in H2. auto. apply NoDup_EList.
split. apply NoDup_Permutation. auto. apply NoDup_EList.
intros; split; intros. unfold incl in H3; apply H3. auto.
apply EList_evalid in H8. destruct x as [u v].
destruct (in_dec E_EqDec (u,v) lsame). auto.
(*u is connected to v in all graphs. So if u-v is not in lsame, exists another path in t1
Then, exists a list of edges l, fits_upath l p. All of l's edges must belong in EList t1, thus in lsame.
Thus, incl l t2. Which means connected_by_path t2 p u v. But (u,v) is an alternative path in t2. contra*)
assert (connected_by_path t2 (u::v::nil) u v).
  split. simpl. split. exists (u,v). split. apply sound_strong_evalid; auto.
  left. destruct H6 as [? [? [? [? ?]]]]. rewrite H11; auto. rewrite H12; auto.
  apply (sound_uv_vvalid t2 u v); auto. simpl; split; auto.
assert (connected t1 u v). apply H0. apply H1. exists (u::v::nil). auto.
destruct H10 as [p ?]. assert (exists l : list EType, fits_upath t1 l p). apply connected_exists_list_edges in H10; auto.
destruct H11 as [l ?].
assert (~ In (u,v) l). unfold not; intros. (*If it were, then it is in lsame*)
  assert (evalid t1 (u,v)). apply (fits_upath_evalid t1 p l H11 (u,v)). auto.
  rewrite <- EList_evalid in H13. apply (Permutation_in (l':=lsame)) in H13. contradiction.
  apply Permutation_sym. apply H2.
apply (fits_upath_transfer p l t1 t2) in H11; auto.
  2: { intros.
        rewrite <- (spanning_preserves_vertices g t1). apply (spanning_preserves_vertices g t2). apply H1. apply H0. }
  2: { intros. assert (In e lsame). apply (Permutation_in (l:=(EList t1))). apply Permutation_sym. apply H2.
        apply EList_evalid. apply (fits_upath_evalid t1 p l); auto. rewrite <- EList_evalid. apply H3. auto. }
(*need the following:
  -if t is a spanning forest of g and In (u,v) t, paths (simple or not) connecting u and v must go through (u,v)
*)
apply (forest_edge' p l t2 (u,v)) in H11. contradiction.
apply H1. apply H1. auto. rewrite <- sound_src; auto. rewrite <- sound_dst; auto. simpl. split.
apply valid_upath_exists_list_edges'. intros. apply (spanning_preserves_vertices g t2). apply H1. apply (spanning_preserves_vertices g t1). apply H0.
apply (valid_upath_vvalid t1 p v0). apply H10. auto.
exists l; auto. apply H10.
(******YYYYYYYYYYYYYYYYYYYYYYYYYYYYYYYESSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS******)
intros. rewrite Zlength_nil in H8. lia.
+
simpl in H2.
destruct a as (u1,v1).
Admitted.