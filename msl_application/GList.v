Require Import Coq.Logic.Classical.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.weak_mark_lemmas.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.graph_gen.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_computable.
Require Export RamifyCoq.graph.FiniteGraph.
Require Export RamifyCoq.graph.MathGraph.
Require Export RamifyCoq.graph.LstGraph.
Require Export RamifyCoq.graph.UnionFind.
Require Import RamifyCoq.msl_application.Graph.

Local Open Scope logic.

Class pSpatialGraph_GList: Type :=
  {
    addr: Type;
    null: addr;
    pred: Type;
    SGBA: SpatialGraphBasicAssum addr (addr * unit)
  }.

Existing Instance SGBA.

Definition is_null_SGBA {pSGG: pSpatialGraph_GList} : DecidablePred addr := (existT (fun P => forall a, {P a} + {~ P a}) (fun x => x = null) (fun x => SGBA_VE x null)).

Class sSpatialGraph_GList {pSGG_Bi: pSpatialGraph_GList} (DV DE: Type): Type :=
  {
    SGP: SpatialGraphPred addr (addr * unit) (DV * addr) unit pred;
    SGA: SpatialGraphAssum SGP;
    SGAvs: SpatialGraphAssum_vs SGP;
    SGAvn: SpatialGraphAssum_vn SGP null
  }.

Existing Instances SGP SGA SGAvs.

Section GRAPH_GList.

  Context {pSGG: pSpatialGraph_GList}.
  Context {DV DE DG: Type}.

  Class LiMaFin (g: PreGraph addr (addr * unit)) :=
    {
      li: LstGraph g (fun x => (x, tt));
      ma: MathGraph g is_null_SGBA;
      fin: FiniteGraph g
    }.

  Definition Graph := (GeneralGraph addr (addr * unit) DV DE DG (fun g => LiMaFin (pg_lg g))).
  Definition LGraph := (LabeledGraph addr (addr * unit) DV DE DG).
  Definition SGraph := (SpatialGraph addr (addr * unit) (DV * addr) unit).

  Instance SGC_GList: SpatialGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_SpatialGraphConstructor _ _ _ _ _ _ _ SGBA _ _).
    + exact (fun G v => (vlabel G v, let target := dst (pg_lg G) (v, tt) in if (SGBA_VE target null) then v else target)).
    + exact (fun _ _ => tt).
  Defined.

  Instance L_SGC_GList: Local_SpatialGraphConstructor addr (addr * unit) DV DE DG (DV * addr) unit.
  Proof.
    refine (Build_Local_SpatialGraphConstructor
              _ _ _ _ _ _ _ SGBA SGC_GList
              (fun G v => evalid (pg_lg G) (v, tt) /\ src (pg_lg G) (v, tt) = v) _
              (fun _ _ => True) _).
    - intros. simpl. destruct H as [? ?], H0 as [? ?]. f_equal; auto. pose proof (H3 _ H H5 H0 H6). rewrite <- !H7. clear H7.
      destruct (SGBA_VE (dst (pg_lg G1) (x, tt)) null); auto.
    - intros; simpl. auto.
  Defined.

  Global Existing Instances SGC_GList L_SGC_GList.

  Definition Graph_LGraph (G: Graph): LGraph := lg_gg G.
  Definition LGraph_SGraph (G: LGraph): SGraph := Graph_SpatialGraph G.

  Local Coercion Graph_LGraph: Graph >-> LGraph.
  Local Coercion LGraph_SGraph: LGraph >-> SGraph.
  Local Identity Coercion Graph_GeneralGraph: Graph >-> GeneralGraph.
  Local Identity Coercion LGraph_LabeledGraph: LGraph >-> LabeledGraph.
  Local Identity Coercion SGraph_SpatialGraph: SGraph >-> SpatialGraph.
  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Instance maGraph(G: Graph): MathGraph G is_null_SGBA := @ma G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance finGraph (G: Graph): FiniteGraph G := @fin G (@sound_gg _ _ _ _ _ _ _ _ G).
  Instance liGraph (G: Graph):  LstGraph G (fun x => (x, tt)) := @li G (@sound_gg _ _ _ _ _ _ _ _ G).

  Instance RGF (G: Graph): ReachableFiniteGraph G.
  Proof.
    apply Build_ReachableFiniteGraph.
    intros.
    apply finite_reachable_computable with (is_null := is_null_SGBA) in H.
    - destruct H as [l [? ?]]. exists l; auto.
    - apply maGraph.
    - apply (LocalFiniteGraph_FiniteGraph G), finGraph.
    - apply (FiniteGraph_EnumCovered G), finGraph.
  Defined.

  Definition make_set_pregraph (v: addr) (g: PreGraph addr (addr * unit)) := pregraph_add_edge (pregraph_add_vertex g v) (v, tt) v null.

  Lemma is_partial_make_set_pregraph: forall x (g: Graph), ~ vvalid g x -> is_partial_graph g (make_set_pregraph x g).
  Proof.
    intros. hnf. simpl. unfold addValidFunc, updateEdgeFunc. split; [|split; [|split]]; intros; [left; auto..| |].
    - destruct (equiv_dec (x, tt) e); auto. hnf in e0. subst e. pose proof (@only_one_edge _ _ _ _ g _ (liGraph g) (src g (x, tt)) (x, tt) H1). simpl in H2.
      assert (src g (x, tt) = src g (x, tt) /\ evalid g (x, tt)) by (split; auto). rewrite H2 in H3. inversion H3. exfalso. rewrite <- H5 in H1. auto.
    - destruct (equiv_dec (x, tt) e); auto. hnf in e0. subst e. destruct (@valid_graph _ _ _ _ g _ (maGraph g) _ H0) as [? _].
      pose proof (@only_one_edge _ _ _ _ g _ (liGraph g) (src g (x, tt)) (x, tt) H2). assert (src g (x, tt) = src g (x, tt) /\ evalid g (x, tt)) by (split; auto).
      rewrite H3 in H4. inversion H4. exfalso. rewrite <- H6 in H2. auto.
  Qed.

  Definition make_set_LabeledGraph (v: addr) (g: LabeledGraph addr (addr * unit) DV DE DG) (default_dv: DV) (default_de: DE) (default_dg: DG) : LGraph :=
    Build_LabeledGraph _ _ _ (make_set_pregraph v g) (fun x => if SGBA_VE x v then default_dv else vlabel g x) (fun e => default_de) default_dg.

  Definition make_set_MathGraph (v: addr) (g: PreGraph addr (addr * unit)) (H: v <> null) (Hm: MathGraph g is_null_SGBA): MathGraph (make_set_pregraph v g) is_null_SGBA.
  Proof.
    apply (Build_MathGraph _ is_null_SGBA).
    - intros. simpl. unfold updateEdgeFunc, addValidFunc. destruct (equiv_dec (v, tt) e). 1: intuition. simpl in H0. unfold addValidFunc in H0. destruct H0.
      + destruct Hm. apply valid_graph in H0. destruct H0. split. 1: left; auto. hnf in H1. simpl in H1. destruct H1; [left | right; left]; auto.
      + compute in c. exfalso; intuition.
    - intros. hnf in H0. simpl in H1. destruct H0.
      + subst x. destruct Hm. apply valid_not_null in H0; auto. simpl. auto.
      + subst v. auto.
  Defined.

  Definition make_set_FiniteGraph (v: addr) (g: PreGraph addr (addr * unit)) (Hf: FiniteGraph g): FiniteGraph (make_set_pregraph v g).
  Proof.
    destruct Hf. unfold EnumEnsembles.Enumerable in *. destruct finiteV as [vl [? ?]]. destruct finiteE as [el [? ?]]. constructor; hnf; simpl; unfold addValidFunc.
    - destruct (in_dec SGBA_VE v vl).
      + exists vl. split; auto. intros. unfold In in H0 |-* . rewrite H0. intuition. subst v. rewrite H0 in i. auto.
      + exists (v :: vl). split; [constructor; auto|]. intros. simpl. unfold In in H0 |-* . rewrite H0. intuition.
    - unfold In in H2 |-* . destruct (in_dec SGBA_EE (v, tt) el).
      + exists el. split; auto. intros. rewrite H2. intuition. inversion H4. rewrite H2 in i. auto.
      + exists ((v, tt) :: el). split; [constructor; auto|]. intros. simpl. rewrite H2. intuition.
  Defined.

  Definition make_set_LstGraph (v: addr) (g: PreGraph addr (addr * unit)) (Hn: v <> null) (Hi: ~ vvalid g v) (Hm: MathGraph g is_null_SGBA)
             (Hl: LstGraph g (fun x => (x, tt))): LstGraph (make_set_pregraph v g) (fun x => (x, tt)).
  Proof.
    constructor; simpl.
    - unfold addValidFunc, updateEdgeFunc. intros. destruct H.
      + destruct Hl. specialize (only_one_edge x e H). destruct (equiv_dec (v, tt) e).
        * hnf in e0. subst e. rewrite <- only_one_edge. split; intros.
          -- destruct H0. subst v. rewrite only_one_edge. auto.
          -- rewrite only_one_edge in H0. inversion H0. subst v. split; auto.
        * compute in c. rewrite <- only_one_edge. split; intros.
          -- destruct H0. split; auto. destruct H1; auto. exfalso; auto.
          -- destruct H0. split; auto.
      + subst v. split; intros.
        * destruct H. destruct H0; auto. destruct (equiv_dec (x, tt) e).
          -- hnf in e0; auto.
          -- destruct Hm. specialize (valid_graph _ H0). destruct valid_graph. rewrite H in H1. exfalso; auto.
        * destruct (equiv_dec (x, tt) e).
          -- hnf in e0. split; auto.
          -- compute in c. exfalso; auto.
    - intros. destruct_eq_dec x v.
      + subst x. destruct p as [p l]. destruct H as [[? ?] [? _]]. simpl in H. subst p. simpl in H1. destruct l; auto. unfold updateEdgeFunc in H1. destruct H1.
        assert (strong_evalid (make_set_pregraph v g) p) by (simpl in H1; destruct l; [|destruct H1]; auto). hnf in H2. simpl in H2. unfold addValidFunc, updateEdgeFunc in H2.
        destruct H2 as [? [? ?]]. destruct (equiv_dec (v, tt) p).
        * exfalso. destruct H4; auto. destruct Hm. apply valid_not_null in H4; simpl; auto.
        * compute in c. exfalso. destruct H2; auto. destruct Hm. apply valid_graph in H2. destruct H2. subst v. auto.
      + destruct p as [p l]. assert (forall e, List.In e l -> e <> (v, tt)). {
          destruct H as [_ [? _]]. intros. apply (valid_path_strong_evalid _ _ _ e) in H; auto. hnf in H. simpl in H. unfold addValidFunc, updateEdgeFunc in H.
          destruct H as [? [? ?]]. intro. destruct (equiv_dec (v, tt) e). 2: compute in c; auto. destruct H3; auto. destruct Hm. apply valid_not_null in H3; simpl; auto.
        } destruct Hl. apply no_loop_path. destruct H as [[? ?] [? ?]]. split; split; auto.
        * clear H H3 H4. revert p H2. induction l; intros. 1: simpl in H2 |-* ; auto.
          assert (forall e : addr * unit, List.In e l -> e <> (v, tt)) by (intros; apply H1; right; auto). specialize (IHl H). clear H.
          rewrite pfoot_cons in H2 |-* . simpl dst in H2. unfold updateEdgeFunc in H2. destruct (equiv_dec (v, tt) a).
          -- hnf in e. assert (a <> (v, tt)) by (apply H1; left; auto). exfalso; auto.
          -- apply IHl; auto.
        * assert (p <> v) by (simpl in H; subst p; auto). clear H H2 H4. revert p H3 H5. induction l; intros.
          -- simpl in H3. unfold addValidFunc in H3. simpl. destruct H3; [|exfalso]; auto.
          -- assert (forall e : addr * unit, List.In e l -> e <> (v, tt)) by (intros; apply H1; right; auto). specialize (IHl H). clear H.
             assert (a <> (v, tt)) by (apply H1; left; auto). rewrite valid_path_cons_iff in H3 |-* . destruct H3 as [? [? ?]]. split; [|split].
             ++ simpl in H2. unfold updateEdgeFunc in H2. destruct (equiv_dec (v, tt) a); [exfalso|]; auto.
             ++ hnf in H3. simpl in H3. unfold addValidFunc, updateEdgeFunc in H3. destruct H3 as [? [? ?]].
                destruct (equiv_dec (v, tt) a); [hnf in e; exfalso|]; auto. destruct H3; [|exfalso]; auto. clear c.
                destruct H6. 2: destruct Hm; apply valid_graph in H3; destruct H3; rewrite H6 in H3; exfalso; auto.
                destruct H7. 2: destruct Hm; apply valid_graph in H3; destruct H3; hnf in H8; simpl in H8; rewrite H7 in H8; exfalso; destruct H8; auto.
                hnf. split; auto.
             ++ simpl dst in H4. unfold updateEdgeFunc in H4. destruct (equiv_dec (v, tt) a); [hnf in e; exfalso|]; auto. apply IHl; auto.
                destruct H3 as [? _]. simpl in H3. unfold addValidFunc in H3. destruct H3; [|exfalso]; auto. destruct Hm. apply valid_graph in H3. destruct H3 as [_ ?].
                hnf in H3. simpl in H3. intro. rewrite H6 in H3. destruct H3; auto.
  Defined.

  Definition make_set_sound (v: addr)  (g: PreGraph addr (addr * unit)) (Hn: v <> null) (Hi: ~ vvalid g v) (Hlmf: LiMaFin g) : LiMaFin (make_set_pregraph v g) :=
    Build_LiMaFin _ (make_set_LstGraph v g Hn Hi ma li) (make_set_MathGraph v g Hn ma) (make_set_FiniteGraph v g fin).

  Definition make_set_Graph (default_dv: DV) (default_de: DE) (default_dg: DG) (v: addr) (g: Graph) (Hn: v <> null) (Hi: ~ vvalid g v) : Graph :=
    Build_GeneralGraph _ _ _ _ (make_set_LabeledGraph v g default_dv default_de default_dg) (make_set_sound v g Hn Hi (sound_gg g)).

  Definition single_uf_pregraph (v: addr) : PreGraph addr (addr * unit) :=
    pregraph_add_edge (single_vertex_pregraph v) (v, tt) v null.

  Lemma reachabel_single_uf: forall x y, x <> null -> reachable (single_uf_pregraph x) x y <-> x = y.
  Proof.
    intros. split; intros.
    - destruct H0 as [[? ?] [[? ?] [? _]]]. simpl in H0. subst a. destruct l.
      + simpl in H1. auto.
      + destruct H2. simpl in H2. assert (strong_evalid (single_uf_pregraph x) p) by (destruct l; intuition). clear H2. exfalso.
        hnf in H3. simpl in H3. unfold updateEdgeFunc in H3. destruct H3 as [? [_ ?]]. unfold addValidFunc in H2. destruct H2; auto. subst p.
        destruct (equiv_dec (x, tt) (x, tt)); [|compute in c]; auto.
    - subst y. apply reachable_refl. simpl. auto.
  Qed.

  Definition single_uf_LabeledGraph (v: addr) (default_dv: DV) (default_de: DE) (default_dg: DG) : LGraph :=
    Build_LabeledGraph _ _ _ (single_uf_pregraph v) (fun v => default_dv) (fun e => default_de) default_dg.

  Definition single_uf_MathGraph (v: addr) (H: v <> null): MathGraph (single_uf_pregraph v) is_null_SGBA.
  Proof.
    apply (Build_MathGraph _ is_null_SGBA).
    - intros. simpl. unfold updateEdgeFunc.
      destruct (equiv_dec (v, tt) e); intuition.
    - intros. hnf in *. subst v. intuition.
  Defined.

  Definition single_uf_FiniteGraph (v: addr): FiniteGraph (single_uf_pregraph v).
  Proof.
    constructor; hnf.
    - exists (v :: nil). split.
      + constructor. intro. inversion H. constructor.
      + intros. simpl. unfold In. intuition.
    - exists ((v, tt) :: nil). split.
      + constructor. intro. inversion H. constructor.
      + intros. simpl. unfold In, addValidFunc. intuition.
  Defined.

  Definition single_uf_LstGraph (v: addr) (H: v <> null): LstGraph (single_uf_pregraph v) (fun x => (x, tt)).
  Proof.
    constructor; simpl; intros; unfold updateEdgeFunc.
    - unfold addValidFunc. subst. destruct (equiv_dec (x, tt) e); intuition.
    - destruct H0 as [[? _] [? _]]. destruct p as [p l]. simpl in *. subst p.
      destruct l; auto. destruct H1. clear H0. simpl in H1. assert (strong_evalid (single_uf_pregraph v) p) by (destruct l; [|destruct H1]; auto). clear H1.
      hnf in H0. simpl in H0. unfold addValidFunc, updateEdgeFunc in H0. destruct H0 as [? [_ ?]]. exfalso. destruct H0; auto. subst p.
      destruct (equiv_dec (v, tt) (v, tt)); auto. compute in c. apply c; auto.
  Defined.

  Definition single_sound (v: addr) (H: v <> null) : LiMaFin (single_uf_pregraph v) :=
    Build_LiMaFin _ (single_uf_LstGraph v H) (single_uf_MathGraph v H) (single_uf_FiniteGraph v).

  Definition single_Graph (v: addr) (H: v <> null) (default_dv: DV) (default_de: DE) (default_dg: DG): Graph :=
    Build_GeneralGraph _ _ _ _ (single_uf_LabeledGraph v default_dv default_de default_dg) (single_sound v H).

  Lemma valid_parent: forall (g: Graph) v n p, vvalid g v -> vgamma g v = (n, p) -> vvalid g p.
  Proof.
    intros. unfold vgamma in H0. simpl in H0. inversion H0. clear H0 H2. destruct (SGBA_VE (dst g (v, tt)) null); auto.
    unfold complement, Equivalence.equiv in c. pose proof (only_one_edge v (v, tt) H). simpl in H0. assert ((v, tt) = (v, tt)) by auto. rewrite <- H0 in H1. destruct H1.
    pose proof (valid_graph _ _ H2). destruct H4 as [_ [? | ?]]; auto. simpl in H4. exfalso; auto.
  Qed.

  Lemma parent_loop: forall (g: Graph) v n y, vgamma g v = (n, v) -> reachable g v y -> v = y.
  Proof.
    intros. unfold vgamma in H. simpl in H. destruct (SGBA_VE (dst g (v, tt)) null).
    - unfold Equivalence.equiv in e. assert (~ reachable g null y) by (intro; apply reachable_head_valid in H1; apply (valid_not_null g null H1); simpl; auto).
      apply (lst_out_edge_only_one g _ v null y); auto.
    - apply (lst_self_loop _ (liGraph g)) in H0; auto. inversion H. rewrite H3. auto.
  Qed.

  Lemma gamma_parent_reachable_included: forall (g: Graph) x r pa, vvalid g x -> vgamma g x = (r, pa) -> Included (reachable g pa) (reachable g x).
  Proof.
    intros. intro y; intros. unfold vgamma in H0. simpl in H0. destruct (SGBA_VE (dst g (x, tt)) null).
    - inversion H0. auto.
    - apply edge_reachable_by with pa; auto. split; auto. split.
      + apply reachable_head_valid in H1; auto.
      + inversion H0. rewrite H4. rewrite (dst_step _ (liGraph g) _ _ H H4). auto.
  Qed.

  Lemma Prop_join_reachable_parent: forall (g: Graph) x r pa,
      vvalid g x ->
      vgamma g x = (r, pa) ->
      Prop_join
        (reachable g pa)
        (Intersection _ (reachable g x) (Complement addr (reachable g pa)))
        (reachable g x).
  Proof.
    intros.
    apply Ensemble_join_Intersection_Complement.
    - eapply gamma_parent_reachable_included; eauto.
    - intros. apply decidable_prop_decidable. pose proof (finGraph g).
      apply (@reachable_decidable_prime _ _ _ _ _ _ (maGraph g)).
      + apply LocalFiniteGraph_FiniteGraph; auto.
      + apply (valid_parent _ x r); auto.
      + apply FiniteGraph_EnumCovered; auto.
  Qed.

  Definition Graph_gen_redirect_parent (g: Graph) (x: addr) (pa: addr) (H: weak_valid g pa) (Hv: vvalid g x) (Hn: ~ reachable g pa x): Graph.
  Proof.
    refine (generalgraph_gen_dst g (x, tt) pa _). constructor.
    - simpl. apply (gen_dst_preserve_lst g (liGraph g)); auto.
    - apply (gen_dst_preserve_math g (x, tt) pa (maGraph g) H).
    - apply (gen_dst_preserve_finite g (x, tt) pa (finGraph g)).
  Defined.

  Lemma Graph_reachable_dec: forall (G: Graph) x, Decidable (vvalid G x) -> forall y, Decidable (reachable G x y).
  Proof.
    intros. apply reachable_decidable with (is_null := is_null_SGBA); auto.
    + apply maGraph.
    + apply LocalFiniteGraph_FiniteGraph, finGraph.
    + apply FiniteGraph_EnumCovered, finGraph.
  Qed.

  Definition Graph_vgen (G: Graph) (x: addr) (d: DV) : Graph := generalgraph_vgen G x d (sound_gg G).

End GRAPH_GList.
