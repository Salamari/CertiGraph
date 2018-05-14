Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import RamifyCoq.lib.Coqlib.
Require Import RamifyCoq.lib.EquivDec_ext.

Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.msl_application.Graph.

Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.graph.MathGraph.
Require Import RamifyCoq.graph.FiniteGraph.

Class pPointwiseGraph_GC: Type :=
  {
    val: Type;
    null: val;
    SGBA: PointwiseGraphBasicAssum val (val * nat)
  }.

Existing Instance SGBA.

Definition is_null_SGBA {pSGG: pPointwiseGraph_GC} : DecidablePred val :=
  (existT (fun P => forall a, {P a} + {~ P a})
          (fun x => x = null) (fun x => SGBA_VE x null)).

Section GC_Graph.

  Context {pPG_GC: pPointwiseGraph_GC}.

  Inductive raw_field : Type :=
  | raw_data : val -> raw_field
  | raw_pointer : raw_field.
  
  Record raw_vertex_block : Type :=
    {
      raw_mark: bool;
      raw_fields: list raw_field;
      raw_color: Z;
      raw_tag: Z;
    }.

  Record space: Type :=
    { 
      start: val;
      used_space: nat;
      rest_space: nat;
    }.

  Record heap: Type :=
    {
      spaces: list space;
    }.

  Definition LGraph := LabeledGraph val (val * nat) raw_vertex_block unit heap.

  Fixpoint get_edges' (lf: list raw_field) (v: val) (n: nat) : list (val * nat) :=
    match lf with
    | nil => nil
    | cons x lf' => match x with
                    | raw_data _ => get_edges' lf' v (n + 1)
                    | raw_pointer => (v, n) :: get_edges' lf' v (n + 1)
                    end
    end.

  Definition get_edges (g: LGraph) (v: val) :=
    get_edges' (raw_fields (vlabel g v)) v O.

  Lemma get_edges'_range: forall v n l m,
      In (v, n) (get_edges' l v m) -> m <= n < m + length l.
  Proof.
    intros v n l. revert v n. induction l; simpl; intros. 1: exfalso; auto.
    specialize (IHl v n (m + 1)). destruct a. 1: apply IHl in H; omega.
    simpl in H. destruct H. 1: inversion H; omega. apply IHl in H. omega.
  Qed.

  Lemma get_edges'_nth: forall n l a m v,
      n < length l -> nth n l a = raw_pointer <-> In (v, n + m) (get_edges' l v m).
  Proof.
    induction n.
    - induction l; simpl; intros. 1: inversion H. destruct a.
      + split; intros. inversion H0. apply get_edges'_range in H0. exfalso; omega.
      + simpl. intuition.
    - destruct l; simpl; intros. 1: inversion H. assert (n < length l) by omega.
      specialize (IHn l a (m + 1) v H0).
      replace (n + (m + 1)) with (S (n + m)) in IHn by omega. rewrite IHn.
      destruct r; intuition. simpl in H3. destruct H3; auto. inversion H3. omega.
  Qed.

  Local Coercion pg_lg: LabeledGraph >-> PreGraph.

  Class SoundGCGraph (g: LGraph) :=
    {
      fin: FiniteGraph g;
      field_decided_edges: forall v e,
          vvalid g v -> (src g e = v /\ evalid g e <-> In e (get_edges g v));
      (* Other constraints would be added later *)
    }.

  Definition Graph :=
    GeneralGraph val (val * nat) raw_vertex_block unit heap (fun g => SoundGCGraph g).

  Record vertex_block :=
    {
      v_mark: bool;
      v_fields: list val;
      v_color: Z;
      v_tag: Z;
    }.

  Definition SGraph := PointwiseGraph val (val * nat) vertex_block unit.

  Fixpoint make_fields' (g: LGraph) (lf : list raw_field)
           (v : val) (n : nat) : list val :=
    match lf with
    | nil => nil
    | cons x lf' => match x with
                    | raw_data d => d :: make_fields' g lf' v (n + 1)
                    | raw_pointer => dst g (v, n) :: make_fields' g lf' v (n+1)
                  end
    end.

  Definition make_fields (g: LGraph) (v: val) :=
    make_fields' g (raw_fields (vlabel g v)) v O.

  Definition gen_vertex_gamma (g: LGraph) (v: val): vertex_block :=
    Build_vertex_block (raw_mark (vlabel g v))
                       (make_fields g v)
                       (raw_color (vlabel g v))
                       (raw_tag (vlabel g v)).

  Instance SGC_GC: PointwiseGraphConstructor
                     val (val * nat) raw_vertex_block unit heap vertex_block unit.
  Proof.
    constructor. exact gen_vertex_gamma. exact (fun _ _ => tt).
  Defined.

  Instance LSGC_GC: Local_PointwiseGraphConstructor val (val * nat) raw_vertex_block unit heap vertex_block unit.
  Proof.
    refine (Build_Local_PointwiseGraphConstructor
              _ _ _ _ _ _ _ SGBA SGC_GC
              (fun G v => forall e, In e (get_edges G v) -> evalid G e /\ src G e = v)
              _ (fun G e => True) _); trivial.
    simpl. intros. unfold gen_vertex_gamma. rewrite H1. f_equal.
    unfold make_fields. rewrite H1. remember (raw_fields (vlabel G2 x)) as l.
    clear Heql. remember 0 as n. clear Heqn. revert n. induction l; intros; simpl.
    1: reflexivity. destruct a. 1: f_equal; rewrite IHl; reflexivity.
    rewrite IHl. f_equal.
  Abort.

  Class sPointwiseGraph_GraphGC: Type :=
    {
      pred: Type;
      PGP: PointwiseGraphPred val (val * nat) vertex_block unit pred;
      PGA: PointwiseGraphAssum PGP;
      PGAvs: PointwiseGraphAssum_vs PGP;
      PGAvn: PointwiseGraphAssum_vn PGP null
    }.

End GC_Graph.
