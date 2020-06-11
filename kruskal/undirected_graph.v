(*Looted and modified from graph/path_lemmas.v
Idea is with a definition of connectedness, there's no need to explicitly define an undirected graph
Which sort of makes sense I guess, because every directed graph has an underlying undirected graph by just removing the direction
And directed graphs make more sense in C compared to ugraphs (correct me if I'm wrong)
*)

Require Import Coq.Logic.ProofIrrelevance.
(*Require Import RamifyCoq.lib.Coqlib.*)
Require Import RamifyCoq.lib.Ensembles_ext.
(*Require Import RamifyCoq.lib.EnumEnsembles.*)
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.path_lemmas.
(*
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
*)

Section UNDIRECTED.

Context {V E: Type}.
Context {EV: EqDec V eq}.
Context {EE: EqDec E eq}.

Notation Gph := (PreGraph V E).

(*as long as there is an edge from u to v, u and v are connected, regardless of who is the src*)
Definition adj_edge (g: Gph) (e: E) (u v: V) :=
  strong_evalid g e /\ (*just evalid?*)
  ((src g e = u /\ dst g e = v) \/ (src g e = v /\ dst g e = u)).

(*Consequently, we may not care about the exact nature of the edges*)
Definition adjacent (g: Gph) (u v: V) := exists e: E,
  adj_edge g e u v.

Lemma adjacent_requires_vvalid:
  forall g u v, adjacent g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H. destruct H0; destruct H0; rewrite <- H0; rewrite <- H1; split; apply H.
Qed.

Lemma adjacent_symm:
  forall g u v, adjacent g u v -> adjacent g v u.
Proof.
intros. destruct H. exists x. destruct H. destruct H0.
split. apply H. right. apply H0.
split. apply H. left. apply H0.
Qed.

(* But we may still need to pull out the edges, e.g. for labels
Problem is, because the graph is still fundamentally directed, there can be edges going a->b and b->a
So maybe we just return every such edge
But, it makes no sense having an undirected graph with more than one edge between two vertices
*)
Definition adj_edges g u v: Ensemble E := fun e => adj_edge g e u v.

(************CUSTOM LIST OPERATIONS************)
(*Since it makes sense for us to deal with l+::a a lot*)

(*curious this doesn't exist in the list library*)
Fixpoint last_error {A: Type} (l : list A): option A :=
match l with
| nil => None
| a::nil => Some a
| _::l' => last_error l'
end.

Lemma last_error_cons: (*for convenience*)
  forall {A:Type} (l: list A) (a: A), l <> nil -> last_error (a::l) = last_error l.
Proof.
intros. destruct l. contradiction. simpl. reflexivity.
Qed.

Lemma last_err_appcons:
  forall {A:Type} (l: list A) (a: A), last_error (l+::a) = Some a.
Proof.
induction l. auto. intros. rewrite <- app_comm_cons. rewrite <- (IHl a0). simpl.
destruct (l+::a0) eqn:H. assert (l+::a0 <> nil) by (apply app_not_nil). contradiction.
reflexivity.
Qed.

Lemma last_err_app':
  forall {A:Type} (l2 l1: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
induction l2; intros. inversion H.
destruct l2. simpl in H. inversion H. apply last_err_appcons.
assert (last_error (a::a1::l2) = last_error (a1::l2)). simpl. reflexivity. rewrite H0 in H.
assert (l1++a::a1::l2 = (l1+::a) ++ (a1::l2)).
assert (a:: a1 :: l2 = (a::nil)++a1::l2) by reflexivity. rewrite H1.
rewrite app_assoc. reflexivity. rewrite H1.
apply (IHl2 (l1+::a)). apply H.
Qed.

Lemma last_err_app:
  forall {A:Type} (l1 l2: list A) (a: A), last_error l2 = Some a -> last_error (l1++l2) = Some a.
Proof.
intros. apply (last_err_app' l2 l1 a H).
Qed.

Lemma rev_hd_last:
  forall {A:Type} (l: list A), hd_error l = last_error (rev l).
Proof.
induction l. auto.
simpl. rewrite (last_err_appcons (rev l) a). reflexivity.
Qed.

Lemma hd_error_In:
  forall {A:Type} (l: list A) a, hd_error l = Some a -> In a l.
Proof.
intros. destruct l; simpl in H; inversion H. left; auto.
Qed.

Lemma last_error_In:
  forall {A:Type} (l: list A) a, last_error l = Some a -> In a l.
Proof.
induction l; intros. inversion H.
destruct l. inversion H. left; auto.
right. apply IHl. rewrite last_error_cons in H. apply H.
unfold not; intros. inversion H0.
Qed.

(*A bunch of helpers for convenience in handling options*)
Fixpoint adjacent_last g (u: option V) (v: V) :=
match u with
| None => vvalid g v
| Some u' => adjacent g u' v
end.

Fixpoint adjacent_hd g (u: V) (v: option V) :=
match v with
| None => vvalid g u
| Some v' => adjacent g u v'
end.

Fixpoint adjacent_err g (u: option V) (v: option V) :=
match u, v with
| None, None => True
| None, Some v' => vvalid g v'
| Some u', None => vvalid g u'
| Some u', Some v' => adjacent g u' v'
end.

Lemma adjacent_last_adjacent:
  forall g u v, adjacent_last g (Some u) v <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_hd_adjacent:
  forall g u v, adjacent_hd g u (Some v) <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_err_adjacent:
  forall g u v, adjacent_err g (Some u) (Some v) <-> adjacent g u v.
Proof.
intros; split; intros; destruct H; exists x; apply H.
Qed.

Lemma adjacent_err_last:
  forall g opt_u v, adjacent_err g opt_u (Some v) -> adjacent_last g opt_u v.
Proof.
destruct opt_u; intros; apply H.
Qed.

Lemma adjacent_err_hd:
  forall g u opt_v, adjacent_err g (Some u) opt_v -> adjacent_hd g u opt_v.
Proof.
destruct opt_v; intros; apply H.
Qed.

(************UNDIRECTED PATHS************)

(*I think it makes sense to define an undirected path based on vertices,
  given the definition above. Hard to define based on edges since edges are implicitly directed*)
Definition upath := list V.

(*So the difference between here and path_lemmas, is that the directed paths are guaranteed one vertex. That's why I need the last_error*)

Fixpoint valid_upath (g: Gph) (p: upath) : Prop :=
  match p with
    | nil => True
    | u :: nil => vvalid g u
    | u :: ((v :: _) as p') => adjacent g u v /\ valid_upath g p' (* /\ vvalid g u*)
  end.

Lemma valid_upath_tail':
  forall g p u, valid_upath g (u::p) -> valid_upath g p.
Proof.
induction p; intros.
-simpl; auto.
-simpl in H. destruct H. destruct p.
  +simpl; auto.
  +destruct H0. simpl. split. apply H0. apply H1.
Qed.

Corollary valid_upath_tail:
  forall g p, valid_upath g p -> valid_upath g (tl p).
Proof.
intros; destruct p. auto. simpl. apply (valid_upath_tail' g p v H).
Qed.

Lemma valid_upath_cons:
  forall g p u, valid_upath g p -> adjacent_hd g u (hd_error p) -> valid_upath g (u::p).
Proof.
induction p; intros.
-simpl in H0. simpl; auto.
-destruct p.
  +simpl in *. auto.
  +split. apply H0. apply H.
Qed.

Lemma valid_upath_vvalid:
  forall g p v, valid_upath g p -> In v p -> vvalid g v.
Proof.
induction p; intros. contradiction.
simpl in H0. destruct H0.
subst a. destruct p. auto. destruct H. destruct H. destruct H. destruct H.
destruct H1; destruct H1. rewrite <- H1. apply H2. rewrite <- H3; apply H2.
apply IHp. apply (valid_upath_tail' g p a H). auto.
Qed.

Lemma valid_upath_app:
  forall g p1 p2, valid_upath g p1 -> valid_upath g p2 -> adjacent_err g (last_error p1) (hd_error p2) -> valid_upath g (p1++p2).
Proof.
induction p1; intros.
-apply H0.
-destruct p1.
  +simpl. apply valid_upath_cons. apply H0. apply adjacent_err_hd. apply H1.
  +rewrite <- app_comm_cons. split. apply H. apply IHp1. apply H. apply H0. apply H1.
Qed.

Lemma hd_error_none_nil:
  forall {A:Type} (l: list A), hd_error l = None <-> l = nil.
Proof.
  intros; split; intros. destruct l. reflexivity. simpl in H. inversion H.
  rewrite H. reflexivity.
Qed.

Lemma valid_upath_app_2: (*find a better name*)
  forall g p1 p2, valid_upath g p1 -> valid_upath g p2 -> (last_error p1) = (hd_error p2) -> valid_upath g (p1++(tail p2)).
Proof.
intros. apply valid_upath_app. apply H. apply (valid_upath_tail g p2 H0).
unfold adjacent_err.
destruct (last_error p1) eqn:H2. destruct (hd_error p2) eqn:H3.
assert (v = v0) by (inversion H1; reflexivity).
destruct (hd_error (tl p2)) eqn: H5. assert (p2 = v0::v1::(tl (tl p2))).
apply hd_error_tl_repr. split. apply H3. apply hd_error_tl_repr. split. apply H5. reflexivity.
rewrite H6 in H0. destruct H0. rewrite H4. apply H0.
assert (p2 = v0::(tl p2)). apply hd_error_tl_repr. split. apply H3. reflexivity.
rewrite hd_error_none_nil in H5. unfold valid_upath in H0. rewrite H6 in H0; rewrite H5 in H0.
rewrite H4; apply H0.
inversion H1.
assert (tl p2 = nil). destruct p2. reflexivity. inversion H1. rewrite H3. simpl. trivial.
Qed.

Corollary valid_upath_concat:
  forall g p v, valid_upath g p -> adjacent_last g (last_error p) v -> valid_upath g (p+::v).
Proof.
intros. apply (valid_upath_app g p (v::nil)). apply H.
simpl. destruct (last_error p); simpl in H0. apply (adjacent_requires_vvalid g v0 v H0). apply H0.
destruct (last_error p); simpl in *; apply H0.
Qed.

Lemma valid_upath_rev:
  forall g p, valid_upath g p -> valid_upath g (rev p).
Proof.
induction p; intros. auto.
simpl. apply valid_upath_concat. apply IHp. apply (valid_upath_tail' g p a H).
rewrite <- rev_hd_last. destruct p. apply H.
simpl. destruct H. apply adjacent_symm. apply H.
Qed.

Definition upath_prop (P : Ensemble V)  (p: upath) : Prop :=
  Forall (fun v => P v) p.

Definition good_upath (g: Gph) (P : Ensemble V) : (upath -> Prop) := fun p => valid_upath g p /\ upath_prop P p.

Corollary good_upath_rev:
  forall g P p, good_upath g P p -> good_upath g P (rev p).
Proof.
intros. split. apply valid_upath_rev. apply H.
destruct H. unfold upath_prop in *; rewrite Forall_forall in *. intros. apply H0. rewrite In_rev; apply H1.
Qed.

Definition connected_by_path (g: Gph) (P : Ensemble V) (p: upath) (n : V) : Ensemble V :=
  fun n' => good_upath g P p /\ hd_error p = Some n /\ last_error p = Some n'.

Definition connected_by (g: Gph) (P : Ensemble V) (n : V) : Ensemble V :=
  fun n' => exists p, connected_by_path g P p n n'.

Definition connected (g: Gph) (n : V): Ensemble V:= connected_by g (fun _ => True) n.

Lemma connected_by_symm:
  forall g P u v, connected_by g P u v -> connected_by g P v u.
Proof.
unfold connected_by; unfold connected_by_path; intros.
destruct H. rename x into p. exists (rev p). split. apply good_upath_rev. apply H.
split. rewrite <- (rev_involutive p) in H. rewrite <- rev_hd_last in H. apply H.
rewrite rev_hd_last in H. apply H.
Qed.

Corollary connected_symm:
  forall g u v, connected g u v -> connected g v u.
Proof.
  intro; apply connected_by_symm.
Qed.

Lemma connected_by_trans:
  forall g P u v w, connected_by g P u v -> connected_by g P v w -> connected_by g P u w.
Proof.
unfold connected_by; unfold connected_by_path; intros.
destruct H; rename x into p0. destruct H0; rename x into p1.
destruct H. destruct H1. destruct H0. destruct H3.
exists (p0++(tail p1)). split. split. apply valid_upath_app_2. apply H. apply H0.
rewrite H3. rewrite H2. reflexivity.
destruct H.  destruct H0. unfold upath_prop in *. rewrite Forall_forall in *; intros. apply in_app_or in H7.
destruct H7. apply H5. apply H7. apply In_tail in H7. apply H6. apply H7.
split. assert (p0 = u::(tl p0)). apply hd_error_tl_repr. split. apply H1. reflexivity.
rewrite H5. rewrite <- app_comm_cons. simpl. reflexivity.
destruct p1 eqn:H5. inversion H4.
destruct u0. simpl in *. rewrite <- app_nil_end. rewrite <- H4. rewrite H3. apply H2.
simpl. apply last_err_app. simpl in H4. simpl. apply H4.
Qed.

Corollary connected_trans:
  forall g u v w, connected g u v -> connected g v w -> connected g u w.
Proof.
intros. apply (connected_by_trans g (fun _ => True) u v w H H0).
Qed.

Lemma adjacent_connected:
  forall g u v, adjacent g u v -> connected g u v.
Proof.
intros. exists (u::v::nil). split. split. simpl. split. apply H. unfold adjacent in H. destruct H. destruct H. destruct H.
destruct H0; destruct H0. rewrite <- H2; apply H1. rewrite <- H0; apply H1.
unfold upath_prop; rewrite Forall_forall. intros; auto.
split; simpl; auto.
Qed.

Lemma connected_by_path_vvalid:
forall g P p u v, connected_by_path g P p u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H0. destruct H.
split. apply (valid_upath_vvalid g p u). auto. apply hd_error_In; auto.
apply (valid_upath_vvalid g p v). auto. apply last_error_In; auto.
Qed.

Corollary connected_vvalid:
  forall g u v, connected g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H as [p ?]. apply (connected_by_path_vvalid _ _ _ _ _ H).
Qed.

Definition connected_graph (g: Gph) := forall u v, vvalid g u -> vvalid g v -> connected g u v.

Definition simple_upath g p := valid_upath g p /\ NoDup p.
(*
Lemma paths_can_be_simplified:
  forall g p, valid_upath g p -> exists p', simple_upath g p' /\ simplified p p'
*)

(************REASONING ABOUT A SPECIFIC LIST OF EDGES************)

Fixpoint fits_upath g (l: list E) (p: upath) :=
match l, p with
| nil, nil => True
| nil, v::nil => True
| e::l', u::v::p' => adj_edge g e u v /\ fits_upath g l' (v::p')
| _, _ => False
end.

Lemma connected_exists_list_edges:
forall g P p u v, connected_by_path g P p u v -> exists l, fits_upath g l p.
Proof.
induction p; intros. exists nil; simpl; auto.
destruct p. exists nil; simpl; auto.
destruct (IHp v0 v). unfold connected_by_path, good_upath in H.
destruct H. destruct H. destruct H0.
split. split. apply H.
unfold upath_prop in *; rewrite Forall_forall in *. intros. apply H1. apply in_cons. apply H3.
split. simpl; auto. rewrite <- (last_error_cons (v0::p) a). apply H2. unfold not; intros; inversion H3.
assert (adjacent g a v0). apply H. destruct H1.
exists (x0::x).
split. apply H1. apply H0.
Qed.

Lemma fits_upath_cons:
forall g p l e v v0, fits_upath g (e::l) (v::v0::p) -> fits_upath g l (v0::p).
Proof.
intros; destruct p; destruct l.
simpl. auto.
simpl in H. destruct H. contradiction.
simpl in H. destruct H. contradiction.
simpl in H. destruct H. destruct H0. simpl. split; auto.
Qed.

Lemma fits_upath_evalid:
forall g p l, fits_upath g l p -> forall e, In e l -> evalid g e.
Proof.
induction p; destruct l; intros; try contradiction.
destruct p eqn:Hp. unfold fits_upath in H. contradiction. rename l0 into p'.
destruct l eqn:Hl. unfold fits_upath in H. simpl in H; destruct H.
simpl in H0; destruct H0; try contradiction. rewrite H0 in H. destruct H. apply H.
apply in_inv in H0. destruct H0.
  unfold fits_upath in H. simpl in H; destruct H. rewrite H0 in H. destruct H. apply H.
apply fits_upath_cons in H.
apply (IHp (e1::l0)). apply H. apply H0.
Qed.

(************REACHABLE -> CONNECTED************)

Lemma valid_path'_cons:
  forall (g: PreGraph V E) p a, valid_path' g (a::p) -> valid_path' g p.
Proof.
intros; destruct p. reflexivity.
simpl. simpl in H. destruct H. destruct H0. apply H1.
Qed.

Corollary valid_path_cons:
  forall (g: PreGraph V E) v a l, valid_path g (v,a::l) -> valid_path g (dst g a, l).
Proof.
unfold valid_path; intros. destruct H. destruct l. apply H0.
split. apply H0. apply (valid_path'_cons g (e::l) a H0).
Qed.

Lemma valid_dpath_implies_valid_upath':
  forall g p, valid_path' g p -> valid_upath g (epath_to_vpath' g p).
Proof.
intros. induction p.
simpl. trivial.
assert (valid_path' g p). apply (valid_path'_cons g p a H).
destruct p eqn:H_p. simpl. split.
exists a. split. apply H. left. split; reflexivity.
apply H.
assert (epath_to_vpath' g (a :: e :: l) = (src g a) :: epath_to_vpath' g (e::l)).
simpl. reflexivity.
rewrite H1; clear H1.
apply valid_upath_cons. apply IHp. apply H0.
assert (hd_error (epath_to_vpath' g (e :: l)) = Some (src g e)).
destruct l; reflexivity. rewrite H1.
unfold adjacent_hd. unfold adjacent. exists a.
split. apply H. left. split. reflexivity. apply H.
Qed.

Lemma valid_dpath_implies_valid_upath:
  forall g p, valid_path g p -> valid_upath g (epath_to_vpath g p).
Proof.
intros. unfold epath_to_vpath. destruct p. destruct l.
simpl. apply H. apply valid_dpath_implies_valid_upath'. apply H.
Qed.

Lemma epath_to_vpath_head:
  forall (g: PreGraph V E) p, valid_path g p -> hd_error (epath_to_vpath g p) = Some (phead p).
Proof.
intros. destruct p. destruct l.
-simpl. reflexivity.
-simpl. unfold valid_path in H. destruct H. destruct l; rewrite H; simpl; reflexivity.
Qed.

Lemma pfoot_cons:
  forall (g: PreGraph V E) l e v, valid_path g (v, e::l) -> pfoot g (v,(e::l)) = pfoot g (dst g e, l).
Proof.
intros. destruct l; simpl. reflexivity.
apply (pfoot_head_irrel l g v (dst g e) e0).
Qed.

Lemma epath_to_vpath_foot':
  forall (g: PreGraph V E) l v, valid_path g (v, l) -> last_error (epath_to_vpath g (v,l)) = Some (pfoot g (v,l)).
Proof.
unfold epath_to_vpath; induction l; intros. reflexivity.
destruct l. reflexivity. rewrite pfoot_cons. 2: auto.
assert (valid_path g (dst g a, e::l)). apply H.
rewrite <- IHl. 2: auto.
apply last_error_cons. simpl. unfold not; intros. destruct l; inversion H1.
Qed.

Corollary epath_to_vpath_foot:
  forall (g: PreGraph V E) p, valid_path g p -> last_error (epath_to_vpath g p) = Some (pfoot g p).
Proof.
destruct p. apply epath_to_vpath_foot'.
Qed.

Lemma reachable_implies_connected_by:
  forall g P u v, reachable_by g u P v -> connected_by g P u v.
Proof.
intros. unfold reachable_by in H. destruct H. destruct H. rename x into dp.
exists (epath_to_vpath g dp). split.
split. apply valid_dpath_implies_valid_upath. apply H0.
destruct H0. unfold path_prop in H1. destruct H1.
rewrite Forall_forall in H2.
unfold upath_prop. rewrite Forall_forall. intros.
rewrite (in_path_eq_epath_to_vpath) in H3. unfold In_path in H3.
destruct H3. rewrite H3. apply H1.
destruct H3. destruct H3. specialize (H2 x0 H3). destruct H4; rewrite H4; apply H2.
apply H0.
destruct dp; destruct l. unfold path_ends in H; unfold phead in H; destruct H.
split; simpl. rewrite H; reflexivity.
unfold pfoot in H1. unfold pfoot' in H1. rewrite H1; reflexivity.
unfold path_ends in H. destruct H. unfold phead in H.
split. rewrite H. apply epath_to_vpath_head. rewrite <- H. apply H0.
rewrite epath_to_vpath_foot. rewrite H1. reflexivity. apply H0.
Qed.

Corollary reachable_implies_connected:
  forall g u v, reachable g u v -> connected g u v.
Proof.
intro. apply reachable_implies_connected_by.
Qed.

(************(CONNECTED) COMPONENTS************)

Definition component (g: Gph) (P: Ensemble V):=
  forall u v, P u -> P u -> connected g u v. (*Here we only care about connectedness; and are using P as a set*)

Definition maximal_component (g: Gph) (P: Ensemble V):=
  component g P /\ forall u v, connected g u v -> P u -> P v.
(*
Lemma connected_graph_component:
  forall g P, connected_graph g -> maximal_component g P -> Same_set P (vvalid g).
*)
(************UNDIRECTED CYCLES************)

(*A valid upath is a ucycle if its start and end are the same*)
(*Exclude empty paths?*)
(*Alternative: If any element shows up twice?*)
Definition ucycle (p: upath) := hd_error p = last_error p /\ tail p <> nil.

Lemma ucycle_nil :
  forall p , p = nil -> ~ (ucycle p).
Proof.
unfold not; unfold ucycle; intros. destruct H0.
assert (tail p = nil). rewrite H. auto. contradiction.
Qed.

Lemma ucycle_single:
  forall u, ~ (ucycle (u::nil)).
Proof.
unfold not; unfold ucycle; intros. destruct H.
assert (tail (u::nil) = nil). auto. contradiction.
Qed.

(*This means that all ucycles must be. If self-loop, must be u->u*)

Definition simple_ucycle p := ucycle p /\ NoDup (tail p).

(*which is better?*)

Definition acyclic_ugraph g := forall p, simple_ucycle p -> ~ (valid_upath g p). (*so walking back and forth is an accepted "cycle", but we don't care*)

Definition acyclic_ugraph2 g := forall u v w, connected g u v -> connected g v w -> ~ (adjacent g u w).

(*A forest's more common definition is based on trees, but it's equivalent to an acyclic graph (requires proof)*)
Definition uforest g := acyclic_ugraph g.

Definition spanning_uforest g t := is_partial_graph t g /\ uforest t /\ (forall u v, connected g u v <-> connected t u v).

(*Next problem: graphs can be disconnected. So, the definition of a tree is dependent on components. E.g Prim's returns a tree of the component its root is in

Definition tree' g u :=
  forall v, connected_by g P u v -> (*only one path from u to v. Use NoDup?*).

Definition tree g :=
  forall u, tree' g u.
*)

(**************FINITE GRAPHS************)
(*
Require Import RamifyCoq.graph.graph_gen.
Require Import graph.FiniteGraph.
Lemma empty_pregraph_vvalid:
forall src dst v, ~ vvalid (empty_pregraph src dst) v.
Proof. simpl; auto. Qed.

Lemma empty_pregraph_evalid:
forall src dst e, ~ evalid (empty_pregraph src dst) e.
Proof. simpl; auto. Qed.

Definition finite_empty_pregraph src dst:
FiniteGraph (empty_pregraph src dst).
Proof.
constructor; unfold EnumEnsembles.Enumerable, In; exists nil; split.
apply NoDup_nil.
intros; split; auto.
apply NoDup_nil.
intros; split; auto.
Qed.


Definition finite_pregraph_add_edge g {fg: FiniteGraph g} e u v:
FiniteGraph (pregraph_add_edge g e u v).
Proof.
destruct fg. unfold EnumEnsembles.Enumerable, In in finiteV. unfold EnumEnsembles.Enumerable, In in finiteE.
constructor; unfold EnumEnsembles.Enumerable, In.
destruct finiteV as [vl Hvl]. exists vl. apply Hvl.
destruct finiteE as [el Hel]. simpl; unfold addValidFunc.
*)

End UNDIRECTED.