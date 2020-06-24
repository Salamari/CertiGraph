(*Looted and modified from graph/path_lemmas.v
Idea is with a definition of connectedness, there's no need to explicitly define an undirected graph
Which sort of makes sense I guess, because every directed graph has an underlying undirected graph by just removing the direction
And directed graphs make more sense in C compared to ugraphs (correct me if I'm wrong)
*)
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
Require Import Coq.Logic.ProofIrrelevance.
Require Import RamifyCoq.lib.Ensembles_ext.
(*Require Import RamifyCoq.lib.Coqlib.*)
(*Require Import RamifyCoq.lib.EnumEnsembles.*)
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.path_lemmas.

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
Definition adj_edges g u v := fun e => adj_edge g e u v.

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

Lemma hd_error_app:
  forall {A:Type} (l2 l1: list A) (a: A), hd_error l1 = Some a -> hd_error (l1++l2) = Some a.
Proof.
induction l1; intros. inversion H. simpl. simpl in H. auto.
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

Lemma valid_upath_app_split:
  forall g p p', valid_upath g (p++p') -> (valid_upath g p /\ valid_upath g p').
Proof.
induction p; intros. simpl in H. split. simpl. auto. apply H.
destruct p. destruct p'. simpl in *. split; auto. simpl in H. destruct H. destruct H. destruct H.
split. simpl. destruct H. destruct H1; destruct H1. rewrite <- H1. apply H2. rewrite <- H3. apply H2.
apply H0.
destruct H. apply IHp in H0. split. split. apply H. apply H0. apply H0.
Qed.

Lemma valid_upath_rev:
  forall g p, valid_upath g p -> valid_upath g (rev p).
Proof.
induction p; intros. auto.
simpl. apply valid_upath_concat. apply IHp. apply (valid_upath_tail' g p a H).
rewrite <- rev_hd_last. destruct p. apply H.
simpl. destruct H. apply adjacent_symm. apply H.
Qed.

Definition connected_by_path (g: Gph) (p: upath) (n : V) :=
  fun n' => valid_upath g p /\ hd_error p = Some n /\ last_error p = Some n'.

Definition connected (g: Gph) (n : V) :=
  fun n' => exists p, connected_by_path g p n n'.

Lemma connected_exists_path:
  forall (g: Gph) u v,
    connected g u v <->
    exists p, 
      valid_upath g p /\
      hd_error p = Some u /\ last_error p = Some v.
Proof. intros; split; intros; auto. Qed.

Lemma connected_symm:
  forall g u v, connected g u v -> connected g v u.
Proof.
unfold connected; unfold connected_by_path; intros.
destruct H. rename x into p. exists (rev p). split. apply valid_upath_rev. apply H.
split. rewrite <- (rev_involutive p) in H. rewrite <- rev_hd_last in H. apply H.
rewrite rev_hd_last in H. apply H.
Qed.

Lemma connected_refl:
forall g v, vvalid g v -> connected g v v.
Proof.
intros. exists (v::nil). split. simpl; auto.
split; simpl; auto.
Qed.

Lemma connected_trans:
  forall g u v w, connected g u v -> connected g v w -> connected g u w.
Proof.
unfold connected; unfold connected_by_path; intros.
destruct H; rename x into p0. destruct H0; rename x into p1.
destruct H. destruct H1. destruct H0. destruct H3.
exists (p0++(tail p1)). split. apply valid_upath_app_2. apply H. apply H0.
rewrite H3. rewrite H2. reflexivity.
split. assert (p0 = u::(tl p0)). apply hd_error_tl_repr. split. apply H1. reflexivity.
rewrite H5. rewrite <- app_comm_cons. simpl. reflexivity.
destruct p1 eqn:H5. inversion H4.
destruct u0. simpl in *. rewrite <- app_nil_end. rewrite <- H4. rewrite H3. apply H2.
simpl. apply last_err_app. simpl in H4. simpl. apply H4.
Qed.

Lemma adjacent_connected:
  forall g u v, adjacent g u v -> connected g u v.
Proof.
intros. exists (u::v::nil). split. split. auto.
simpl. destruct H. destruct H. destruct H.
destruct H0; destruct H0. rewrite <- H2; apply H1. rewrite <- H0; apply H1.
split; simpl; auto.
Qed.

Lemma connected_by_path_vvalid:
forall g p u v, connected_by_path g p u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H. destruct H0.
split. apply (valid_upath_vvalid g p u). auto. apply hd_error_In; auto.
apply (valid_upath_vvalid g p v). auto. apply last_error_In; auto.
Qed.

Corollary connected_vvalid:
  forall g u v, connected g u v -> vvalid g u /\ vvalid g v.
Proof.
intros. destruct H as [p ?]. apply (connected_by_path_vvalid _ _ _ _ H).
Qed.

Definition connected_graph (g: Gph) := forall u v, vvalid g u -> vvalid g v -> connected g u v.

(************REASONING ABOUT A SPECIFIC LIST OF EDGES************)

Fixpoint fits_upath g (l: list E) (p: upath) :=
match l, p with
| nil, nil => True
| nil, v::nil => True
| e::l', u::v::p' => adj_edge g e u v /\ fits_upath g l' (v::p')
| _, _ => False
end.

Lemma valid_upath_exists_list_edges:
forall g p, valid_upath g p-> exists l, fits_upath g l p.
Proof.
induction p; intros. exists nil; simpl; auto.
destruct p. exists nil; simpl; auto.
destruct H. destruct H. apply IHp in H0. destruct H0 as [l ?].
exists (x::l). split; auto.
Qed.

Lemma valid_upath_exists_list_edges':
forall g p, (forall v, In v p -> vvalid g v) -> (exists l, fits_upath g l p) -> valid_upath g p.
Proof.
induction p; intros. simpl. auto.
destruct p. simpl. apply H. left; auto.
destruct H0 as [l ?]. destruct l. simpl in H0; contradiction. destruct H0.
split. exists e; apply H0. apply IHp.
intros; apply H. right; apply H2.
exists l. apply H1.
Qed.

Corollary connected_exists_list_edges:
forall g p u v, connected_by_path g p u v -> exists l, fits_upath g l p.
Proof.
intros. destruct H. apply valid_upath_exists_list_edges. apply H.
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

Lemma reachable_implies_connected:
  forall g u v, reachable g u v -> connected g u v.
Proof.
intros. unfold reachable_by in H. destruct H. destruct H. rename x into dp.
exists (epath_to_vpath g dp). split.
apply valid_dpath_implies_valid_upath. apply H0.
destruct H0. clear H1.
destruct dp; destruct l. unfold path_ends in H; unfold phead in H; destruct H.
split; simpl. rewrite H; reflexivity.
unfold pfoot in H1. unfold pfoot' in H1. rewrite H1; reflexivity.
unfold path_ends in H. destruct H. unfold phead in H.
split. rewrite H. apply epath_to_vpath_head. rewrite <- H. apply H0.
rewrite epath_to_vpath_foot. rewrite H1. reflexivity. apply H0.
Qed.

(************(CONNECTED) COMPONENTS************)

Definition component (g: Gph) :=
  forall u v, connected g u v. (*Here we only care about connectedness; and are using as a set*)

Definition maximal_component (g: Gph):=
  component g /\ forall u v, connected g u v.
(*
Lemma connected_graph_component:
  forall g P, connected_graph g -> maximal_component g -> Same_set P (vvalid g).
*)

(************UFOREST************)

(*Use wiki/Bender & Williamson 2010's definition. Defining a cycle is troublesome because
1. have to deal with negations in definition of uforest
2. we support multiple edges btwn vertices, if so are they a cycle?
For the purposes of kruskal, we need uforest more than cycles*)

Definition simple_upath g p := valid_upath g p /\ NoDup p.

Lemma simple_upath_app_split:
  forall g p p', simple_upath g (p++p') -> (simple_upath g p /\ simple_upath g p').
Proof.
intros. destruct H. split; split.
apply (valid_upath_app_split _ _ _ H). apply (NoDup_app_l _ _ _ H0).
apply (valid_upath_app_split _ _ _ H). apply (NoDup_app_r _ _ _ H0).
Qed.

Lemma last_err_split2:
forall {A: Type} (l1 l2: list A) (a: A),
last_error (l1++a::l2) = last_error (a::l2).
induction l1; intros. rewrite app_nil_l; auto.
replace (last_error ((a :: l1) ++ a0 :: l2)) with (last_error (l1 ++ a0 :: l2)).
2: { simpl. destruct (l1++a0::l2) eqn:Htmp.
  apply app_eq_nil in Htmp. destruct Htmp. inversion H0. auto. }
apply IHl1.
Qed.

Lemma upath_simplifiable:
  forall g p u v, connected_by_path g p u v-> exists p', connected_by_path g p' u v /\ simple_upath g p' /\ incl p' p.
Proof.
induction p; intros.
destruct H. destruct H0. inversion H0.
destruct p. destruct H. simpl in H. simpl in H0; destruct H0.
inversion H0; inversion H1. subst u; subst v. clear H0 H1.
exists (a::nil). split. split. simpl; auto. simpl; split; auto.
split. split. simpl; auto. apply NoDup_cons. auto. apply NoDup_nil.
unfold incl; intros; auto.
destruct H. destruct H0. destruct H.
assert (connected_by_path g (v0::p) v0 v). split. auto. split. apply hd_error_cons. rewrite last_error_cons in H1; auto. unfold not; intros. inversion H3.
apply IHp in H3. destruct H3 as [p' ?]. destruct H3.
destruct (in_dec EV a p').
apply in_split in i. destruct i as [l1 [l2 ?]].
subst p'. exists (a::l2). split.
destruct H3. destruct H5. split. apply (valid_upath_app_split g l1 _).
apply H3. split. simpl in H0; simpl; apply H0.
rewrite last_err_split2 in H6. auto. destruct H4. split. apply simple_upath_app_split in H4; apply H4.
unfold incl; intros. destruct H6. subst a0. left; auto.
right. apply H5. apply in_or_app. right; right; apply H6.
exists (a::p'). split. destruct H3. destruct H5. split. apply valid_upath_cons. auto.
rewrite H5. unfold adjacent_hd. apply H.
split. simpl in H0; simpl; auto.
rewrite last_error_cons. auto. unfold not; intros. subst p'. inversion H5.
split. split. destruct H3. destruct H5. apply valid_upath_cons. auto. rewrite H5. unfold adjacent_hd. auto.
apply NoDup_cons. auto. apply H4.
unfold incl; intros. destruct H5. subst a0. left; auto. destruct H4. right; apply H6. auto.
Qed.

Lemma fits_upath_split:
forall g p1 p2 l, fits_upath g l (p1++p2) -> exists l1 l2 l3, fits_upath g l1 p1 /\ fits_upath g l3 p2 /\ l = (l1++l2++l3).
Proof.
induction p1; intros.
rewrite app_nil_l in H. exists nil. exists nil. exists l. split. simpl; auto. split; simpl; auto.
destruct p1. destruct l. destruct p2.
exists nil; exists nil; exists nil. split. simpl; auto. split; simpl; auto.
simpl in H. contradiction.
replace ((a :: nil) ++ p2) with (a::p2) in H. 2: simpl; auto.
destruct p2. simpl in H; contradiction.
destruct H. exists nil. exists (e::nil). exists l. split; simpl; auto.
destruct l. simpl in H; contradiction.
destruct H. apply IHp1 in H0. destruct H0 as [l1 [l2 [l3 [? [? ?]]]]].
exists (e::l1). exists l2. exists l3. split. split; auto. split. auto. simpl. rewrite H2. auto.
Qed.

Lemma upath_simplifiable_edges:
  forall g p l u v, connected_by_path g p u v -> fits_upath g l p ->
    exists p' l', connected_by_path g p' u v /\ simple_upath g p' /\ incl p' p
      /\ fits_upath g l' p' /\ incl l' l.
Proof.
induction p; intros.
destruct H. destruct H1. inversion H1.
destruct p. destruct H. simpl in H. simpl in H1; destruct H1.
inversion H1; inversion H2. subst u; subst v. clear H1 H2.
destruct l. 2: { simpl in H0; contradiction. }
exists (a::nil). exists nil. split. split. simpl; auto. simpl; split; auto.
split. split. simpl; auto. apply NoDup_cons. auto. apply NoDup_nil.
unfold incl; intros; auto.
(*inductive step*)
destruct l. simpl in H0; contradiction.
destruct H as [? [? ?]]. destruct H.
assert (connected_by_path g (v0::p) v0 v). split. auto. split. apply hd_error_cons. rewrite last_error_cons in H2; auto. unfold not; intros. inversion H4.
destruct H0. apply (IHp l v0 v H4) in H5. destruct H5 as [p' ?]. destruct H5 as [l' [? [? [? [? ?]]]]].
destruct (in_dec EV a p').
(*if a is already inside p, then we take the subpath.*)
apply in_split in i. destruct i as [p1 [p2 ?]]. subst p'.
exists (a::p2). (*split l'*)
apply fits_upath_split in H8. destruct H8 as [l1 [l2 [l3 [? [? ?]]]]].
exists l3. split. split. destruct H6. apply valid_upath_app_split in H6. apply H6.
split. simpl in H1. simpl. apply H1. destruct H5. destruct H12.
rewrite last_err_split2 in H13. auto. split.
apply simple_upath_app_split in H6. apply H6. split.
unfold incl; intros. destruct H12. subst a0. left; auto.
right. apply H7. apply in_or_app. right. right. auto.
split. auto. unfold incl; intros. right. apply H9. subst l'. apply in_or_app. right. apply in_or_app. auto.
(*case where a isn't inside. Then straightforward concat*)
exists (a::p'). exists (e::l').
split. split.
destruct p'. simpl. apply (adjacent_requires_vvalid g a v0). auto.
destruct H5. destruct H10. simpl in H10. inversion H10. subst v1.
split; auto.
split. simpl in H1. simpl. auto.
destruct H5. destruct H10.
rewrite last_error_cons. auto. unfold not; intros; subst p'. inversion H10.
split. split.
destruct p'. simpl. apply (adjacent_requires_vvalid g a v0). auto.
destruct H5. destruct H10. simpl in H10. inversion H10. subst v1. split; auto.
apply NoDup_cons. auto. apply H6.
split.
unfold incl; intros. destruct H10. subst a0. left; auto. right; apply H7. auto.
split. destruct H5. destruct H10. destruct p'. inversion H10.
inversion H10. subst v1. split; auto.
unfold incl; intros. destruct H10. subst a0. left. auto. right. apply H9. auto.
Qed.

Lemma connected_by_upath_exists_simple_upath:
  forall g p u v, connected_by_path g p u v-> exists p', connected_by_path g p' u v /\ simple_upath g p'.
Proof.
induction p; intros.
destruct H. destruct H0. inversion H0.
destruct p. destruct H. simpl in H. simpl in H0; destruct H0.
inversion H0; inversion H1. subst u; subst v. clear H0 H1.
exists (a::nil). split. split. simpl; auto. simpl; split; auto.
split. simpl; auto. apply NoDup_cons. auto. apply NoDup_nil.
destruct H. destruct H0. destruct H.
assert (connected_by_path g (v0::p) v0 v). split. auto. split. apply hd_error_cons. rewrite last_error_cons in H1; auto. unfold not; intros. inversion H3.
apply IHp in H3. destruct H3 as [p' ?]. destruct H3.
destruct (in_dec EV a p').
apply in_split in i. destruct i as [l1 [l2 ?]].
subst p'. exists (a::l2). split.
destruct H3. destruct H5. split. apply (valid_upath_app_split g l1 _).
apply H3. split. simpl in H0; simpl; apply H0.
rewrite last_err_split2 in H6. auto. apply simple_upath_app_split in H4; apply H4.
exists (a::p'). split. destruct H3. destruct H5. split. apply valid_upath_cons. auto.
rewrite H5. unfold adjacent_hd. apply H.
split. simpl in H0; simpl; auto.
rewrite last_error_cons. auto. unfold not; intros. subst p'. inversion H5.
split. destruct H3. destruct H5. apply valid_upath_cons. auto. rewrite H5. unfold adjacent_hd. auto.
apply NoDup_cons. auto. apply H4.
Qed.

(*barebones, this has a lot of loopholes*)
Definition uforest g :=
  (forall u v p1 p2,
  simple_upath g p1 -> connected_by_path g p1 u v ->
  simple_upath g p2 -> connected_by_path g p2 u v ->
  p1 = p2).

Definition sound_uforest g :=
  (forall e, evalid g e -> src g e <> dst g e) /\ (*No self-cycles*)
  (forall u v e1 e2, adj_edge g e1 u v /\ adj_edge g e2 u v -> e1 = e2) /\ (*Not a multigraph, preventing internal cycles within two vertices*)
  (forall e, evalid g e -> strong_evalid g e) /\ (*with no rubbish edges. Debatable where this should go?*)
  uforest g. (*finally, the actual forest definition*)

Lemma trivial_path1:
forall g e, strong_evalid g e -> connected_by_path g ((src g e)::(dst g e)::nil) (src g e) (dst g e) /\
fits_upath g (e::nil) ((src g e)::(dst g e)::nil).
Proof.
intros. split.
split. simpl. split. exists e. split. auto. left; auto. apply H.
simpl. auto.
simpl. split; auto. split. apply H. left; auto.
Qed.

(*Annnd even with the extra restrictions I STILL can't prove this
I'm going about this the wrong way. I need to convert p,l into a simple_upath p' l'
THEN I can use the fact that p' must be (u::v::nil) by uforest.
And because e::nil fits (u::v::nil), any lpath must be e::nil (prove this)
THEN e is in l', and by above we have incl l' l, thus e is in l
*)
Lemma forest_edge':
forall p l g e, sound_uforest g -> strong_evalid g e -> connected_by_path g p (src g e) (dst g e) ->
fits_upath g l p -> In e l.
Proof.
intros. pose proof (upath_simplifiable_edges g p l (src g e) (dst g e) H1 H2).
destruct H3 as [p' [l' [? [? [? [? ?]]]]]].
pose proof (trivial_path1 g e H0). destruct H8 as [? ?].
assert (simple_upath g ((src g e)::(dst g e)::nil)). split. apply H8. apply NoDup_cons.
unfold not; intros; destruct H10. symmetry in H10. apply H in H10. contradiction. apply H0.
simpl in H10; contradiction.
apply NoDup_cons. unfold not; intros. simpl in H10; contradiction. apply NoDup_nil.
assert (p' = (src g e :: dst g e :: nil)). destruct H as [? [? [? ?]]]. apply (H13 (src g e) (dst g e)); auto.
subst p'. apply H7.
destruct l'. simpl in H6; contradiction.
destruct l'. 2: { simpl in H6. destruct H6. contradiction. }
left. destruct H9. destruct H6.
destruct H as [? [? ?]]. apply (H13 (src g e) (dst g e)). split; auto.
Qed.

Definition spanning t g :=
  forall u v, connected g u v <-> connected t u v.

Lemma spanning_preserves_vertices:
forall g t v, spanning t g -> (vvalid g v <-> vvalid t v).
Proof.
intros; split; intros; pose proof (connected_refl _ v H0);
apply H in H1; apply connected_vvalid in H1; apply H1.
Qed.

Definition spanning_uforest t g :=
  is_partial_graph t g /\ (*t is a partial graph of g*)
  sound_uforest t /\ (*it is also a forest*)
  spanning t g. (*that is spanning...*)

End UNDIRECTED.