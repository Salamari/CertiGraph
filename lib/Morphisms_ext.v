Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.Morphisms.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.Equivalence_ext.

Definition app_sig {A B: Type} (P: A -> Prop) (f: A -> B): sig P -> B := fun a => f (proj1_sig a).

Definition guarded_pointwise_relation {A B : Type} (P: A -> Prop) (R : relation B) : relation (A -> B) :=
  respectful_relation (app_sig P) (pointwise_relation (sig P) R).

Instance guarded_pointwise_equivalence {A B : Type} (P: A -> Prop) {R : relation B} {EqR: Equivalence R}: Equivalence (guarded_pointwise_relation P R).
Proof.
  apply resp_Equivalence.
  apply pointwise_equivalence.
  auto.
Defined.

Definition guarded_pointwise_relation_spec: forall {A B : Type} (P: A -> Prop) (R : relation B) f g, guarded_pointwise_relation P R f g <-> (forall x: A, P x -> R (f x) (g x)).
Proof.
  intros.
  unfold guarded_pointwise_relation, respectful_relation, app_sig, pointwise_relation.
  split; intros.
  + specialize (H (exist P x H0)).
    exact H.
  + destruct a.
    specialize (H x p).
    exact H.
Qed.

Lemma guarded_pointwise_relation_pointwise_relation: forall {A B : Type} (P: A -> Prop) (R : relation B), inclusion _ (pointwise_relation A R) (guarded_pointwise_relation P R).
Proof.
  intros.
  hnf; intros.
  rewrite guarded_pointwise_relation_spec.
  intros.
  apply H.
Qed.