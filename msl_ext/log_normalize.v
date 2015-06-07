Require Import RamifyCoq.msl_ext.seplog.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Local Open Scope logic.

Lemma ocon_sep_true: forall {A} `{OverlapSepLog A} (P Q: A), ocon P Q |-- P * TT.
Proof.
  intros.
  eapply derives_trans.
  + apply ocon_derives; [apply derives_refl | apply TT_right].
  + rewrite ocon_TT.
    apply derives_refl.
Qed.

Lemma exp_allp: forall {A} `{NatDed A} (S T: Type) (P: S -> T -> A),
    exp (fun s => allp (P s)) |-- allp (fun t => exp (fun s => P s t)).
Proof.
  intros.
  apply exp_left; intro s.
  apply allp_right; intro t.
  apply (exp_right s).
  eapply allp_left.
  apply derives_refl.
Qed.

Lemma precise_sepcon_cancel_right: forall {A} `{PreciseSepLog A} P Q R, precise P -> Q * P |-- R * P -> Q |-- R.
Proof.
  intros.
  rewrite !(sepcon_comm _ P) in H1.
  eapply precise_sepcon_cancel_left; eauto.
Qed.

Lemma precise_wand_sepcon: forall {A} `{PreciseSepLog A} P Q, precise P -> P -* (P * Q) = Q.
Proof.
  intros.
  apply pred_ext.
  + apply precise_sepcon_cancel_left with P; auto.
    apply modus_ponens_wand.
  + apply wand_sepcon_adjoint.
    rewrite sepcon_comm.
    apply derives_refl.
Qed.

Lemma precise_andp_left: forall {A} `{PreciseSepLog A} P Q, precise P -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with P; auto.
  apply andp_left1; auto.
Qed.

Lemma precise_andp_right: forall {A} `{PreciseSepLog A} P Q, precise Q -> precise (P && Q).
Proof.
  intros.
  apply derives_precise with Q; auto.
  apply andp_left2; auto.
Qed.

Lemma exp_sepcon: forall {A} `{SepLog A} {B} (P Q: B -> A), exp (P * Q) |-- exp P * exp Q.
Proof.
  intros.
  apply exp_left; intro.
  simpl.
  apply sepcon_derives; apply (exp_right x); apply derives_refl.
Qed.

Lemma precise_exp_sepcon: forall {A} `{PreciseSepLog A} {B} (P Q: B -> A), precise (exp P) -> precise (exp Q) -> precise (exp (P * Q)).
Proof.
  intros.
  eapply derives_precise.
  + apply exp_sepcon.
  + apply precise_sepcon; auto.
Qed.

Lemma mapsto_precise: forall {AV} {A} `{PreciseSepLog A} {MSL: MapstoSepLog AV A} p v , precise (mapsto p v).
Proof.
  intros.
  eapply derives_precise; [| apply mapsto__precise].
  apply (exp_right v).
  apply derives_refl.
Qed.

Lemma precise_weak_conflict: forall {A} {ND: NatDed A} {SL: SepLog A} {CSL: ClassicalSep A} {PSL: PreciseSepLog A} {OSL: OverlapSepLog A} P, precise P -> P * P |-- emp.
Proof.
  intros.
  pose proof sepcon_ocon P P.
  rewrite precise_ocon_self in H0 by auto.
  rewrite <- sepcon_emp in H0.
  apply precise_sepcon_cancel_left in H0; [| auto].
  eapply derives_trans; [apply sepcon_derives; exact H0 |].
  rewrite sepcon_emp.
  apply derives_refl.
Qed.

