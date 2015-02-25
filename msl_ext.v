Require Import msl.msl_direct.
Require Import ramify_tactics.
Require Import utilities.
Require Import Permutation.

Lemma overlapping_eq {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}
      {CaA : Canc_alg A} {CrA : Cross_alg A} {DA : Disj_alg A}:
  forall h1 h2 h3 i1 i2 i3 i12 i23 w1 w2,
    join h1 h2 i12 -> join h2 h3 i23 -> join i12 h3 w1 -> join i1 i2 i12 -> join i2 i3 i23 -> join i12 i3 w2 -> w1 = w2.
Proof.
  intros; try_join h2 h3 h23'; equate_join i23 h23'; try_join i2 i3 i23'; equate_join i23 i23'.
  destruct (cross_split h1 h2 i1 i2 i12 H H2) as [[[[h1i1 h1i2] h2i1] h2i2] [? [? [? ?]]]].
  try_join h1i2 i3 i3'; try_join i3 h2i2 i23'; try_join h1i2 h1 h1'; try_join h1i2 h1i2 x.
  generalize (join_self H17); intro Heq; rewrite <- Heq in *; clear Heq x;
  assert (Hid1: unit_for h1i2 h1i2) by apply H17; rewrite <- identity_unit_equiv in Hid1.

  try_join h2i1 h3 h3'; try_join h3 h2i2 h23; try_join h2i1 i1 i1'; try_join h2i1 h2i1 x;
  generalize (join_self H25); intro Heq; rewrite <- Heq in *; clear Heq x;
  assert (Hid2: unit_for h2i1 h2i1) by apply H25; rewrite <- identity_unit_equiv in Hid2.
  repeat match goal with
           | [H1: identity ?X, H2: join ?X _ _ |- _] => apply H1 in H2; rewrite H2 in *; clear H2
           | [H1: identity ?X, H2: join _ ?X _ |- _] => apply join_comm in H2; apply H1 in H2; rewrite H2 in *; clear H2
         end.
  equate_join w1 w2; apply eq_refl.
Qed.

Lemma overlapping_join_eq {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CaA : Canc_alg A} {DA : Disj_alg A}:
  forall h1 h2 h3 h4 h12 h23 w, join h1 h2 h12 -> join h2 h3 h23 -> join h12 h3 w -> join h12 h4 h23 -> h23 = w.
Proof.
  intros. try_join h2 h3 h23'; equate_join h23 h23'. assertSub h1 h23 HS. assert (emp h1).
  apply join_sub_joins_identity with h23; auto. exists w; auto. apply join_unit1_e with h1; auto.
Qed.

Arguments overlapping_join_eq [A] [JA] [PA] [SA] [CaA] [DA] [h1] [h2] [h3] [h4] [h12] [h23] [w] _ _ _ _.

Lemma precise_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} :
  forall P Q, precise P -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H0 H1 H2 H3); tauto. Qed.

Lemma precise_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} :
  forall P Q, precise Q -> precise (P && Q).
Proof. intros; intro; intros; destruct H0; destruct H1; generalize (H w w1 w2 H4 H5 H2 H3); tauto. Qed.

Lemma precise_orp {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} :
  forall P Q, (forall w1 w2: A, ~ (P w1 /\ Q w2)) -> precise P -> precise Q -> precise (P || Q).
Proof.
  intros P Q Hfalse H H0; intro; intros.
  destruct H1; destruct H2. generalize (H w w1 w2 H1 H2 H3 H4); tauto.
  specialize (Hfalse w1 w2); destruct Hfalse; intuition.
  specialize (Hfalse w2 w1); destruct Hfalse; intuition.
  generalize (H0 w w1 w2 H1 H2 H3 H4); tauto.
Qed.

Lemma precise_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} :
  forall P Q, precise Q -> precise P -> precise (P * Q).
Proof.
  repeat intro; destruct H1 as [w11 [w12 [? [? ?]]]], H2 as [w21 [w22 [? [? ?]]]].
  assert (w11 = w21) by (apply join_join_sub in H1; generalize (join_sub_trans H1 H3); intro;
                         apply join_join_sub in H2; generalize (join_sub_trans H2 H4); intro;
                         hnf in H0; apply H0 with (w := w); trivial).
  assert (w12 = w22) by (apply join_join_sub' in H1; generalize (join_sub_trans H1 H3); intro;
                         apply join_join_sub' in H2; generalize (join_sub_trans H2 H4); intro;
                         hnf in H; apply H with (w := w); trivial).
  rewrite H9 in *; rewrite H10 in *; equate_join w1 w2; auto.
Qed.

Lemma sepcon_combine {A} {JA : Join A}: forall p q r s : pred A, p = q -> r = s -> (p * r)%pred = (q * s)%pred.
Proof. intros. subst. auto. Qed.

Lemma precise_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}  B:
  forall P Q: B -> pred A, precise (exp P) -> precise (exp Q) -> precise (EX x : B, P x * Q x).
Proof.
  repeat intro.
  destruct H1 as [x [w11 [w12 [? [? ?]]]]]; destruct H2 as [y [w21 [w22 [? [? ?]]]]].
  specialize (H w w11 w21); specialize (H0 w w12 w22).
  assert (w11 = w21) by (apply H; [exists x; auto | exists y; auto |
                                   apply join_sub_trans with (b := w1); apply join_join_sub in H1; auto |
                                   apply join_sub_trans with (b := w2); apply join_join_sub in H2; auto]).
  assert (w12 = w22) by (apply H0; [exists x; auto | exists y; auto |
                                    apply join_sub_trans with (b := w1); apply join_join_sub' in H1; auto |
                                    apply join_sub_trans with (b := w2); apply join_join_sub' in H2; auto]).
  rewrite H9 in *; rewrite H10 in *; equate_join w1 w2; auto.
Qed.

Lemma precise_tri_exp_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}  B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, Q x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_andp_left {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}  B:
  forall (P Q: B -> B -> B -> pred A),
    precise (EX x : B, EX y : B, EX z : B, P x y z) ->
    precise (EX x : B, EX y : B, EX z : B, P x y z && Q x y z).
Proof.
  repeat intro; destruct H0 as [x1 [y1 [z1 [? ?]]]], H1 as [x2 [y2 [z2 [? ?]]]];
  hnf in H; apply H with (w := w); [exists x1, y1, z1 | exists x2, y2, z2 | | ]; auto.
Qed.

Lemma precise_tri_exp_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}  B:
  forall (P Q R: B -> pred A),
    precise (exp P) -> precise (exp Q) -> precise (exp R) -> precise (EX x : B, EX y : B, EX z : B, P x * Q y * R z).
Proof.
  repeat intro; destruct H2 as [x1 [y1 [z1 [h1 [h2 [? [[i1 [i2 [? [? ?]]]] ?]]]]]]];
  destruct H3 as [x2 [y2 [z2 [j1 [j2 [? [[k1 [k2 [? [? ?]]]] ?]]]]]]].
  assert (i1 = k1) by (hnf in H; apply H with (w := w);
                       [exists x1 | exists x2; auto | assertSub i1 w Hsub | assertSub k1 w Hsub]; auto).
  assert (i2 = k2) by (hnf in H0; apply H0 with (w := w);
                       [exists y1 | exists y2; auto | assertSub i2 w Hsub | assertSub k2 w Hsub]; auto).
  rewrite H14 in *; rewrite H15 in *; equate_join h1 j1.
  assert (h2 = j2) by (hnf in H1; apply H1 with (w := w);
                       [exists z1 | exists z2; auto | assertSub h2 w Hsub | assertSub j2 w Hsub]; auto).
  rewrite H10 in *; equate_join w1 w2; auto.
Qed.

Lemma join_together {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A}
      {CaA : Canc_alg A} {CrA : Cross_alg A} {DA : Disj_alg A}:
  forall p q m n w i, join p q w -> join m n w -> join p m i -> exists j, join i j w.
Proof.
  intros; destruct_cross w. try_join pm m pmm. try_join pm pm pmpm. apply join_self in H8. subst. apply join_comm in H6.
  generalize (join_canc H9 H6); intro. subst. equate_join m pmm. apply unit_identity in H4. apply (join_unit1_e pn p H4) in H2.
  subst. try_join p m i'. equate_join i i'. apply join_comm in H8. exists qn. auto.
Qed.

Arguments join_together [A] [JA] [PA] [SA] [CaA] [CrA] [DA] [p] [q] [m] [n] [w] [i] _ _ _.

Definition sepcon_unique {A : Type} {JA : Join A} {B : Type} (p : B -> pred A) : Prop := forall x w, ~ (p x * p x)%pred w.

Fixpoint iter_sepcon {A : Type} {JA : Join A} {B : Type} (l : list B) (p : B -> pred A) : pred A :=
  match l with
    | nil => emp
    | x :: xl => (p x * iter_sepcon xl p)%pred
  end.

Lemma iter_sepcon_app_sepcon {A : Type} {JA : Join A} {B : Type} {PA : Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A}:
  forall (l1 l2 : list B) (p : B -> pred A), iter_sepcon (l1 ++ l2) p = (iter_sepcon l1 p * iter_sepcon l2 p)%pred.
Proof.
  induction l1; intros; apply pred_ext; intro w; intros. rewrite app_nil_l in H. simpl. rewrite emp_sepcon. auto.
  simpl in H. rewrite emp_sepcon in H. rewrite app_nil_l. auto. rewrite <- app_comm_cons in H. simpl in H. destruct_sepcon H h.
  rewrite (IHl1 l2 p) in H1. destruct_sepcon H1 i. try_join h1 i1 h1i1. apply join_comm in H5. exists h1i1, i2.
  do 2 (split; auto). apply join_comm in H4. exists h1, i1. split; auto. rewrite <- app_comm_cons. simpl. destruct_sepcon H h.
  simpl in H0. destruct_sepcon H0 i. try_join i2 h2 i2h2. exists i1, i2h2. do 2 (split; auto). rewrite (IHl1 l2 p).
  exists i2, h2. split; auto.
Qed.

Lemma iter_sepcon_app_comm {A : Type} {JA : Join A} {B : Type} {PA : Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A}:
  forall (l1 l2 : list B) (p : B -> pred A), iter_sepcon (l1 ++ l2) p = iter_sepcon (l2 ++ l1) p.
Proof. intros. do 2 rewrite iter_sepcon_app_sepcon. rewrite sepcon_comm. auto. Qed.

Lemma iter_sepcon_permutation {A : Type} {JA : Join A} {B : Type} {PA : Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A}:
  forall  (l1 l2 : list B) (p : B -> pred A), Permutation l1 l2 -> iter_sepcon l1 p = iter_sepcon l2 p.
Proof.
  intro l1. remember (length l1). assert (length l1 <= n) by intuition. clear Heqn. revert l1 H. induction n; intros.
  destruct l1. apply Permutation_nil in H0. subst; auto. simpl in H; inversion H. destruct l1. apply Permutation_nil in H0.
  subst; auto. assert (In b l2) by (apply Permutation_in with (b :: l1); [auto | apply in_eq]). apply in_split in H1.
  destruct H1 as [ll1 [ll2 ?]]. subst. generalize (Permutation_middle ll1 ll2 b); intro. apply Permutation_sym in H1.
  generalize (Permutation_trans H0 H1); intro. apply Permutation_cons_inv in H2.
  assert (iter_sepcon l1 p = iter_sepcon (ll1 ++ ll2) p). apply IHn. simpl in H; intuition. auto.
  assert (iter_sepcon (ll1 ++ b :: ll2) p = iter_sepcon (b :: ll2 ++ ll1) p). rewrite iter_sepcon_app_comm.
  rewrite app_comm_cons. auto. rewrite H4. simpl. apply sepcon_combine. auto. rewrite iter_sepcon_app_comm. auto.
Qed.

Lemma iter_sepcon_unique_nodup {A : Type} {JA : Join A} {PA : Perm_alg A} {SA : Sep_alg A} {CA : Canc_alg A}
      {B : Type} {p : B -> pred A} {w : A} {l : list B}: sepcon_unique p -> iter_sepcon l p w -> NoDup l.
Proof.
  intro. revert w;  induction l; intros. apply NoDup_nil. simpl in H0. destruct_sepcon H0 w. apply NoDup_cons.
  intro. destruct (in_split a l H3) as [l1 [l2 ?]]. rewrite H4 in H2. rewrite iter_sepcon_app_comm in H2.
  rewrite <- app_comm_cons in H2. simpl in H2. destruct_sepcon H2 h. try_join w1 h1 w1h1. assert ((p a * p a)%pred w1h1).
  exists h1, w1; split; auto. apply H in H9. auto. apply (IHl w2); auto.
Qed.

Lemma precise_iter_sepcon {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A} {B : Type}:
  forall (p : B -> pred A), (forall z, precise (p z)) -> forall (l : list B), precise (iter_sepcon l p).
Proof. intros; induction l; simpl. apply precise_emp. apply precise_sepcon; auto. Qed.

Definition joinable {A : Type} {JA : Join A} {B : Type} (p : B -> pred A) (w : A) :=
  forall (x y : B), x <> y -> (p x * TT)%pred w -> (p y * TT)%pred w -> (p x * p y * TT)%pred w.

Lemma iter_sepcon_joinable {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}
      {C: Cross_alg A} {DA : Disj_alg A} {B : Type}:
  forall (p : B -> pred A) (l : list B) (w : A) (x : B),
    joinable p w -> (forall z, precise (p z)) -> (~ In x l) -> (p x * TT)%pred w ->
    (iter_sepcon l p * TT)%pred w -> (p x * iter_sepcon l p * TT)%pred w.
Proof.
  intros; induction l. simpl. rewrite sepcon_emp. auto. assert (x <> a). intro. apply H1. rewrite H4. apply in_eq.
  assert (~ In x l). intro; apply H1. apply in_cons. auto. specialize (IHl H5). simpl in H3. destruct H3 as [w1 [w2 [? [? ?]]]].
  destruct H6 as [w3 [w4 [? [? ?]]]]. assert ((p a * TT)%pred w). try_join w4 w2 w24. exists w3, w24. split; auto.
  assert ((iter_sepcon l p * TT)%pred w). try_join w3 w2 w23. exists w4, w23; split; auto. specialize (IHl H11).
  simpl. generalize H2; intro. destruct_sepcon H2 w. destruct_sepcon IHl w. destruct_sepcon H16 w. try_join w7 w9 w79.
  assertSub w0 w Sub1. assertSub w8 w Sub2. generalize (H0 x w w0 w8 H13 H18 Sub1 Sub2); intro. clear Sub1 Sub2. subst.
  clear H13. equate_canc w5 w79. specialize (H x a H4 H12 H10). specialize (precise_iter_sepcon p H0 l); intro.
  assertSub w4 w Sub1. assertSub w9 w Sub2. specialize (H13 w w4 w9 H9 H19 Sub1 Sub2). clear Sub1 Sub2. subst. clear H9.
  destruct_sepcon H w. destruct_sepcon H9 w. assertSub w10 w Sub1. assertSub w8 w Sub2.
  generalize (H0 x w w10 w8 H21 H18 Sub1 Sub2); intro; subst. clear Sub1 Sub2. assertSub w11 w Sub1. assertSub w3 w Sub2.
  generalize (H0 a w w11 w3 H22 H8 Sub1 Sub2); intro; subst. clear Sub1 Sub2 H21 H22. try_join w3 w4 w34. equate_canc w5 w34.
  destruct (join_together H21 H20 H6) as [w10 ?]. try_join w1 w8 w18. apply join_comm in H24. exists w18, w10.
  repeat split; auto. apply join_comm in H23. exists w8, w1. repeat split; auto. exists w3, w9. repeat split; auto.
Qed.

Lemma iter_sepcon_app_joinable {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A} {C: Cross_alg A}
      {DA : Disj_alg A} {B : Type}: forall (p : B -> pred A) (l1 l2 : list B) (w : A),
                                      joinable p w -> (forall z, precise (p z)) -> (forall x, In x l1 -> ~ In x l2) ->
                                      NoDup l1 -> (iter_sepcon l1 p * TT)%pred w -> (iter_sepcon l2 p * TT)%pred w ->
                                      (iter_sepcon (l1 ++ l2) p * TT)%pred w.
Proof.
  intros; induction l1; simpl; auto. simpl in H3. destruct_sepcon H3 h. rename h1 into h12; rename h2 into h3.
  destruct_sepcon H5 h. try_join h2 h3 h23. try_join h1 h3 h13. assert (forall x : B, In x l1 -> ~ In x l2).
  intros; apply H1. apply in_cons; auto. assert ((iter_sepcon l1 p * TT)%pred w). exists h2, h13. split; auto.
  assert (NoDup l1). apply NoDup_cons_1 in H2. auto. specialize (IHl1 H13 H15 H14). apply iter_sepcon_joinable; auto.
  intro. apply in_app_or in H16. destruct H16. apply NoDup_cons_2 in H2. auto. revert H16. apply H1. apply in_eq.
  exists h1, h23. split; auto.
Qed.

Lemma join_iter {A : Type} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} {CA : Canc_alg A}
      {C: Cross_alg A} {DA : Disj_alg A} {B : Type}:
  forall (w : A) (p : B -> pred A) (l : list B), NoDup l -> (forall y, In y l -> (p y * TT)%pred w) -> joinable p w ->
                                                 (forall z, precise (p z)) -> (iter_sepcon l p * TT)%pred w.
Proof.
  induction l; intros. simpl. rewrite sepcon_comm, sepcon_emp. auto. simpl. assert (In a (a :: l)) by apply in_eq.
  generalize (H0 a H3); clear H3; intro. destruct H3 as [w1 [r1 [? [? ?]]]]. rewrite <- app_nil_l in H.
  assert (NoDup l). apply NoDup_remove_1 in H. rewrite app_nil_l in H. auto. assert (forall y : B, In y l -> (p y * TT)%pred w).
  intros. apply H0. apply in_cons. auto. specialize (IHl H6 H7 H1). apply iter_sepcon_joinable; auto. apply NoDup_remove_2 in H.
  rewrite app_nil_l in H. auto. apply H0. apply in_eq.
Qed.

(* Program Definition mprecise {A} {JA: Join A}{AG: ageable A} (P: pred A) : pred A := *)
(*   fun w => forall w' w1 w2, necR w w' -> P w1 -> P w2 -> join_sub w1 w' -> join_sub w2 w' -> w1 = w2. *)
(* Next Obligation. *)
(* apply H0 with w'; trivial; apply rt_trans with a'; auto; apply rt_step; auto. *)
(* Qed. *)

(* Lemma mprecise_eq {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A}{XA: Age_alg A} {B} (P: B -> pred A): *)
(*     (forall x, precise (P x)) <-> (TT |-- ALL x : B, mprecise (P x)). *)
(* Proof. *)
(*   split; intros; repeat intro; *)
(*   [specialize (H b); hnf in H; apply H with w'; trivial | specialize (H w I x w w1 w2); apply H; trivial]. *)
(* Qed. *)

(* Lemma mprecise_orp {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} : *)
(*   forall w (P Q : pred A), (forall w1 w2: A, ~ (P w1 /\ Q w2)) -> (mprecise P) w -> *)
(*                 (mprecise Q) w -> (mprecise (P || Q)) w. *)
(* Proof. *)
(*   intros w P Q Hfalse H H0; intro; intros. *)
(*   destruct H2; destruct H3. generalize (H w' w1 w2 H1 H2 H3 H4 H5); tauto. *)
(*   specialize (Hfalse w1 w2); destruct Hfalse; intuition. *)
(*   specialize (Hfalse w2 w1); destruct Hfalse; intuition. *)
(*   generalize (H0 w' w1 w2 H1 H2 H3 H4 H5); tauto. *)
(* Qed. *)

(* Lemma mprecise_andp_right {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} : *)
(*   forall w P Q, (mprecise Q) w -> mprecise (P && Q) w. *)
(* Proof. intros; intro; intros; destruct H1; destruct H2; generalize (H w' w1 w2 H0 H5 H6 H3 H4); tauto. Qed. *)

(* Lemma mprecise_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{AG: ageable A}{XA: Age_alg A}: *)
(*   forall w, (mprecise emp) w. *)
(* Proof. *)
(*   assert ((TT |-- ALL  _ : nat , mprecise emp) <-> forall w, (mprecise emp) w). *)
(*   split; intros; [apply H; trivial; apply 0 | do 3 intro; apply H]. *)
(*   generalize (mprecise_eq (fun _ : nat => emp)); intro; simpl allp in H. *)
(*   rewrite <- H. rewrite <- H0. intro. apply precise_emp. *)
(* Qed. *)

(* Lemma mprecise_exp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{AG: ageable A}{XA: Age_alg A} {B}: *)
(*   forall w (P : B -> pred A), (forall x y : B, (x = y) \/ (x <> y)) -> (forall x y w1 w2, x <> y -> ~ (P x w1 /\ P y w2)) -> *)
(*                               (forall x, (mprecise (P x)) w) -> (mprecise (exp P)) w.  *)
(* Proof. *)
(*   intros w P X H H0. *)
(*   repeat intro. *)
(*   simpl in H0. *)
(*   destruct H2. *)
(*   apply (H0 x) with w'; trivial. *)
(*   destruct H3 as [y ?]. *)
(*   destruct (X x y) as [e | n]. *)
(*   rewrite e; trivial. *)
(*   specialize (H x y w1 w2). *)
(*   apply H in n; destruct n; split; auto. *)
(* Qed. *)

(* Lemma mprecise_sepcon {A} {JA : Join A} {PA : Perm_alg A} {SA: Sep_alg A} : *)
(*   forall w P Q, (mprecise P) w -> (mprecise Q) w -> (mprecise (P * Q)) w. *)
(* Proof. *)
(*   repeat intro; simpl in H, H0; destruct H2 as [h1 [h2 [? [? ?]]]]; destruct H3 as [i1 [i2 [? [? ?]]]]. *)
(*   assert (h1 = i1) by (apply H with w'; trivial; [assertSub h1 w' X | assertSub i1 w' X]; trivial). *)
(*   assert (h2 = i2) by (apply H0 with w'; trivial; [assertSub h2 w' X | assertSub i2 w' X]; trivial). *)
(*   rewrite H10 in *; rewrite H11 in *; equate_join w1 w2; trivial. *)
(* Qed. *)
