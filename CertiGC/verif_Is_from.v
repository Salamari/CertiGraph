Require Export compcert.common.Events.
Require Export RamifyCoq.CertiGC.gc_spec.

Definition valid_block (m : mem) (b : block) (o : ptrofs) (n : Z) : Prop :=
  0 < n /\
  Ptrofs.unsigned o + n <= Int.modulus /\
  forall i : Z, 0 <= i < n ->
                common.Memory.Mem.valid_pointer m b (Ptrofs.unsigned o + i) = true.

Definition Is_from_sem : extcall_sem :=
  fun _ args m1 trc ret m2 =>
    m1 = m2 /\ trc = nil /\ 
    match args with
    | (Vptr b1 o1) :: (Vptr b2 o2) :: (Vptr b3 o3) :: nil =>
      exists n : Z, 0 < n /\ Ptrofs.unsigned o1 + n < Int.modulus /\
                    (b1 = b2) /\ (Ptrofs.unsigned o1 + n = Ptrofs.unsigned o2) /\
                    valid_block m1 b1 o1 n /\
                    common.Memory.Mem.valid_pointer m1 b3 (Ptrofs.unsigned o3) = true /\
                    ((b1 = b3 /\ (Ptrofs.unsigned o1 <=
                                  Ptrofs.unsigned o3 <
                                  Ptrofs.unsigned o2)
                      /\ ret = Vone) \/
                     (((b1 <> b3) \/
                       (b1 = b3 /\
                        (Ptrofs.unsigned o3 < Ptrofs.unsigned o1 \/
                         Ptrofs.unsigned o3 >= Ptrofs.unsigned o2)))
                      /\ ret = Vzero))
    | _ => False
    end.

Definition Is_from_sig : signature :=
  mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil) (Some AST.Tint) cc_default.

Lemma intmod_eq_ptrofsmod: Int.modulus = Ptrofs.modulus.
Proof. now unfold Archi.ptr64; apply Ptrofs.modulus_eq32. Qed.

Lemma lt_ptr_mod: forall n1 n2, n1 <= n2 <= Ptrofs.max_unsigned -> n1 <= n2 < Ptrofs.modulus.
Proof.
  intros.
  replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by rep_omega.
  now rewrite <- Z.lt_le_pred in *.
Qed.

Lemma mem_ext_valid_block: forall m1 m2 b i n,
    Mem.extends m1 m2 -> valid_block m1 b i n -> valid_block m2 b i n.
Proof.
  intros. destruct H0 as [? [? ?]].
  do 2 (split; trivial).
  intros. specialize (H2 i0 H3).
  eapply Mem.valid_pointer_extends; eauto.
Qed.

Lemma Is_from_extcall: extcall_properties Is_from_sem Is_from_sig.
Proof.
  constructor.
  - intros. destruct H as [_ [_ ?]].
    do 4 (destruct vargs; try destruct v; try contradiction).
    destruct H as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    destruct H as [[_ [_ ?]] | [_ ?]]; subst; apply I.
  - intros; apply H0.
  - intros. destruct H as [? _]. subst m1. trivial. 
  - intros. destruct H as [? _]. subst m1. trivial. 
  - intros. destruct H as [? _]. subst m1; apply Mem.unchanged_on_refl.
  - intros. exists vres, m1'.
    destruct H as [? [? ?]]; subst m2 t.
    split.      
    2: split3; [apply Val.lessdef_refl | trivial | apply Mem.unchanged_on_refl].
    split3; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).    
    inversion H1; inversion H4; inversion H6; inversion H11;
      inversion H13; inversion H18; inversion H20; subst.
    clear H4 H11 H18 H20 H13 H6 H1.
    destruct H3 as [n [? [? [? [? ?]]]]].
    exists n. do 4 (split; trivial).
    clear -H0 H4. destruct H4 as [? [? ?]].
    split3; [apply (mem_ext_valid_block _ _ _ _ _ H0 H) | eapply Mem.valid_pointer_extends; eauto | tauto].
  - intros. exists f, vres, m1'. destruct H0 as [? [? ?]]. 
    split.
    2: {
      split.
      - clear -H4.
        do 4 (destruct vargs; try destruct v; try contradiction).
        destruct H4 as [_ [_ [_ [_ [_ [_ [_ H]]]]]]].
        destruct vres; auto. now destruct H. 
      - repeat (split; [now subst|]).
        apply mem_lemmas.inject_separated_same_meminj.
    }
    split3; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).
    inversion H2; inversion H7; inversion H9;
      inversion H17; inversion H19; inversion H27; inversion H29; subst.
    clear H2 H7 H9 H17 H19 H27 H29.
    destruct H4 as [n [? [? [? [? [? [? ?]]]]]]].
    exists n. rewrite H3 in  H12; rewrite H22 in H12; inversion H12.
    subst; clear H12.
    assert (Hf: 0 <= Ptrofs.unsigned i + n < Ptrofs.modulus) by
        (rewrite H4; apply Ptrofs.unsigned_range).
    assert (Ha: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta)) + n < Int.modulus). {
      rewrite intmod_eq_ptrofsmod.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep b0 b3 delta
                      (Ptrofs.add i (Ptrofs.repr n)) H22) as [Hx Hy]. 
      { right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]].
        assert (Hm: 0 <= n - 1 < n) by omega; rewrite <- (H5 _ Hm).
        f_equal; unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
      }
      clear -Hx Hy Hf H0.
      apply lt_ptr_mod in Hy.
      unfold Ptrofs.add in *. 
      repeat rewrite Ptrofs.unsigned_repr_eq in *.
      rewrite Z.add_mod_idemp_r, Z.mod_small in * by easy.
      rewrite Z.mod_small; [omega|]. 
      destruct i. unfold Ptrofs.unsigned in *; simpl in *. omega.
    }
    split3; [| |split3; [| |split3]]; trivial.
    + destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta
                   (Ptrofs.add i (Ptrofs.repr n)) H22) as [Hd' Hd]. {
        right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        destruct H5 as [_ [_ H5]]. assert (0 <= n - 1 < n) by omega.
        rewrite <- (H5 _ H1). f_equal.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
      }
      unfold Ptrofs.add. rewrite <- H4.
      destruct (Ptrofs.unsigned_range i) as [? _].
      repeat rewrite Ptrofs.unsigned_repr_eq.
      repeat rewrite Z.add_mod_idemp_r by easy.
      rewrite intmod_eq_ptrofsmod in Ha.
      unfold Ptrofs.add in Hd.
      repeat rewrite Ptrofs.unsigned_repr_eq in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small in Hd by easy.
      apply lt_ptr_mod in Hd.
      repeat rewrite Z.mod_small; [omega | trivial | omega].
    + split3; [easy | omega|]. intros.
      destruct H5 as [_ [_ H5]].
      rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H22 H1 (H5 i2 H3)).
      f_equal. unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta i H22) as [_ Hd]. {
        left. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
        assert (0 <= 0 < n) by omega; rewrite <- (H5 0 H1); f_equal; omega.
      } 
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
    + rewrite <- (Mem.valid_pointer_inject _ _ _ _ _ _ _ H32 H1 H6).
      f_equal. unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr_eq.
      destruct H1 as [_ _ _ _ rep _].
      destruct (rep _ _ delta1 i1 H32) as [_ Hd]. {
        left; now apply Mem.perm_cur_max,
              Mem.valid_pointer_nonempty_perm.
      }
      apply lt_ptr_mod in Hd.
      rewrite Z.add_mod_idemp_r, Z.mod_small by easy. omega.
    + destruct H7.
      * destruct H3 as [? [? ?]]; subst b1 vres.
        destruct H1 as [_ _ _ _ rep _].
        destruct (rep b0 b3 delta i H22) as [_ Hp]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          destruct H5 as [_ [_ H5]]; assert (0 <= 0 < n) by omega.
          specialize (H5 0 H1).
          now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H5 by omega.
        }
        destruct (rep b0 b3 delta i1 H22) as [_ Hq]. {
          left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm;
            destruct H5 as [_ [_ ?]]; assert (0 <= 0 < n) by omega.
          specialize (H1 0 H3); now rewrite H6.
        }
        destruct (rep b0 b3 delta i0 H22) as [_ Hr]. {
          destruct H5 as [_ [_ H5]]. rewrite <- H4.
          assert (Hm: 0 <= n - 1 < n) by omega.
          right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
          rewrite <- (H5 _ Hm); f_equal; omega.
        }
        rewrite H22 in H32; inversion H32.
        left. split3; trivial.
        subst delta1. clear -H7 Hp Hq Hr.
        unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
        apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr.  
        repeat rewrite Z.add_mod_idemp_r, Z.mod_small by easy.
        omega.
      * destruct H3. right. split; trivial.
        rename m2 into m; rename m1' into m'.
        destruct H1 as [_ _ _ lap rep _].
        destruct H3.
        -- destruct (EqDec_block b3 b7); [|now left].
           subst b3. right. split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           destruct H5 as [_ [_ H5]].
           assert (0 <= 0 < n) by omega.
           pose proof (H5 _ H3).
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H6.
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H8.
           replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H8 by omega.
           destruct (rep _ _ delta1 i1 H32) as [_ Hp]; [left; easy|].
           destruct (rep _ _ delta i H22) as [_ Hq]; [left; easy|].
           destruct (rep _ _ delta i0 H22) as [_ Hr]. {
             rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             specialize (H5 _ Hm).
             replace (Ptrofs.unsigned i + (n - 1)) with (Ptrofs.unsigned i + n - 1) in H5 by omega.
             apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H5. now right.
           }
           replace Ptrofs.max_unsigned with (Z.pred Ptrofs.modulus) in * by rep_omega.
           rewrite <- Z.lt_le_pred in *.
           repeat rewrite Z.mod_small by easy.
           destruct (lap _ _ _ _ _ _ _ _ H1 H22 H32 H8 H6); [contradiction|].
           clear rep Hp Hq Hr.
           replace (Ptrofs.unsigned i) with ((Ptrofs.unsigned i - delta) + delta) in H5 by omega.
           assert ((Ptrofs.unsigned i1 + delta1 < Ptrofs.unsigned i + delta) \/
                   (Ptrofs.unsigned i1 + delta1 >= Ptrofs.unsigned i0 + delta) \/
                   ((Ptrofs.unsigned i1 + delta1 >= Ptrofs.unsigned i + delta) /\
                    Ptrofs.unsigned i1 + delta1 < Ptrofs.unsigned i0 + delta)) by omega.
           destruct H10; [auto | destruct H10; [auto|]]. exfalso.
           destruct H10. rewrite <- H4 in H11.
           assert (0 <= Ptrofs.unsigned i1 + delta1 - Ptrofs.unsigned i - delta < n) by omega.
           specialize (H5 (Ptrofs.unsigned i1 + delta1 - Ptrofs.unsigned i - delta) H12).
           apply Mem.valid_pointer_nonempty_perm, Mem.perm_cur_max in H5.
           destruct (lap b0 b7 delta b1 b7 delta1 _ (Ptrofs.unsigned i1) H1 H22 H32 H5 H6); [auto | apply H13; omega].
        -- destruct H1. subst b0 vres.
           right. rewrite H22 in H32; inversion H32. clear H32.
           split; trivial.
           unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq.
           repeat rewrite Z.add_mod_idemp_r by easy.
           subst delta1.           
           destruct (rep b1 b3 delta i H22) as [_ Hp]. {
             left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             destruct H5 as [_ [_ H5]]; assert (H1: 0 <= 0 < n) by omega.
             specialize (H5 0 H1).
             now replace (Ptrofs.unsigned i + 0) with (Ptrofs.unsigned i) in H5 by omega.
           }
           destruct (rep b1 b3 delta i1 H22) as [_ Hq].
           1:  now left; apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
           destruct (rep b1 b3 delta i0 H22) as [_ Hr]. {
             destruct H5 as [_ [_ H5]].
             rewrite <- H4.
             assert (Hm: 0 <= n - 1 < n) by omega.
             right. apply Mem.perm_cur_max, Mem.valid_pointer_nonempty_perm.
             rewrite <- (H5 _ Hm); f_equal; omega.
           }
           clear - H3 Hp Hq Hr.
           apply lt_ptr_mod in Hp; apply lt_ptr_mod in Hq; apply lt_ptr_mod in Hr. 
           repeat rewrite Z.mod_small by easy.
           destruct H3; [left | right]; omega.
  - intros. destruct H as [_ [? _]]. subst t. simpl. omega.
  - intros. generalize H. destruct H as [_ [? _]]. subst t1. inversion H0. subst t2. clear H0. intro H.
    exists vres1, m1. apply H.
  - intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
    subst m1 m2 t1 t2.
    split; [constructor|].
    intros _. split; trivial.
    do 4 (destruct vargs; try destruct v; try contradiction).
    destruct H2 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    destruct H4 as [_ [_ [_ [_ [_ [_ [_ ?]]]]]]].
    intuition; congruence.
Qed.

Definition test_iop_sem : extcall_sem :=
  fun _ args m1 trc ret m2 =>
    m1 = m2 /\ trc = nil /\ 
    match args with
    | (Vint i) :: [] =>
      ret = Vint (Int.modu i (Int.repr 2))
    | (Vptr b ofs) :: [] =>
      ret = Vint (Ptrofs.to_int (Ptrofs.modu ofs (Ptrofs.repr 2)))
    | _ => False
    end.

Definition test_iop_sig : signature :=
  mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default.

Lemma test_iop__extcall: extcall_properties test_iop_sem test_iop_sig.
Proof.
  constructor.
  - intros. destruct H as [_ [_ ?]].
    do 2 (destruct vargs; try destruct v; try contradiction); subst; apply I.
  - intros. apply H0.
  - intros. destruct H as [? _]. subst m1. trivial. 
  - intros. destruct H as [? _]. subst m1. trivial.
  - intros. destruct H as [? _]. subst m1. apply Mem.unchanged_on_refl.
  - intros. exists vres, m1'.
    destruct H as [? [? ?]]. subst m2 t.
    split.
    2: split3; [apply Val.lessdef_refl | trivial | apply Mem.unchanged_on_refl]. 
    split3; trivial.
    do 2 (destruct vargs; try destruct v; try contradiction);    
      inversion H1; inversion H4; inversion H6; auto.
  - intros. (* is the choice of f forced?? *)
    exists f, vres, m1'. destruct H0 as [? [? ?]]; subst.
    split.
    2: {
      split.
      - do 2 (destruct vargs; try destruct v; try contradiction); subst; constructor.
      - split; [trivial|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply Mem.unchanged_on_refl|].
        split; [apply inject_incr_refl|].
        apply mem_lemmas.inject_separated_same_meminj.
    } clear f H H1 H2.
    split3; trivial.
    do 2  (destruct vargs; try destruct v; try contradiction).
    + inversion H2; inversion H5; inversion H7; trivial.
    + inversion H2; inversion H5; inversion H7; subst.
      (* dead *)
      admit.
  - intros. destruct H as [_ [? _]]. subst t. simpl; omega.
  - intros. generalize H. destruct H as [_ [? _]].
    subst t1; inversion H0; subst t2.
    intro H; exists vres1, m1; apply H.
  - intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
    subst m1 m2 t1 t2.
    split; [constructor|]. intros _. split; trivial.
    do 2 (destruct vargs; try destruct v; try contradiction); congruence.
Admitted.
