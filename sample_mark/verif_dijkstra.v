Require Import VST.msl.iter_sepcon.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.sample_mark.env_dijkstra_arr.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.graph_relation.
Require Import RamifyCoq.graph.reachable_computable.
Require Import RamifyCoq.floyd_ext.share.
Require Import RamifyCoq.msl_application.ArrayGraph.
Require Import RamifyCoq.msl_application.DijkstraArrayGraph.
Require Import RamifyCoq.sample_mark.spatial_dijkstra_array_graph.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Lemma inf_eq: 1879048192 = inf.   
Proof. compute; trivial. Qed.

Lemma inf_eq2: Int.sub (Int.repr 2147483647)
                       (Int.divs (Int.repr 2147483647)
                                 (Int.repr SIZE)) = Int.repr inf.
Proof. compute. trivial. Qed.

Definition inrange_prev prev_contents :=
  Forall (fun x => 0 <= x < SIZE \/ x = inf) prev_contents.

Definition inrange_priq priq_contents :=
  Forall (fun x => 0 <= x <= inf+1) priq_contents.

Definition inrange_dist dist_contents :=
  Forall (fun x => 0 <= x <= inf) dist_contents. 

(* hmm, this can move to the soundness condition *)
Definition inrange_graph grph_contents :=
  forall i j,
    0 <= i < Zlength grph_contents ->
    0 <= j < Zlength grph_contents ->
    0 <= Znth i (Znth j grph_contents) <= Int.max_signed / SIZE.

Lemma inrange_upd_Znth: forall (l: list Z) i new F,
    0 <= i < Zlength l ->
    Forall F l -> F new ->
    Forall F (upd_Znth i l new).
Proof.
  intros. rewrite Forall_forall in *. intros.
  destruct (eq_dec x new); [rewrite e; trivial|].
  unfold upd_Znth in H2; apply in_app_or in H2; destruct H2.
  - apply sublist_In in H2. apply (H0 x H2).
  - simpl in H2. destruct H2; [omega|].
    apply sublist_In in H2. apply (H0 x H2).
Qed.

Definition isEmpty_Prop (pq_contents : list Z) :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then False else acc) True pq_contents.

Definition isEmpty (pq_contents : list Z) : val :=
  fold_right (fun h acc => if (Z_lt_dec h inf) then Vzero else acc) Vone pq_contents.

Lemma isEmpty_prop_val: forall l,
    isEmpty_Prop l <-> isEmpty l = Vone.
Proof.
  intros. induction l; simpl in *. split; intro; trivial. 
  destruct (Z_lt_dec a inf); trivial. split; inversion 1.
Qed.

(* During refactoring, merge the two that follow *)
Lemma isEmpty_in': forall l,
    (exists i, In i l /\ i < inf) <-> isEmpty l = Vzero.
Proof.
  split; intros.
  - destruct H as [? [? ?]]. induction l. 
    1: exfalso; apply (in_nil H).
    unfold isEmpty. rewrite fold_right_cons.
    destruct (Z_lt_dec a inf); trivial.
    simpl in H; simpl; destruct H.
    1: rewrite H in n; exfalso. omega.
    clear n a. specialize (IHl H).
    unfold isEmpty in IHl. trivial.
  - induction l.
    1: inversion H.
    simpl in H.
    destruct (Z_lt_dec a inf).
    + exists a. split; simpl; [left|]; trivial.
    + destruct (IHl H) as [? [? ?]].
      exists x. split; [apply in_cons|]; assumption.
Qed.

Lemma isEmpty_in: forall l target,
    In target l -> target < inf -> isEmpty l = Vzero.
Proof.
  intros. induction l.
  1: exfalso; apply (in_nil H).
  unfold isEmpty. rewrite fold_right_cons.
  destruct (Z_lt_dec a inf); trivial.
  simpl in H; simpl; destruct H.
  1: rewrite H in n; exfalso; omega.
  clear n a. specialize (IHl H).
  unfold isEmpty in IHl. trivial.
Qed.

Lemma isEmptyTwoCases: forall l,
    isEmpty l = Vone \/ isEmpty l = Vzero.
Proof.
  intros. induction l. 1: simpl; left; trivial.
  destruct IHl; simpl; destruct (Z_lt_dec a inf);
  (try now left); now right.
Qed.

Lemma isEmptyMeansInf: forall l,
    isEmpty l = Vone -> Forall (fun x => x >= inf) l.
Proof.
  intros. induction l; trivial. simpl in H.
  destruct (Z_lt_dec a inf); [inversion H|].
  specialize (IHl H). apply Forall_cons; trivial.
Qed.

Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
  induction al; intros. 1: inversion H.
  destruct H.
  1: subst a; simpl; apply Z.le_min_l.
  simpl. rewrite Z.le_min_r. apply IHal, H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof. intros. apply fold_min_general, H. Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
 intros. induction H0.
 simpl. auto. simpl. unfold Z.min at 1.
 destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
 intros. revert x; induction al; simpl; intros.
 apply Z.min_comm. rewrite <- Z.min_assoc. f_equal. apply IHal.
Qed.

Lemma min_not_in_prev i l :
  Znth i l < fold_right Z.min (Znth 0 l) (sublist 0 i l) ->
  ~ In (Znth i l) (sublist 0 i l).
Proof.
  intros. intro.
  pose proof (fold_min_general (sublist 0 i l) (Znth i l) H0(Znth 0 l)). omega.
Qed.

Fixpoint find (l : list Z) (n : Z) (ans : Z) :=
  match l with
  | [] => ans
  | h :: t => if eq_dec h n
              then ans
              else (find t n (1 + ans))
  end.

Lemma find_index_gen: forall l i ans,
  0 <= i < Zlength l ->
  ~ In (Znth i l) (sublist 0 i l) ->
  find l (Znth i l) ans = i + ans.
Proof.
  intros. generalize dependent i.
  generalize dependent ans. induction l.
  1: intros; rewrite Zlength_nil in H; exfalso; omega.
  unfold find.
  intros.
  destruct (eq_dec a (Znth i (a :: l))).
  - rewrite <- e in H0. clear - H H0.
    destruct (Z.eq_dec 0 i). 1: omega. 
    destruct H. assert (0 < i) by omega.
    exfalso. apply H0.
    unfold sublist. replace (i-0) with i by omega.
    simpl. replace (Z.to_nat i) with (Z.to_nat (Z.succ (i-1))) by rep_omega.
    rewrite Z2Nat.inj_succ by omega.
    rewrite firstn_cons. apply in_eq.
  - destruct (Z.eq_dec 0 i).
    1: rewrite <- e in n; rewrite Znth_0_cons in n;
      exfalso; omega.
    assert (0 <= i - 1 < Zlength l) by 
        (rewrite Zlength_cons in H; rep_omega).
    assert (~ In (Znth (i - 1) l) (sublist 0 (i - 1) l)). { 
        rewrite <- (Znth_pos_cons i l a) by omega.
        rewrite <- (sublist_1_cons l a i).
        intro. apply H0.
        apply (sublist_In 1 i).
        rewrite sublist_sublist0 by omega. assumption.
      }
    pose proof (IHl (1 + ans) (i - 1) H1 H2).
    replace (i - 1 + (1 + ans)) with (i + ans) in H3 by omega.
    replace (Znth i (a :: l)) with (Znth (i - 1) l).
    2: { symmetry. apply Znth_pos_cons; omega. }
    rewrite <- H3.
    unfold find. trivial.
Qed.

Lemma find_index: forall l i,
    0 <= i < Zlength l ->
    ~ In (Znth i l) (sublist 0 i l) ->
    find l (Znth i l) 0 = i.
Proof.
  intros. replace i with (i + 0) at 2 by omega.
  apply find_index_gen; trivial.
Qed.

Lemma find_range_gen: forall l target ans,
    In target l ->
    0 <= ans ->
    ans <= find l target ans < Zlength l + ans.
Proof.
  intros. generalize dependent target.
  generalize dependent ans.
  induction l.
  1: intros; simpl; now rewrite Zlength_nil. 
  intros. apply in_inv in H. destruct H.
  - subst a. unfold find.
    destruct (eq_dec target target).
    rewrite Zlength_cons. split; rep_omega.
    exfalso; omega.
  - unfold find. destruct (eq_dec a target).
    1: rewrite Zlength_cons; split; rep_omega.
    assert (0 <= 1 + ans) by omega.
    pose proof (IHl (1+ans) H1 target H).
    clear -H2. unfold find in H2.
    rewrite Zlength_cons. rep_omega.
Qed.

Lemma find_range: forall l target,
    In target l ->
    0 <= find l target 0 < Zlength l.
Proof.
  intros. replace (Zlength l) with (Zlength l + 0) by omega.
  apply find_range_gen; trivial; omega.
Qed.

Lemma Znth_find_gen:
  forall l target ans,
    0 <= ans ->
    In target l ->
    Znth ((find l target ans)-ans) l = target.
Proof.
  intros. generalize dependent ans.
  induction l. 1: inversion H0.
  intros.
  destruct H0.
  - subst target. simpl.
    destruct (initial_world.EqDec_Z a a).
    + replace (ans-ans) with 0 by omega.
      rewrite Znth_0_cons; auto.
    + exfalso; omega.
  - specialize (IHl H0).
    simpl.
    destruct (initial_world.EqDec_Z a target).
    + replace (ans-ans) with 0 by omega.
      rewrite Znth_0_cons; auto.
    + assert (0 <= 1 + ans) by omega.
      specialize (IHl (1+ans) H1).
      rewrite Znth_pos_cons.
      replace (1+ans) with (ans+1) in IHl at 2 by omega.
      rewrite Z.sub_add_distr in IHl.
      assumption.
      destruct (find_range_gen l target (1+ans) H0 H1) as [? _].
      omega.
Qed.

Lemma Znth_find:
  forall l target,
    In target l ->
    Znth (find l target 0) l = target.
Proof.
  intros.
  replace (find l target 0) with (find l target 0 - 0) by omega.
  apply Znth_find_gen; [omega | assumption].
Qed.  

Lemma min_in_list : forall l1 l2 starter,
    incl l1 l2 ->
    In starter l2 ->
    In (fold_right Z.min starter l1) l2.
Proof.
  intros. induction l1; trivial. simpl.
  destruct (Z.min_dec a (fold_right Z.min starter l1));
    rewrite e; clear e.
  - apply H, in_eq.
  - apply IHl1, (incl_cons_inv H).
Qed.  

Lemma Znth_0_hd:
  forall list, Zlength list > 0 -> Znth 0 list = hd 0 list.
Proof.
  intros. induction list; inversion H.
  rewrite Znth_0_cons. trivial.
Qed.

Lemma min_picks_first:
  forall num mono start,
    start <= mono ->
    fold_right Z.min start (list_repeat num mono) = start.
Proof.
  intros. induction num; trivial.
  simpl. rewrite IHnum. rewrite Z.min_r; omega.
Qed.
  
Lemma find_src: forall src,
    0 <= src < Zlength (list_repeat (Z.to_nat SIZE) inf) ->
    find (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)
               (fold_right Z.min (hd 0 (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0))
                           (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0)) 0 = src.
Proof.
  intros.
  remember (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) as l.
  replace (fold_right Z.min (hd 0 l) l) with (Znth src l).
  - apply find_index.
    1: rewrite Heql, upd_Znth_Zlength; trivial.
    rewrite Heql.
    rewrite upd_Znth_same; trivial.
    rewrite sublist_upd_Znth_l by omega.
    rewrite sublist_list_repeat.
    2: omega.
    2: rewrite Zlength_list_repeat in H; [|unfold SIZE]; rep_omega.
    replace (src - 0) with (src) by omega.
    intro.
    apply in_list_repeat in H0.
    inversion H0.
  - subst l.
    rewrite upd_Znth_same; trivial.
    rewrite upd_Znth_unfold at 2.
    repeat rewrite fold_right_app.
    repeat rewrite sublist_list_repeat; try omega.
    2: rewrite Zlength_list_repeat in H; [|unfold SIZE]; omega.
    2: { split. omega. unfold SIZE in *; rewrite Zlength_list_repeat; omega. }
    repeat rewrite Zlength_list_repeat by omega.
    replace (src - 0) with (src) by omega.
    rewrite <- Znth_0_hd.
    2: { unfold SIZE in *; rewrite upd_Znth_Zlength by assumption.
         rewrite Zlength_list_repeat; omega. }
    destruct (Z.eq_dec src 0).
    + rewrite e. rewrite upd_Znth_same. simpl.
      compute; trivial. omega.
    + rewrite upd_Znth_diff by omega.
      rewrite Znth_list_repeat_inrange by (unfold SIZE in *; omega).
      rewrite Zlength_list_repeat.
      simpl. rewrite Z.min_l.
      1,2: rewrite min_picks_first.
      all: try rewrite <- inf_eq; try unfold SIZE; omega.
Qed.

Definition get_popped pq : list VType :=
  map snd (filter (fun x => (fst x) =? (inf+1))
                  (combine pq (nat_inc_list (Z.to_nat (Zlength pq))))).

Lemma get_popped_empty:
  forall l,
    Forall (fun x => x <> inf + 1) l -> get_popped l = [].
Proof.
  intros. 
  unfold get_popped.
  replace (filter (fun x : Z * Z => (fst x) =? (inf + 1))
                  (combine l (nat_inc_list (Z.to_nat (Zlength l))))) with (@nil (Z*Z)).
  trivial. symmetry. 
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2. clear Heql2.
  generalize dependent l2. induction l; trivial.
  intros. simpl. destruct l2; [reflexivity|].
  simpl. pose proof (Forall_inv H). pose proof (Forall_tl _ _ _ H).
  simpl in H0. destruct (a =? 1879048193) eqn:?.
  1: rewrite Z.eqb_eq in Heqb; omega.
  apply IHl; assumption.
Qed.

Lemma filter_app:
  forall l1 l2 (F: Z*Z -> bool),
    filter F (l1 ++ l2) = (filter F l1) ++ (filter F l2).
Proof.
  intros. induction l1.
  1: simpl; repeat rewrite app_nil_l; reflexivity.
  simpl. destruct (F a); [rewrite IHl1|]; easy.
Qed.

Lemma sublist_nil: forall lo hi A,
    sublist lo hi (@nil A) = (@nil A).
Proof.
  intros. unfold sublist, skipn.
  destruct (Z.to_nat lo); destruct (Z.to_nat (hi - lo)); reflexivity.
Qed.

(* Find a way to hint that the inhabitant of 
   Z*Z is (0,0). 
   Then merge the two below 
 *)
Lemma sublist_cons:
  forall a (l: list Z) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by omega.
  rewrite sublist_one by omega. simpl.
  rewrite Znth_0_cons.
  rewrite sublist_1_cons. reflexivity.
Qed.

Lemma sublist_cons':
  forall a (l: list (Z*Z)) i,
    0 < i < Zlength (a :: l) ->
    sublist 0 i (a :: l) = a :: sublist 0 (i-1) l.
Proof.
  intros.
  rewrite (sublist_split 0 1 i) by omega.
  rewrite sublist_one by omega. simpl.
  rewrite Znth_0_cons.
  rewrite sublist_1_cons. reflexivity.
Qed.

Lemma combine_same_length:
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    Zlength (combine l1 l2) = Zlength l1.
Proof.
  intros.
  repeat rewrite Zlength_correct in *.
  rewrite combine_length.
  rewrite min_l. reflexivity. rep_omega.
Qed.

Lemma sublist_skip: forall A lo (l: list A) a,
    0 < lo ->
    sublist lo (Zlength (a :: l)) (a::l) =
    sublist (lo - 1) (Zlength (a :: l) - 1) l.
Proof.
  intros.
  unfold sublist.
  destruct (Z.to_nat lo) eqn:?.
  - exfalso.
    unfold Z.to_nat in Heqn.
    destruct lo; try inversion H.
    pose proof (Pos2Nat.is_pos p); omega.
  - simpl. replace (Zlength (a :: l) - 1 - (lo - 1)) with 
               (Zlength (a :: l) - lo) by omega.
    f_equal. replace (Z.to_nat (lo - 1)) with n.
    reflexivity. apply juicy_mem_lemmas.nat_of_Z_lem1. omega.
Qed.

Lemma combine_sublist_0:
  forall (l1 l2 : list Z),
    Zlength l1 = Zlength l2 ->
    combine (sublist 0 (Zlength l1) l1) (sublist 0 (Zlength l2) l2) =
    sublist 0 (Zlength (combine l1 l2)) (combine l1 l2).
Proof. 
  intros. generalize dependent l2. induction l1. 
  - intros. simpl. rewrite sublist_nil. reflexivity.
  - intros.
    assert (1 <= Zlength l2). {
      rewrite Zlength_cons in H. rep_omega. }
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite (sublist_one 0 1) by omega.
    rewrite <- semax_lemmas.cons_app.
    rewrite sublist_same by omega.
    rewrite sublist_same by omega.
    rewrite (sublist_same 0 (Zlength (combine (a :: l1) (Znth 0 l2 :: sublist 1 (Zlength l2) l2))))  by omega.
    simpl. f_equal. 
Qed.

Lemma combine_sublist_gen:
  forall (l1 l2 : list Z) lo,
    0 <= lo < Zlength l1 + 1 ->
    Zlength l1 = Zlength l2 ->
    combine (sublist lo (Zlength l1) l1) (sublist lo (Zlength l2) l2) =
    sublist lo (Zlength (combine l1 l2)) (combine l1 l2).
Proof. 
  intros.
  generalize dependent l2.
  generalize dependent lo.
  induction l1. 
  1: intros; rewrite sublist_nil; simpl;
    rewrite sublist_nil; reflexivity.
  intros. destruct (Z.eq_dec 0 lo).
  1: subst lo; apply combine_sublist_0; omega.
  rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
  assert (1 <= Zlength l2). {
    rewrite Zlength_cons in H0.
    rewrite <- Z.add_1_l in H0. rewrite <- H0.
    pose proof (Zlength_nonneg l1). omega. }
  rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
  rewrite (sublist_one 0 1); try omega.
  rewrite <- semax_lemmas.cons_app.
  simpl.
  repeat rewrite sublist_skip by omega.
  replace (Zlength (a :: l1) - 1) with (Zlength l1)
    by (rewrite Zlength_cons; omega).
  replace (Zlength (Znth 0 l2 :: sublist 1 (Zlength l2) l2) - 1) with (Zlength (sublist 1 (Zlength l2) l2)) by
      (rewrite Zlength_cons, Zlength_sublist; rep_omega).
    replace (Zlength ((a, Znth 0 l2) :: combine l1 (sublist 1 (Zlength l2) l2)) - 1)
      with (Zlength (combine l1 (sublist 1 (Zlength l2) l2))) by
      (rewrite Zlength_cons; rep_omega).
    apply IHl1.
    rewrite Zlength_cons in H; omega.
    rewrite Zlength_cons in H0.
    rewrite Zlength_sublist; omega.
Qed.

Lemma combine_sublist_specific:
  forall (l1 l2: list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (sublist 0 i l1) (sublist 0 i l2) = sublist 0 i (combine l1 l2).
Proof.
  intros.
  generalize dependent i.
  generalize dependent l2. induction l1. 
  - intros. simpl. repeat rewrite sublist_nil. reflexivity.
  - intros.
    assert (1 <= Zlength l2). {
      rewrite Zlength_cons in H. rep_omega. }
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite (sublist_one 0 1) by omega.
    rewrite <- semax_lemmas.cons_app.
    destruct (Z.eq_dec i 0).
    + subst i; repeat rewrite sublist.sublist_nil; reflexivity.
    + repeat rewrite sublist_cons.
      simpl. rewrite sublist_cons'.
      f_equal. apply IHl1.
      all: try rewrite Zlength_cons in *.
      3: rewrite combine_same_length.
      1,4,5: rewrite Zlength_sublist.
      all: omega.
Qed.


Lemma combine_upd_Znth:
  forall (l1 l2: list Z) i new,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    combine (upd_Znth i l1 new) l2 =
    upd_Znth i (combine l1 l2) (new , Znth i l2).
Proof.
  intros.
  rewrite <- (sublist_same 0 (Zlength l2) l2) at 1 by reflexivity.
  repeat rewrite (sublist_split 0 i (Zlength l2) l2) by omega.
  unfold upd_Znth.
  rewrite combine_app.
  2: { repeat rewrite <- ZtoNat_Zlength.
       f_equal. repeat rewrite Zlength_sublist; omega. }
  f_equal. 
  1: apply combine_sublist_specific; assumption.
  rewrite (sublist_split i (i+1) (Zlength l2) l2) by omega.
  rewrite sublist_len_1 by omega.
  rewrite <- semax_lemmas.cons_app.
  simpl combine. f_equal.
  apply combine_sublist_gen.  omega. omega.
Qed.

Lemma Znth_combine:
  forall (l1 l2 : list Z) i,
    Zlength l1 = Zlength l2 ->
    0 <= i < Zlength l1 ->
    Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros. generalize dependent i.
  generalize dependent l2.
  induction l1.
  - intros. rewrite Zlength_nil in H0; exfalso; omega.
  - intros.
    rewrite <- (sublist_same 0 (Zlength l2) l2) by omega.
    rewrite (sublist_split 0 1 (Zlength l2) l2) by omega.
    rewrite sublist_len_1 by omega.
    rewrite <- semax_lemmas.cons_app.
    simpl. destruct (Z.eq_dec i 0).
    1: subst i; repeat rewrite Znth_0_cons; reflexivity.
    repeat rewrite Znth_pos_cons by omega.
    apply IHl1.
    rewrite Zlength_sublist by omega.
    rewrite Zlength_cons in H; rep_omega.
    rewrite Zlength_cons in H0; rep_omega.
Qed.

Lemma get_popped_unchanged:
  forall l new i,
    0 <= i < Zlength l ->
    new <> inf + 1 ->
    Znth i l <> inf + 1 ->
    get_popped (upd_Znth i l new) = get_popped l.
Proof.
  intros. unfold get_popped. 
  remember (fun x : Z * Z => fst x =? inf + 1) as F.
  rewrite upd_Znth_Zlength by omega.
  remember (nat_inc_list (Z.to_nat (Zlength l))) as l2.
  assert (Zlength l = Zlength l2). {
    rewrite Heql2.
    rewrite nat_inc_list_Zlength. rep_omega.
  } 
  f_equal.
  pose proof (combine_same_length l l2 H2).
  rewrite combine_upd_Znth by assumption.  
  unfold upd_Znth.
  rewrite <- (sublist_same 0 (Zlength (combine l l2)) (combine l l2)) at 4 by reflexivity.
  rewrite (sublist_split 0 i (Zlength (combine l l2))
                         (combine l l2)) by omega.
  do 2 rewrite filter_app.
  f_equal. rewrite H3.
  rewrite (sublist_split i (i+1) (Zlength l)) by omega.
  rewrite (sublist_one i (i+1) (combine l l2)) by omega.
  rewrite semax_lemmas.cons_app.
  do 2 rewrite filter_app.
  f_equal. simpl.
  destruct (F (new, Znth i l2)) eqn:?; rewrite HeqF in Heqb; simpl in Heqb.
  - exfalso. apply H1. rewrite <- inf_eq.
    simpl. rewrite Z.eqb_eq in Heqb. rewrite <- inf_eq in *.
    omega.
  - destruct (F (Znth i (combine l l2))) eqn:?; trivial.
    rewrite HeqF, Znth_combine, Z.eqb_eq in Heqb0 by omega.
    simpl in Heqb0. exfalso. apply H1. rewrite <- inf_eq. omega.
Qed.



Lemma behead_list:
  forall (l: list Z),
    0 < Zlength l -> 
    l = Znth 0 l :: tl l.
Proof.
  intros.
  destruct l.
  - rewrite Zlength_nil in H. inversion H.
  - simpl. rewrite Znth_0_cons. reflexivity.
Qed.

Lemma nat_inc_list_hd:
  forall n,
    0 < n ->
    Znth 0 (nat_inc_list (Z.to_nat n)) = 0.
Proof.
  intros. induction (Z.to_nat n).
  - reflexivity.
  - simpl.
    destruct n0.
    + reflexivity.
    + rewrite app_Znth1. omega.
      rewrite nat_inc_list_Zlength.
      rewrite <- Nat2Z.inj_0.
      apply inj_lt. omega.
Qed.

Lemma tl_app:
  forall (l1 l2: list Z),
    0 < Zlength l1 ->
    tl (l1 ++ l2) = tl l1 ++ l2.
Proof.
  intros. destruct l1.
  - inversion H.
  - intros. simpl. reflexivity.
Qed.

Lemma in_tl_nat_inc_list:
  forall i n,
    In i (tl (nat_inc_list n)) ->
    1 <= i.
Proof.
  destruct n. inversion 1.
  induction n. inversion 1. 
  intros.
  simpl in H.
  rewrite Zpos_P_of_succ_nat in H.
  rewrite tl_app in H.
  2: { rewrite Zlength_app.
       replace (Zlength [Z.of_nat n]) with 1 by reflexivity.
       rep_omega.
  } 
  apply in_app_or in H; destruct H.
  - apply IHn. simpl. assumption.
  - simpl in H. destruct H; omega.
Qed.

Lemma nat_inc_list_app:
  forall n m p i,
    0 <= i < m ->
    0 <= n ->
    n + m <= p ->
    Znth i (nat_inc_list (Z.to_nat m)) =
    Znth i
         (sublist n (n + m)
                  (nat_inc_list (Z.to_nat p))) - n.
Proof.
  symmetry.
  rewrite Znth_sublist by rep_omega.
  repeat rewrite nat_inc_list_i by rep_omega.
  omega.
Qed.

Lemma nat_inc_list_sublist:
  forall n m,
    0 <= n ->
    n <= m ->
    sublist 0 n (nat_inc_list (Z.to_nat m)) =
    nat_inc_list (Z.to_nat n).
Proof.
  intros.
  apply Zle_lt_or_eq in H0. destruct H0.
  2: { subst. rewrite sublist_same.
       reflexivity. reflexivity.
       rewrite nat_inc_list_Zlength. rep_omega. }
  apply Znth_eq_ext.
  1: { rewrite Zlength_sublist.
       rewrite nat_inc_list_Zlength. rep_omega.
       rep_omega.
       rewrite nat_inc_list_Zlength. rep_omega.
  }
  intros.
  rewrite nat_inc_list_i.
  2: { rewrite Zlength_sublist in H1.
       rep_omega.
       rep_omega.
       rewrite nat_inc_list_Zlength. rep_omega.
  }
  rewrite <- Z.sub_0_r at 1.
  replace n with (0 + n) by omega.
  rewrite Zlength_sublist in H1. 
  rewrite <- nat_inc_list_app. 
  rewrite nat_inc_list_i.
  all: try rep_omega.
  rewrite nat_inc_list_Zlength. rep_omega.
Qed.

Lemma in_get_popped:
  forall i l1 l2,
    0 <= i < Zlength l1 + Zlength l2 ->
    Zlength l1 <= i  ->
    In i (get_popped (l1 ++ l2)) <-> In (i - Zlength l1) (get_popped l2).
Proof.
  intros.
  split; unfold get_popped; intros.
  - rewrite In_map_snd_iff in H1; destruct H1.
    rewrite filter_In in H1; destruct H1; simpl in H2.
    rewrite In_map_snd_iff.
    exists x.
    rewrite filter_In; split; trivial. clear H2.
    rewrite <- (sublist_same 0 (Zlength (l1 ++ l2)) (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))) in H1.
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))) in H1.
    5,3: rewrite (Zlength_correct (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2)))));
         rewrite nat_inc_list_length;
         rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.    
    all: try rep_omega.
    rewrite combine_app in H1.
    2: { rewrite Zlength_correct.
         repeat rewrite <- ZtoNat_Zlength.
         f_equal.
         pose proof (Zlength_nonneg l1). 
         rewrite Zlength_sublist.
         all: rewrite Z2Nat.id.
         all: try omega.
         rewrite Zlength_app.
         (* rewrite Zlength_correct at 1. *)
         (* rewrite Zlength_correct at 1. *)
         rewrite nat_inc_list_Zlength.
         rewrite Z2Nat.id by omega. omega.
    }
    apply in_app_or in H1.
    destruct H1.
    + exfalso.
      pose proof (in_combine_r _ _ _ _ H1).
      clear H1.
      rewrite nat_inc_list_sublist in H2.
      2: apply Zlength_nonneg.
      2: rewrite Zlength_app; omega.
      apply nat_inc_list_in_iff in H2.
      rewrite Z2Nat.id in H2 by (apply Zlength_nonneg).
      omega.
    + apply In_Znth_iff in H1. destruct H1 as [? [? ?]].
      rewrite In_Znth_iff. exists x0.
      split.
      * rewrite combine_same_length in *.
        assumption.
        rewrite Zlength_sublist.
        rewrite Zlength_app. omega.
        rewrite Zlength_app.
        rep_omega.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        apply Zlength_nonneg.
      * rewrite Znth_combine in *; trivial.
        2: {
          rewrite Zlength_sublist.
          rewrite Zlength_app. omega.
          rewrite Zlength_app. rep_omega.
          rewrite nat_inc_list_Zlength.
          rewrite Z2Nat.id. reflexivity.
          rep_omega. }
        2, 4: rewrite combine_same_length in H1; trivial.
        2, 3: rewrite Zlength_sublist, Zlength_app; [|rewrite Zlength_app|]; try rep_omega;
             repeat rewrite Zlength_correct;
             rewrite nat_inc_list_length;
             rewrite Nat2Z.id; omega.
        2: repeat rewrite nat_inc_list_Zlength; rep_omega.
        inversion H2.
        rewrite Zlength_app.
        rewrite <- nat_inc_list_app. 
        reflexivity.
        rewrite combine_same_length in H1. omega.
        rewrite Zlength_sublist. rewrite Zlength_app.
        omega.
        rewrite Zlength_app. rep_omega.
        rewrite nat_inc_list_Zlength.
        rewrite Z2Nat.id. reflexivity.
        rep_omega. rep_omega. reflexivity.
  - rewrite In_map_snd_iff in H1; destruct H1.
    rewrite filter_In in H1; destruct H1; simpl in H2.
    rewrite In_map_snd_iff.
    exists x. 
    rewrite filter_In; split; trivial. clear H2.
    rewrite <- (sublist_same 0 (Zlength (l1 ++ l2)) (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2))))).
    rewrite (sublist_split 0 (Zlength l1) (Zlength (l1 ++ l2))).
    5,3: rewrite (Zlength_correct (nat_inc_list (Z.to_nat (Zlength (l1 ++ l2)))));
         rewrite nat_inc_list_length;
         rewrite Z2Nat.id; trivial.
    3: rewrite Zlength_app.    
    all: try rep_omega.
    rewrite combine_app. 
    2: { repeat rewrite <- ZtoNat_Zlength. f_equal.
         rewrite Zlength_sublist. omega.
         pose proof (Zlength_nonneg l1); omega.
         rewrite Zlength_app.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id; omega.
    }
    rewrite in_app_iff. right.
    rewrite In_Znth_iff in H1; destruct H1 as [? [? ?]].
    rewrite In_Znth_iff.
    exists x0. split.
    1: { rewrite combine_same_length in *.
         assumption.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id. reflexivity.
         omega.
         rewrite Zlength_sublist.
         rewrite Zlength_app. omega.
         rewrite Zlength_app.
         pose proof (Zlength_nonneg l2).
         rep_omega.
         repeat rewrite Zlength_correct.
         rewrite nat_inc_list_length.
         rewrite Z2Nat.id. reflexivity.
         omega.
    }
    rewrite Znth_combine in *.
    2: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; omega.    
    3: rewrite Zlength_sublist, Zlength_app; [|rewrite Zlength_app|]; try rep_omega;
             repeat rewrite Zlength_correct;
             rewrite nat_inc_list_length;
             rewrite Nat2Z.id; omega.
    2, 3: rewrite combine_same_length in H1; [rep_omega|].
    2, 3: repeat rewrite Zlength_correct;
      rewrite nat_inc_list_length;
      rewrite Nat2Z.id; omega.    
    inversion H2.
    rewrite (nat_inc_list_app (Zlength l1) _ (Zlength (l1 ++ l2))) in H5.
    rewrite Z.sub_cancel_r in H5.
    rewrite Zlength_app at 1.
    rewrite H5. reflexivity.
    rewrite combine_same_length in H1. omega.
    repeat rewrite Zlength_correct.
    rewrite nat_inc_list_length.
    rewrite Z2Nat.id. reflexivity.
    omega. rep_omega.
    rewrite Zlength_app. rep_omega.
Qed.

Lemma get_popped_meaning:
  forall l i,
    0 <= i < Zlength l ->
    In i (get_popped l) <-> Znth i l = inf + 1. 
Proof.
  intros. generalize dependent i.
  induction l; intros.
  1: rewrite Zlength_nil in H; omega.
  destruct (Z.eq_dec i 0).
  - subst i.
    split; intros.
    + rewrite Znth_0_cons.
      unfold get_popped in H0.
      rewrite In_map_snd_iff in H0; destruct H0.
      rewrite filter_In in H0; destruct H0.
      simpl in H1.
      rewrite (behead_list (nat_inc_list (Z.to_nat (Zlength (a :: l))))) in H0.
      2: { rewrite Zlength_correct.
           rewrite nat_inc_list_length.
           rewrite Z2Nat.id; omega.
      }
      rewrite nat_inc_list_hd in H0 by omega.
      simpl in H0. destruct H0.
      * inversion H0. rewrite Z.eqb_eq in H1.
        rewrite <- inf_eq. rep_omega.
      * pose proof (in_combine_r _ _ _ _ H0).
        exfalso. 
        apply in_tl_nat_inc_list in H2.
        omega.
    + unfold get_popped.
      rewrite (behead_list (nat_inc_list (Z.to_nat (Zlength (a :: l))))).
      2: { rewrite Zlength_correct.
           rewrite nat_inc_list_length.
           rewrite Z2Nat.id; omega.
      }
      rewrite nat_inc_list_hd by omega.
      simpl.
      destruct (a =? 1879048193) eqn:?.
      simpl; left; trivial.
      rewrite Z.eqb_neq in Heqb.
      exfalso; apply Heqb.
      rewrite Znth_0_cons in H0.
      rewrite <- inf_eq in H0. omega.
  - rewrite Znth_pos_cons by omega.
    rewrite Zlength_cons in H.
    assert (0 <= (i-1) < Zlength l) by omega.
    rewrite semax_lemmas.cons_app.
    assert (Zlength [a] = 1) by reflexivity.
    rewrite in_get_popped by omega.
    apply IHl; omega.
Qed.

Lemma get_popped_irrel_upd:
  forall l i j new,
    0 <= i < Zlength l ->
    0 <= j < Zlength l ->
    i <> j ->
    In i (get_popped l) <->
    In i (get_popped (upd_Znth j l new)).
Proof.
  intros.
  repeat rewrite get_popped_meaning; [| rewrite upd_Znth_Zlength; omega | omega].
  rewrite upd_Znth_diff; trivial; reflexivity.
Qed. 

Lemma get_popped_range:
  forall n l,
    In n (get_popped l) ->
    0 <= n < Zlength l.
Proof.
  intros.
  unfold get_popped in H.
  rewrite In_map_snd_iff in H. destruct H.
  rewrite filter_In in H. destruct H as [? _].
  apply in_combine_r in H.
  apply nat_inc_list_in_iff in H.
  rewrite Z2Nat.id in H by (apply Zlength_nonneg).
  assumption.
Qed.

Definition path_correct (g: LGraph) prev dist src dst p : Prop  :=
  valid_path g p /\
  path_ends g p src dst /\
  path_cost g p <> inf /\
  Znth dst dist = path_cost g p /\
  Forall (fun x => Znth (snd x) prev = fst x) (snd p).

Definition path_globally_optimal (g: LGraph) src dst p : Prop :=
  forall p', valid_path g p' ->
             path_ends g p' src dst ->
             path_cost g p <= path_cost g p'.

Definition inv_popped g src prev priq dist dst :=
    In dst (get_popped priq) ->
    exists path,
      path_correct g prev dist src dst path /\
      Forall (fun x => In (fst x) (get_popped priq) /\
                       In (snd x) (get_popped priq))
             (snd path) /\
      path_globally_optimal g src dst path.

Definition inv_unpopped g src prev priq dist dst :=
  Znth dst priq < inf ->
  let mom := Znth dst prev in
  exists p2mom,
    path_correct g prev dist src mom p2mom /\
    Forall (fun x => In (fst x) (get_popped priq) /\
                     In (snd x) (get_popped priq))
           (snd p2mom) /\
    path_globally_optimal g src mom p2mom /\
    Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) <> inf /\ 
    Znth dst dist = path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) /\
    forall mom' p2mom',
      path_correct g prev dist src mom' p2mom' ->
      Forall (fun x => In (fst x) (get_popped priq) /\
                       In (snd x) (get_popped priq))
             (snd p2mom') ->
      path_globally_optimal g src mom' p2mom' ->
      path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) <= path_cost g p2mom' + Znth dst (Znth mom' (graph_to_mat g)).

Definition inv_unseen src prev priq dist dst :=
  Znth dst priq = inf ->
  dst <> src -> Znth dst dist = inf /\
                Znth dst prev = inf.

Definition dijkstra_correct g (src : VType) (prev priq dist: list VType) : Prop :=
  forall dst,
    0 <= dst < SIZE ->  
    inv_popped g src prev priq dist dst /\
    inv_unpopped g src prev priq dist dst /\
    inv_unseen src prev priq dist dst.

(* SPECS *)
Definition pq_emp_spec :=
  DECLARE _pq_emp
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP (inrange_priq priq_contents)
    LOCAL (temp _pq pq)
    SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
    POST [ tint ]
    PROP ()
    LOCAL (temp ret_temp (isEmpty priq_contents))
    SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq).

Definition popMin_spec :=
 DECLARE _popMin
  WITH pq: val, priq_contents: list Z
  PRE [_pq OF tptr tint]
    PROP  (inrange_priq priq_contents;
         isEmpty priq_contents = Vzero)
    LOCAL (temp _pq pq)
    SEP   (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)
  POST [ tint ]
    EX rt : Z,
    PROP (rt = find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0)
    LOCAL (temp ret_temp  (Vint (Int.repr rt)))
    SEP   (data_at Tsh (tarray tint SIZE) (upd_Znth
       (find priq_contents (fold_right Z.min (Znth 0 priq_contents) priq_contents) 0)
       (map Vint (map Int.repr priq_contents)) (Vint (Int.repr (inf+1)))) pq).

Definition dijkstra_spec :=
  DECLARE _dijkstra
  WITH sh: wshare, g: Graph, arr : pointer_val,
       dist : pointer_val, prev : pointer_val, src : Z
  PRE [_graph OF (tptr (tarray tint SIZE)), _src OF tint,
       _dist OF (tptr tint), _prev OF (tptr tint)]
    PROP (0 <= src < SIZE;
          Forall (fun list => Zlength list = SIZE) (graph_to_mat g);
          inrange_graph (graph_to_mat g);
          sound_dijk_graph g;
          forall i, 0 <= i < SIZE ->
                    Znth i (Znth i (graph_to_mat g)) = 0)
    LOCAL (temp _graph (pointer_val_val arr);
         temp _src (Vint (Int.repr src));
         temp _dist (pointer_val_val dist);
         temp _prev (pointer_val_val prev))
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val dist);
       data_at_ Tsh (tarray tint SIZE) (pointer_val_val prev))
  POST [tvoid]
    EX prev_contents : list Z,
    EX dist_contents : list Z,
    EX priq_contents : list Z,
    PROP (dijkstra_correct g src prev_contents priq_contents dist_contents)
        (* and add a statement that the items that are in PQ but are not inf+1 are known to be unreachable *) 
    LOCAL ()
    SEP (graph_rep sh (graph_to_mat g) (pointer_val_val arr); 
         data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
         data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist)).
    
Definition Gprog : funspecs := ltac:(with_library prog [pq_emp_spec; popMin_spec; dijkstra_spec]).

Lemma body_pq_emp: semax_body Vprog Gprog f_pq_emp pq_emp_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP (isEmpty_Prop (sublist 0 i priq_contents))
     LOCAL (temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_omega.
  - unfold SIZE; rep_omega.
  - entailer!.
  - simpl.
    assert_PROP (Zlength priq_contents = SIZE). {
      entailer!. repeat rewrite Zlength_map in H3; auto.
    }
    forward; forward_if; forward; entailer!.
    + rewrite (isEmpty_in priq_contents (Znth i priq_contents)).
      trivial. 
      apply Znth_In; omega.
      rewrite <- H1 in H0.
      pose proof (Forall_Znth _ _ i H0 H).
      rewrite Int.signed_repr in H3.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3; trivial.
      simpl in H7. rep_omega.
    + rewrite (sublist_split 0 i (i+1)); try omega.
      unfold isEmpty_Prop.
      rewrite fold_right_app.
      rewrite sublist_one; try omega. simpl.
      destruct (Z_lt_dec (Znth i priq_contents) inf).
      2: unfold isEmpty_Prop in H2; trivial.
      exfalso.
      replace 8 with SIZE in H3 by (unfold SIZE; trivial).
      rewrite inf_eq2 in H3.
      do 2 rewrite Int.signed_repr in H3. 
      rep_omega.
      1: compute; split; inversion 1. 
      1,2: rewrite <- H1 in H0; apply (Forall_Znth _ _ i H0) in H; simpl in H; rep_omega.  
  - forward. entailer!.
    rewrite sublist_same in H0; trivial.
    2: { symmetry; repeat rewrite Zlength_map in H2.
         unfold SIZE. simpl in H2. omega. }
    replace (Vint (Int.repr 1)) with Vone by now unfold Vone, Int.one.
    symmetry. apply isEmpty_prop_val; trivial. 
Qed.

Lemma body_popMin: semax_body Vprog Gprog f_popMin popMin_spec.
Proof.
  start_function.
  assert_PROP (Zlength priq_contents = SIZE). {
    entailer!. repeat rewrite Zlength_map in H2; auto.
  }
  assert (0 <= 0 < Zlength (map Int.repr priq_contents)) by
      (rewrite Zlength_map; rewrite H1; unfold SIZE; omega).
  assert (0 <= 0 < Zlength priq_contents) by 
      (rewrite H1; unfold SIZE; omega).
  forward. forward.
  forward_for_simple_bound
    SIZE
    (EX i : Z,
     PROP ()
     LOCAL (temp _minWeight (Vint (Int.repr (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents))));
            temp _minVertex (Vint (Int.repr (find priq_contents (fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents)) 0))); 
            temp _pq pq)
     SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) pq)).
  - unfold SIZE; rep_omega.
  - entailer!. simpl. rewrite find_index.
    trivial. omega. simpl. unfold not. omega.
  - forward.
    assert (0 <= i < Zlength priq_contents) by omega.
    assert (Int.min_signed <=
            fold_right Z.min (Znth 0 priq_contents) (sublist 0 i priq_contents) <= Int.max_signed).
    { apply Forall_fold_min. apply Forall_Znth. omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      pose proof (Forall_Znth _ _ x0 H6 H).
      simpl in H8. rep_omega.
      rewrite Forall_forall. intros. rewrite In_Znth_iff in H6.
      destruct H6 as [? [? ?]]. rewrite <- H7.
      apply (Forall_sublist _ 0 i _) in H.
      apply (Forall_Znth _ _ _ H6) in H.
      simpl in H. rep_omega.
    }
    assert (Int.min_signed <= Znth i priq_contents <= Int.max_signed). {
      apply (Forall_Znth _ _ _ H5) in H; simpl in H; rep_omega. }
    forward_if.
    + forward. forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by omega.
      rewrite (sublist_one i (i+1) priq_contents) by omega.
      rewrite fold_min_another.
      rewrite Z.min_r; [|omega]. 
      split; trivial. f_equal. 
      rewrite find_index; trivial.
      apply min_not_in_prev; trivial.
    + forward. entailer!.
      rewrite (sublist_split 0 i (i+1)) by omega.
      rewrite (sublist_one i (i+1) priq_contents) by omega.
      rewrite fold_min_another.
      rewrite Z.min_l; [|omega]. split; trivial.
  - forward. 
    + entailer!. rewrite <- H1.
      apply find_range. 
      rewrite sublist_same; [|omega..].
      apply min_in_list; [apply incl_refl | apply Znth_In; omega]. 
    + forward. 
      Exists (find priq_contents (fold_right Z.min (hd 0 priq_contents) (sublist 0 SIZE priq_contents)) 0).
      rewrite sublist_same by omega. entailer!.
      destruct priq_contents; simpl; auto.
Qed.

Definition cost_was_improved_if_possible g me dst dist : Prop :=
  let cost := Znth dst (Znth me (graph_to_mat g)) in
  (* cost from me to dst *)
  cost < inf -> (* is dst my neighbor? if yes... *)
  Znth dst dist <= Znth me dist + cost.
(* by the time we're done, the cost to the dst is either better 
or the same as the cost via me *)

Lemma valid_path_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    valid_path g (src, links2u) ->
    pfoot g (src, links2u) = u ->
    0 <= u < SIZE ->
    0 <= i < SIZE ->
    valid_path g (src, links2u +:: (u,i)).
Proof.
  intros.
  apply valid_path_app.
  split; [assumption|].
  destruct H as [? [? [? ?]]].
  simpl; split.
  + rewrite H5; simpl.
    assumption.  
  + unfold strong_evalid.
    unfold edge_valid in H4.
    unfold vertex_valid in H.
    rewrite H4, H5, H6, H, H; simpl.
    split; split; assumption.
Qed.

Lemma path_ends_app_cons:
  forall g src links2u u i,
    sound_dijk_graph g ->
    path_ends g (src, links2u) src u ->
    path_ends g (src, links2u +:: (u, i)) src i.
Proof.                    
  split.
  + destruct H0; apply H0.
  + rewrite pfoot_last.
    destruct H as [_ [_ [_ ?]]].
    rewrite H; reflexivity.
Qed.

Lemma path_cost_app_cons:
  forall g p2u u i,
    inrange_graph (graph_to_mat g) ->
    sound_dijk_graph g ->
    Zlength (graph_to_mat g) = SIZE ->
    0 <= u < SIZE ->
    0 <= i < SIZE ->
    path_cost g p2u <> inf ->
    path_cost g p2u + Znth i (Znth u (graph_to_mat g)) =
    path_cost g (fst p2u, snd p2u +:: (u, i)).
Proof.
  intros.
  rewrite path_cost_app_cons.
  - rewrite elabel_Znth_graph_to_mat; simpl.
    omega. assumption.
    destruct H0 as [? [? [_ _]]].
    unfold edge_valid in H5.
    unfold vertex_valid in H0.
    rewrite H5; split; simpl; [rewrite H0|]; assumption.
  - rewrite elabel_Znth_graph_to_mat; simpl.
    + intro. unfold inrange_graph in H.
      rewrite <- H1 in H2, H3.
      specialize (H _ _ H3 H2).
      rewrite H5 in H.
      compute in H; destruct H.
      apply H6; reflexivity.
    + assumption.
    + destruct H0 as [? [? [_ _]]].
      unfold edge_valid in H5.
      unfold vertex_valid in H0.
      rewrite H5; split; simpl; [rewrite H0|]; assumption.
  - assumption.
Qed.

(*
Lemma cant_improve_further:
  forall i u src g priq prev dist,
    sound_dijk_graph g ->
    dijkstra_correct g src prev priq dist ->
    Zlength (graph_to_mat g) = SIZE ->
    Zlength priq = SIZE ->
    In i (get_popped priq) ->
    In u (get_popped priq) ->
    inrange_graph (graph_to_mat g) ->
    Znth i dist <= Znth u dist + Znth i (Znth u (graph_to_mat g)).
Proof.
  intros.
  unfold dijkstra_correct in H0.
  destruct (H0 i) as [? _].
  destruct (H0 u) as [? _].
  unfold inv_popped in H6, H7.
  destruct (H6 H3) as [p2i [? ?]].
  destruct (H7 H4) as [p2u [? ?]].
  clear H0 H6 H7. 
  unfold path_globally_optimal in H9. 
  destruct H8 as [? [? [? [? ?]]]].
  destruct H10 as [? [? [? [? ?]]]].  
  specialize (H10 (fst p2u, snd p2u ++ [(u,i)])).
  apply get_popped_range in H3.
  apply get_popped_range in H4.
  unfold VType in *. rewrite H2 in H3, H4.
  rewrite <- path_cost_app_cons in H9 by assumption.
  rewrite H15, H8. apply H9. 
  - destruct p2u; simpl. 
    destruct H13.
    apply valid_path_app_cons; assumption.
  - destruct p2u; simpl.
    replace z with src in *.
    apply path_ends_app_cons; assumption.
    destruct H13; simpl in H13; omega.
Qed.
*)

Lemma path_end_in_popped:
  forall g src mom priq prev dist p2mom,
    sound_dijk_graph g ->
    In src (get_popped priq) ->
    path_correct g prev dist src mom p2mom ->
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq) /\
         In (snd x) (get_popped priq)) (snd p2mom) ->
    In mom (get_popped priq).
Proof.
  intros.
  rewrite Forall_forall in H2. assert (Hrem := H1).
  destruct H1 as [_ [? _]].  
  destruct H1.
  pose proof (pfoot_in _ _ _ H3).
  unfold In_path in H4.
  destruct H4.
  - destruct p2mom. simpl in H4.
    unfold phead in H1; simpl in H1.
    rewrite H1 in H4. rewrite H4.
    trivial. (* here *)
  - destruct H4 as [? [? ?]].
    specialize (H2 _ H4).
    destruct H2.
    destruct H as [? [? [? ?]]].
    destruct H5.
    + rewrite H8 in H5. 
      unfold VType in *.
      rewrite <- H5 in H2; trivial.
    + rewrite H9 in H5.
      unfold VType in *.
      rewrite <- H5 in H6; trivial.
Qed.

Lemma path_end_in_popped':
  forall g src mom priq prev dist p2mom,
    sound_dijk_graph g ->
    snd p2mom <> [] ->
    path_correct g prev dist src mom p2mom ->
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq) /\
         In (snd x) (get_popped priq)) (snd p2mom) ->
    In mom (get_popped priq).
Proof. Abort.
(*
  intros. rewrite Forall_forall in H1.
  destruct H0 as [? [? [? [? ?]]]].
  destruct H2.
  pose proof (pfoot_in _ _ _ H6).
  unfold In_path in H7.
  destruct H7.
  - destruct p2mom. simpl in H7. subst v.
    
    unfold phead in H1; simpl in H1.
    rewrite H1 in H4. rewrite H4.
    trivial. (* here *)
  - destruct H4 as [? [? ?]].
    specialize (H2 _ H4).
    destruct H2.
    destruct H as [? [? [? ?]]].
    destruct H5.
    + rewrite H8 in H5. 
      unfold VType in *.
      rewrite <- H5 in H2; trivial.
    + rewrite H9 in H5.
      unfold VType in *.
      rewrite <- H5 in H6; trivial.
Qed. *)

Lemma graph_to_mat_Zlength: forall g, Zlength (graph_to_mat g) = SIZE.
Proof.
  intros. unfold graph_to_mat.
  rewrite Zlength_map, nat_inc_list_Zlength, Z2Nat.id; auto. now vm_compute.
Qed.

Lemma inrange_graph_cost_pos: forall g e,
    sound_dijk_graph g -> inrange_graph (graph_to_mat g) ->
    evalid g e -> 0 <= elabel g e.
Proof.
  intros. rewrite elabel_Znth_graph_to_mat; auto. destruct H as [? [? _]].
  red in H, H2. rewrite H2, H in H1. destruct H1. red in H0.
  rewrite <- (graph_to_mat_Zlength g) in H1, H3. specialize (H0 _ _ H3 H1).
  now destruct H0.
Qed.

Lemma acc_pos: forall (g: LGraph) l z,
    (forall e : EType, In e l -> 0 <= elabel g e) -> 0 <= z ->
    0 <= fold_left careful_add (map (elabel g) l) z.
Proof.
  intro. induction l; intros; simpl; auto. apply IHl.
  - intros. apply H. now apply in_cons.
  - unfold careful_add. destruct ((z =? inf) || (elabel g a =? inf))%bool.
    + now vm_compute.
    + apply Z.add_nonneg_nonneg; auto. apply H, in_eq.
Qed.

Lemma path_cost_pos:
  forall g p,
    sound_dijk_graph g ->
    valid_path g p ->
    inrange_graph (graph_to_mat g) ->
    0 <= path_cost g p.
Proof.
  intros.
  destruct p as [src links]. unfold path_cost. simpl.
  assert (forall e, In e links -> evalid g e). {
    intros. eapply valid_path_evalid; eauto. }
  assert (forall e, In e links -> 0 <= elabel g e). {
    intros. apply inrange_graph_cost_pos; auto. }
  apply acc_pos; auto. easy.
Qed.

Lemma entirely_in_subgraph_upd:
  forall u priq_contents links2mom mom,
    Forall
      (fun x : Z * Z =>
         In (fst x) (get_popped priq_contents) /\
         In (snd x) (get_popped priq_contents)) links2mom ->
            0 <= u < Zlength priq_contents ->
Znth u priq_contents <> inf + 1           ->
In mom (get_popped priq_contents) ->
 Forall
    (fun x : Z * Z =>
     In (fst x) (get_popped (upd_Znth u priq_contents (inf + 1))) /\
     In (snd x) (get_popped (upd_Znth u priq_contents (inf + 1)))) (links2mom +:: (mom, u)).
Proof.
  intros.
  rewrite Forall_forall; intros.
  rewrite Forall_forall in H.
  simpl in H3. apply in_app_or in H3.
  destruct H3. 
  - specialize (H _ H3).
    destruct H. 
    pose proof (get_popped_range _ _ H). 
    pose proof (get_popped_range _ _ H4).
    split; rewrite <- get_popped_irrel_upd;
      trivial; intro; apply H1;
        rewrite H7 in *; apply get_popped_meaning; trivial.
  - simpl in H3. destruct H3; [|omega].
    rewrite surjective_pairing in H3.
    inversion H3.
    unfold VType in *.
    rewrite <- H5, <- H6. split.
    + apply get_popped_irrel_upd; trivial.
      apply get_popped_range; trivial.
      intro. apply H1. rewrite H4 in *.
      apply get_popped_meaning; trivial.
    + rewrite get_popped_meaning.
      rewrite upd_Znth_same; trivial.
      rewrite upd_Znth_Zlength; trivial.
Qed.

Lemma step_in_range: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= fst x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [? _]]].
  unfold vertex_valid in H.
  unfold src_edge in H2.
  assert (In_path g (fst x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| left]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. omega.
Qed.

Lemma step_in_range2: forall g x x0,
    sound_dijk_graph g ->
    valid_path g x ->
    In x0 (snd x) ->
    0 <= snd x0 < SIZE.
Proof.
  intros.
  destruct H as [? [_ [_ ?]]].
  unfold vertex_valid in H.
  unfold dst_edge in H2.
  assert (In_path g (snd x0) x). {
    unfold In_path. right.
    exists x0. rewrite H2.
    split; [| right]; trivial.
  }
  pose proof (valid_path_valid _ _ _ H0 H3).
  rewrite H in H4. omega.
Qed.

Lemma body_dijkstra: semax_body Vprog Gprog f_dijkstra dijkstra_spec.
Proof.
  start_function. 
  forward_for_simple_bound
    SIZE
    (EX i : Z, 
     PROP (inrange_graph (graph_to_mat g))
     LOCAL (temp _dist (pointer_val_val dist);
            temp _prev (pointer_val_val prev);
            temp _src (Vint (Int.repr src));
            lvar _pq (tarray tint SIZE) v_pq;
            temp _graph (pointer_val_val arr))
     SEP (data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) v_pq;
          data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) (pointer_val_val prev);
          data_at Tsh (tarray tint SIZE) ((list_repeat (Z.to_nat i) (Vint (Int.repr inf))) ++ (list_repeat (Z.to_nat (SIZE-i)) Vundef)) (pointer_val_val dist);
          graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
  - unfold SIZE. rep_omega.
  - unfold data_at, data_at_, field_at_; entailer!.
  - forward. forward. forward.
    entailer!.
    replace 8 with SIZE by (unfold SIZE; rep_omega).
    rewrite inf_eq2.
    replace (upd_Znth i
       (list_repeat (Z.to_nat i) (Vint (Int.repr inf)) ++
                    list_repeat (Z.to_nat (SIZE - i)) Vundef) (Vint (Int.repr inf))) with
        (list_repeat (Z.to_nat (i + 1)) (Vint (Int.repr inf)) ++ list_repeat (Z.to_nat (SIZE - (i + 1))) Vundef).
    1: entailer!.
    rewrite upd_Znth_app2 by (repeat rewrite Zlength_list_repeat by omega; omega).
    rewrite Zlength_list_repeat by omega.
    replace (i-i) with 0 by omega.
    rewrite <- list_repeat_app' by omega.
    rewrite app_assoc_reverse; f_equal.
    rewrite upd_Znth0.
    rewrite Zlength_list_repeat by omega.
    rewrite sublist_list_repeat by omega.
    replace (SIZE - (i + 1)) with (SIZE - i - 1) by omega.
    replace (list_repeat (Z.to_nat 1) (Vint (Int.repr inf))) with ([Vint (Int.repr inf)]) by reflexivity.
    rewrite <- semax_lemmas.cons_app. reflexivity.
  - (* done with the first forloop *)
    replace (SIZE - SIZE) with 0 by omega; rewrite list_repeat_0, <- (app_nil_end).
    forward. forward. forward. 
    forward_loop
      (EX prev_contents : list Z,
       EX priq_contents : list Z,
       EX dist_contents : list Z,
       PROP (
           dijkstra_correct g src prev_contents priq_contents dist_contents;
           (* Znth src dist_contents = 0; *)
           inrange_prev prev_contents;
           inrange_dist dist_contents;
           inrange_priq priq_contents)
       LOCAL (temp _dist (pointer_val_val dist);
              temp _prev (pointer_val_val prev);
              temp _src (Vint (Int.repr src));
              lvar _pq (tarray tint SIZE) v_pq;
              temp _graph (pointer_val_val arr))
       SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) v_pq;
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))) 
      break:
      (EX prev_contents: list Z,
       EX priq_contents: list Z,
       EX dist_contents: list Z,
       PROP (Forall (fun x => x >= inf) priq_contents;
             dijkstra_correct g src prev_contents priq_contents dist_contents)
       LOCAL (lvar _pq (tarray tint SIZE) v_pq)
       SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents)) (pointer_val_val prev);
            (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents)) v_pq);
            data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents)) (pointer_val_val dist);
            graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
    + Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) src).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
      Exists (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0).
      repeat rewrite <- upd_Znth_map; entailer!.
      assert (Zlength (list_repeat (Z.to_nat SIZE) inf) = SIZE). {
        rewrite Zlength_list_repeat; omega. }
      split.
      2: {
        assert (inrange_prev (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_prev. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new. right; trivial.
        }
        assert (inrange_dist (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_dist. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new.
          rewrite new. compute. split; inversion 1.
        }
        assert (inrange_priq (list_repeat (Z.to_nat SIZE) inf)). {
          unfold inrange_priq. rewrite Forall_forall.
          intros ? new. apply in_list_repeat in new.
          rewrite new. rewrite <- inf_eq. omega.
        }
        split3; try apply inrange_upd_Znth; trivial.     
        left; unfold SIZE; simpl.
        2,3: rewrite <- inf_eq. all: unfold SIZE in *; omega.
      }
      assert (get_popped (upd_Znth src (list_repeat (Z.to_nat SIZE) inf) 0) = []).
      { apply get_popped_empty. rewrite Forall_forall; intros.
        unfold upd_Znth in H15.
        apply in_app_or in H15.
        destruct H15; [| apply in_inv in H15; destruct H15].
        1,3: rewrite sublist_list_repeat in H15 by omega;
          apply in_list_repeat in H15; omega.
        rewrite <- H15. compute; omega.
      } 
      (* math stuff *)  
      unfold dijkstra_correct, inv_popped, inv_unpopped, inv_unseen.
      rewrite H15. split3; intros.
      * inversion H17. 
      * unfold VType in *.
        destruct (Z.eq_dec src dst).
        2: rewrite upd_Znth_diff in H17; try omega;
            rewrite Znth_list_repeat_inrange in H17; omega.
        subst dst.
        exists (src, []).
        split3; [| |split3; [| |split]].
        -- split3; [| | split3].
           ++ simpl. destruct H2 as [? [? [? ?]]].
              unfold vertex_valid in H2.
              rewrite H2. omega.
           ++ rewrite upd_Znth_same by omega.
              unfold path_ends; simpl; omega.
           ++ unfold path_cost; simpl.
              rewrite <- inf_eq. omega.
           ++ repeat rewrite upd_Znth_same by omega.
              unfold path_cost; simpl; omega.
           ++ simpl snd. apply Forall_nil.
        -- simpl snd; apply Forall_nil.
        -- intros. rewrite upd_Znth_same by omega.
           unfold path_globally_optimal. intros.
           unfold path_cost at 1; simpl.
           apply path_cost_pos; trivial.
        -- intros. repeat rewrite upd_Znth_same by omega.
           unfold path_cost at 1; simpl.
           rewrite H3 by omega. simpl.
           rewrite <- inf_eq. omega.
        -- intros. repeat rewrite upd_Znth_same by omega.
           unfold path_cost at 1; simpl.
           rewrite H3 by omega. 
           assert (0 <= src < Zlength (graph_to_mat g)). {
             rewrite graph_to_mat_Zlength. omega.
           }
           omega.
        -- intros. repeat rewrite upd_Znth_same by omega.
           unfold path_cost at 1; simpl.
           rewrite H3 by omega. 
           assert (0 <= src < Zlength (graph_to_mat g)). {
             rewrite graph_to_mat_Zlength. omega.
           }
           assert (0 <= mom' < Zlength (graph_to_mat g)). {
             rewrite graph_to_mat_Zlength.
             destruct H18 as [? [? [? [? ?]]]].
             assert (In_path g mom' p2mom'). {
               destruct H22.
               apply pfoot_in; trivial.
             }
             destruct H2. unfold vertex_valid in H2.
             rewrite <- H2.
             apply (valid_path_valid g p2mom'); trivial.
           }
           pose proof (H1 src mom' H21 H22).
           destruct H18.
           pose proof (path_cost_pos g p2mom' H2 H18 H1).
           unfold VType in *. omega.
      * split; trivial. rewrite upd_Znth_diff by omega.
        rewrite Znth_list_repeat_inrange; omega.
    + Intros prev_contents priq_contents dist_contents.
      assert_PROP (Zlength priq_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength prev_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      assert_PROP (Zlength dist_contents = SIZE).
      { entailer!. now repeat rewrite Zlength_map in *. }
      forward_call (v_pq, priq_contents). 
      forward_if.
      * assert (isEmpty priq_contents = Vzero). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H12 in H11; simpl in H11;
              now inversion H11.
        }
        clear H11. 
        forward_call (v_pq, priq_contents). Intros u.
        (* Shengyi's suggestion:
           At this point it's possible to prove
           that dist[u] is globally minimal *)
        assert (0 <= u < Zlength priq_contents).
        { rewrite H11. 
          apply find_range.  
          apply min_in_list. apply incl_refl.
          destruct priq_contents. rewrite Zlength_nil in H8.
          inversion H8. simpl. left; trivial. }
        rewrite Znth_0_hd, <- H11 by omega.
        do 2 rewrite upd_Znth_map.
        assert (~ (In u (get_popped priq_contents))). {
          intro.
          rewrite get_popped_meaning in H14 by omega.
          rewrite <- isEmpty_in' in H12.
          destruct H12 as [? [? ?]].
          rewrite H11 in H14.
          rewrite Znth_find in H14.
          2: {
            rewrite <- Znth_0_hd by (unfold SIZE in *; omega).
            apply min_in_list; [ apply incl_refl | apply Znth_In; unfold SIZE in *; omega].
          }
          pose proof (fold_min _ _ H12).
          omega.
        }
        remember (upd_Znth u priq_contents (inf+1)) as priq_contents_popped.
        forward_for_simple_bound
          SIZE
          (EX i : Z,
           EX prev_contents' : list Z,
           EX priq_contents' : list Z,
           EX dist_contents' : list Z,
          PROP (
              forall dst, inv_popped g src prev_contents' priq_contents' dist_contents' dst;
              (* popped items are not affected by the for loop *)
              forall dst,
                0 <= dst < i ->
                inv_unpopped g src prev_contents' priq_contents' dist_contents' dst;
              forall dst,
                (* a bit weaker than inv_unpopped *)
                i <= dst < SIZE ->
                Znth dst priq_contents' < inf -> (* seen *)
                let mom := Znth dst prev_contents' in
                exists p2mom,
                  path_correct g prev_contents' dist_contents' src mom p2mom /\
                  Forall (fun x => In (fst x) (get_popped priq_contents') /\
                                   In (snd x) (get_popped priq_contents') /\
                                   fst x <> u /\ snd x <> u)
                         (snd p2mom) /\
                  path_globally_optimal g src mom p2mom /\
                  Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) <> inf /\
                  Znth dst dist_contents' = Z.add (path_cost g p2mom) (Znth dst (Znth mom (graph_to_mat g))) /\ 
                  forall mom' p2mom',
                    path_correct g prev_contents' dist_contents' src mom' p2mom' ->
                    Forall (fun x => In (fst x) (get_popped priq_contents') /\
                                     In (snd x) (get_popped priq_contents') /\
                                     fst x <> u /\ snd x <> u)
                           (snd p2mom') ->
                    path_globally_optimal g src mom' p2mom' ->
                    path_cost g p2mom + Znth dst (Znth mom (graph_to_mat g)) <= path_cost g p2mom' + Znth dst (Znth mom' (graph_to_mat g));
               In u (get_popped priq_contents'); (* kill? *)
               inrange_prev prev_contents';
               inrange_priq priq_contents';
               inrange_dist dist_contents')
           LOCAL (temp _u (Vint (Int.repr u));
                  temp _dist (pointer_val_val dist);
                  temp _prev (pointer_val_val prev);
                  temp _src (Vint (Int.repr src));
                  lvar _pq (tarray tint SIZE) v_pq;
                  temp _graph (pointer_val_val arr))
           SEP (data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr prev_contents')) (pointer_val_val prev);
                data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr priq_contents')) v_pq;
                data_at Tsh (tarray tint SIZE) (map Vint (map Int.repr dist_contents')) (pointer_val_val dist);
                graph_rep sh (graph_to_mat g) (pointer_val_val arr))).
        -- unfold SIZE; rep_omega. 
        -- Exists prev_contents. 
           Exists priq_contents_popped.
           Exists dist_contents.
           repeat rewrite <- upd_Znth_map.
           entailer!.  
           remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
           split3; [| | split3].
           (* proving the for loop's invariants for i = 0 *)
           ++ unfold inv_popped. intros.
              pose proof (get_popped_range _ _ H11).
              rewrite upd_Znth_Zlength in H28 by omega.
              rewrite H8 in H28.
              destruct (H4 dst H28) as [? [? ?]].
              unfold inv_popped in H29.
              destruct (Z.eq_dec dst u).
              ** subst dst.
                 (* show that u is a legit entrant into the 
                    popped club *)
                 unfold inv_unpopped in H30.
                 assert (Znth u priq_contents < inf).
                 {
                   rewrite <- isEmpty_in' in H12.
                   destruct H12 as [? [? ?]].
                   rewrite Hequ.
                   rewrite Znth_find.
                   2: { apply min_in_list.
                        apply incl_refl.
                        rewrite <- Znth_0_hd by (unfold SIZE in *; omega).
                        apply Znth_In; omega.
                   }
                   pose proof (fold_min _ _ H12). omega.
                 }
                 specialize (H30 H32).
                 destruct H30 as [p2mom [? [? [? [? [? ?]]]]]].
                 unfold VType in *.
                 remember (Znth u prev_contents) as mom.
                 assert (0 <= mom < SIZE). {
                   destruct H30 as [? [? _]].              
                   assert (In_path g mom p2mom). {
                     destruct H38.
                     apply pfoot_in; trivial.
                   }
                   destruct H2. unfold vertex_valid in H2.
                   rewrite <- H2.
                   apply (valid_path_valid g p2mom); trivial.
           }
                 exists (fst p2mom, snd p2mom +:: (mom, u)).
                 split3; trivial.
                 --- destruct H30 as [? [? [? [? ?]]]].
                     split3; [| | split3].
                     +++ destruct H39.
                       apply valid_path_app_cons; trivial;
                         try rewrite <- surjective_pairing; trivial.
                     +++ rewrite (surjective_pairing p2mom) in *.
                         simpl.
                         replace (fst p2mom) with src in *.
                         apply path_ends_app_cons; trivial.
                         destruct H39. simpl in H39; omega.
                     +++ rewrite <- path_cost_app_cons; trivial.

                     +++ rewrite <- path_cost_app_cons; trivial.
                     +++ unfold VType in *.
                         rewrite Forall_forall. intros.
                         rewrite Forall_forall in H42, H33.
                         apply in_app_or in H43.
                         destruct H43.
                         *** specialize (H42 _ H43). trivial.
                         *** simpl in H43.
                             destruct H43; [| omega].
                             rewrite (surjective_pairing x) in *.
                             inversion H43.
                             simpl.
                             rewrite <- H45, <- H46.
                             omega.
                 --- rewrite Forall_forall; intros.
                     rewrite Forall_forall in H33.
                     simpl in H39. 
                     apply in_app_or in H39.
                     destruct H39; split.
                     +++ specialize (H33 _ H39).
                         destruct H33.
                         rewrite <- get_popped_irrel_upd; try omega; trivial.
                         *** apply get_popped_range in H33; omega.
                         *** intro.
                             unfold VType in *.
                             rewrite H41 in H33.
                             apply H14. trivial.
                     +++ destruct (Z.eq_dec (snd x) u).
                         *** rewrite get_popped_meaning.
                             rewrite e.
                             rewrite upd_Znth_same; trivial.
                             rewrite upd_Znth_Zlength by omega.
                             rewrite H8.
                             destruct H30.
                             apply (step_in_range2 g p2mom);
                               trivial.
                         *** specialize (H33 _ H39).
                             destruct H33.
                             rewrite <- get_popped_irrel_upd; try omega; trivial.
                             rewrite H8.
                             destruct H30.
                             apply (step_in_range2 g p2mom);
                               trivial.
                     +++ simpl in H39.
                         destruct H39; [|omega].
                         rewrite (surjective_pairing x) in *.
                         inversion H39.
                         simpl fst.
                         rewrite <- H41, <- H42.
 (* may need to add that mom is in popped...
    but that is not true for the very first step, 
    when src is set to 0. need to think of something.
*)
                         admit.
                     +++ simpl in H39.
                         destruct H39; [|omega].
                         rewrite (surjective_pairing x) in *.
                         inversion H39.
                         simpl snd.
                         rewrite get_popped_meaning.
                         rewrite upd_Znth_same; omega.
                         rewrite upd_Znth_Zlength; omega.
                 --- intros.
                     simpl.
                     (* unfold path_globally_optimal in H34. *)
                     (* unfold path_globally_optimal; intros. *)
                     (* rewrite <- path_cost_app_cons; trivial. *)
                     admit.
                     (* tricky admit #1 *)
              ** rewrite <- get_popped_irrel_upd in H11 by omega.
                 (* show that all is well for the old
                    popped vertices *)
                 specialize (H29 H11).
                 destruct H29 as [? [? [? ?]]].
                 exists x. split3; trivial.
                 rewrite Forall_forall; intros.
                 rewrite Forall_forall in H32.
                 specialize (H32 _ H34).
                 destruct H29.
                 pose proof (step_in_range _ _ _ H2 H29 H34).
                 pose proof (step_in_range2 _ _ _ H2 H29 H34). 
                 destruct H32; split;
                 unfold VType in *;
                 rewrite <- get_popped_irrel_upd; try omega; trivial.
                 --- intro contra. rewrite contra in H32.
                     apply H14. trivial.
                 --- intro contra. rewrite contra in H38.
                     apply H14. trivial.
           ++ intros. omega.
           ++ intros.
              destruct (Z.eq_dec dst u).
              1: subst dst; rewrite upd_Znth_same in H28; omega.
              rewrite upd_Znth_diff in H28 by omega.
              (* dst is some previously "seen" 
                 vertex that is not u.
                 ie, it technically has not been 
                 affected at all *)
              (* proceed by using the old path 
                 from inv_unpopped *)
              destruct (H4 dst H11) as [_ [? _]].
              unfold inv_unpopped in H29.
              specialize (H29 H28).
              destruct H29 as [? [? [? ?]]].
              exists x. split3; trivial.
              ** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H30.
                 specialize (H30 _ H32).
                 destruct H30. 
                 assert (fst x0 <> u). {
                   intro. 
                   unfold VType in *. rewrite H34 in H30.
                   apply H14; trivial.
                 }
                 assert (snd x0 <> u). {
                   intro.
                   rewrite H35 in H33.
                   apply H14; trivial.
                 }
                 split3; [| |split]; trivial.
                 --- rewrite <- get_popped_irrel_upd; try omega; trivial.
                     rewrite H8. destruct H29.
                     apply (step_in_range g x); trivial.
                 --- rewrite <- get_popped_irrel_upd; try omega; trivial.
                     destruct H29.
                     rewrite H8.
                     apply (step_in_range2 g x); trivial.
              ** intros.
                 destruct H31 as [? [? [? ?]]].
                 split3; [| |split]; trivial.
                 intros.
                 apply H34; trivial.
                 rewrite Forall_forall; intros.
                 rewrite Forall_forall in H36.
                 specialize (H36 _ H38).
                 destruct H36 as [? [? [? ?]]].
                 destruct H35.
                 rewrite <- get_popped_irrel_upd in H36, H39; try omega.
                 split; trivial.
                 all: rewrite H8.
                 
                 1: apply (step_in_range2 g p2mom'); trivial.
                 1: apply (step_in_range g p2mom'); trivial.
           ++ apply get_popped_meaning.
              rewrite upd_Znth_Zlength; omega.
              rewrite upd_Znth_same; omega.
           ++ apply inrange_upd_Znth; trivial;
                rewrite <- inf_eq; rep_omega.
        -- assert (0 <= u < Zlength (graph_to_mat g)). {
             unfold graph_to_mat.
             repeat rewrite Zlength_map.
             rewrite nat_inc_list_Zlength.
             rep_omega.
           }
           assert (Zlength (Znth u (graph_to_mat g)) = SIZE). {
             rewrite Forall_forall in H0. apply H0. apply Znth_In. omega.
           }
           freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
           rewrite (graph_unfold _ _ _ u) by omega.
           Intros.
           freeze FR2 :=
             (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                          (sublist 0 u (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g))))))
                                                                                            (iter_sepcon (list_rep sh SIZE (pointer_val_val arr) (graph_to_mat g))
                                                                                                         (sublist (u + 1) (Zlength (graph_to_mat g))
                                                                                                                  (nat_inc_list (Z.to_nat (Zlength (graph_to_mat g)))))). 
           unfold list_rep.
           assert_PROP (force_val
                          (sem_add_ptr_int tint Signed
                                           (force_val (sem_add_ptr_int (tarray tint SIZE) Signed (pointer_val_val arr) (Vint (Int.repr u))))
                                           (Vint (Int.repr i))) = field_address (tarray tint SIZE) [ArraySubsc i] (list_address (pointer_val_val arr) u SIZE)). {
             entailer!.
             unfold list_address. simpl.
             rewrite field_address_offset.
             1: rewrite offset_offset_val; simpl; f_equal; rep_omega.
             destruct H28 as [? [? [? [? ?]]]].
      unfold field_compatible; split3; [| | split3]; auto.
      unfold legal_nested_field; split; [auto | simpl; omega].
           }
           forward. thaw FR2. 
           gather_SEP 0 3 1.
           rewrite <- graph_unfold; trivial. thaw FR.
           remember (Znth i (Znth u (graph_to_mat g))) as cost.
           assert_PROP (Zlength priq_contents' = SIZE). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength prev_contents' = SIZE). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }
            assert_PROP (Zlength dist_contents' = SIZE). {
             entailer!. repeat rewrite Zlength_map in *. trivial. }    
           assert_PROP (Zlength (graph_to_mat g) = SIZE) by entailer!.
           assert (0 <= cost <= Int.max_signed / SIZE) by
               (rewrite Heqcost; apply H1; omega). 
           forward_if. 
           ++ assert (0 <= Znth u dist_contents' <= inf). {
                assert (0 <= u < Zlength dist_contents') by omega.
                apply (Forall_Znth _ _ _ H32) in H24.
                assumption. 
              } 
              assert (0 <= Znth i dist_contents' <= inf). {
                assert (0 <= i < Zlength dist_contents') by omega.
                apply (Forall_Znth _ _ _ H33) in H24.
                assumption. 
              }               
              assert (0 <= Znth u dist_contents' + cost <= Int.max_signed). {
                split; [omega|].
                unfold inf in *. rep_omega.
                }
              forward. forward. forward_if.
  ** rewrite Int.signed_repr in H35
      by (unfold inf in *; rep_omega).
     assert (~ In i (get_popped priq_contents')). {
       (* This is true because the cost to i was 
          just improved. This is impossible for 
          popped items. 
        *)
       intro.
       unfold inv_popped in H18.
       destruct (H18 _ H36) as [p2i [? [? ?]]].
       destruct (H18 _ H21) as [p2u [? [? ?]]].
       unfold path_globally_optimal in H39.
       specialize (H39 (fst p2u, snd p2u +:: (u,i))).
       rewrite Heqcost in H35.
       rewrite <- path_cost_app_cons in H39.
       destruct H40 as [? [? [? [? ?]]]].
       destruct H37 as [? [? [? [? ?]]]].
       rewrite H49, H45 in H35.
       apply Zlt_not_le in H35.
       unfold VType in *.
       apply H35. apply H39.
       - apply valid_path_app_cons; trivial;
         rewrite <- surjective_pairing; 
         destruct H43; trivial.
       - rewrite (surjective_pairing p2u) in *.
           simpl.
           replace (fst p2u) with src in *.
           apply path_ends_app_cons; trivial.
           destruct H43. simpl in H43; omega.
       - apply H1.
       - apply H2.
       - apply graph_to_mat_Zlength.
       - omega.
       - omega.
       - destruct H40 as [_ [_ [? _]]]. omega.
     }
     assert (0 <= i < Zlength (map Vint (map Int.repr dist_contents'))) by
         (repeat rewrite Zlength_map; omega).
     forward. forward. forward.
     forward; rewrite upd_Znth_same; trivial.
     1: entailer!. 
     forward.
     Exists (upd_Znth i prev_contents' u).
     Exists (upd_Znth i priq_contents' (Znth u dist_contents' + cost)).
     Exists (upd_Znth i dist_contents' (Znth u dist_contents' + cost)). 
     repeat rewrite <- upd_Znth_map; entailer!.
     remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
     assert (u <> i) by (intro; subst; omega).
     split3; [| | split3].
     (* prove that the for loop's invariant 
        holds if I take another step *)
     --- (* hmm, updating values for i should not have
            changed anything for popped vertices... *)
       intros. pose proof (H18 dst).
       unfold inv_popped in H50.
       unfold inv_popped.
       intros.
       destruct (Z.eq_dec dst i).
       +++ subst dst.
           rewrite get_popped_meaning, upd_Znth_same in H51.
           3: rewrite upd_Znth_Zlength.
           all: omega.
       +++ pose proof (get_popped_range _ _ H51).
           rewrite upd_Znth_Zlength in H52 by omega.
           rewrite <- get_popped_irrel_upd in H51; try omega.
           specialize (H50 H51).
           destruct H50 as [? [? [? ?]]].
           exists x; split3; trivial.
           *** destruct H50 as [? [? [? [? ?]]]].
               split3; [| | split3]; trivial.
               1: rewrite upd_Znth_diff; omega.
               rewrite Forall_forall; intros.
               rewrite Forall_forall in H58.
               assert (snd x0 <> i). {
                 rewrite Forall_forall in H53.
                 specialize (H53 _ H59).
                 destruct H53. intro contra.
                 unfold VType in *.
                 rewrite contra in H60.
                 apply H36. trivial.
               }
               rewrite upd_Znth_diff; try omega.
               1: apply (H58 _ H59).
               1: unfold VType in *; rewrite H27;
                 apply (step_in_range2 g x); trivial.
               1: unfold VType in *; omega.
           *** rewrite Forall_forall; intros.
               rewrite Forall_forall in H53.
               specialize (H53 _ H55).
               destruct H53; split;
                 rewrite <- get_popped_irrel_upd; try omega; trivial.
               ---- rewrite H26. destruct H50.
                    apply (step_in_range g x x0); trivial.
               ---- intro contra. rewrite contra in H53.
                    apply H36. trivial.
               ---- rewrite H26. destruct H50.
                    apply (step_in_range2 g x x0); trivial.
               ---- intro contra. rewrite contra in H56.
                    apply H36. trivial.
     --- intros.
         destruct (Z.eq_dec dst i).
         +++ subst dst.
             (* this is the key change --
                i will now be locally optimal,
                thanks to the new path via u. *)
             unfold inv_unpopped; intros.
             unfold inv_popped in H18.
             destruct (H18 _ H21) as [p2u [? [? ?]]].
             unfold VType in *.
             rewrite upd_Znth_same by omega.
             exists p2u.
             split3; [| |split3; [| |split]]; trivial.
             *** destruct H52 as [? [? [? [? ?]]]].
                 split3; [ | | split3]; trivial.
                 ---- rewrite upd_Znth_diff by omega.
                      trivial.
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H58.
                      specialize (H58 _ H59).
                      unfold VType in *.
                      rewrite upd_Znth_diff; try omega; trivial.
                      rewrite H27.
                      apply (step_in_range2 g p2u); trivial.
                      intro.
                      rewrite Forall_forall in H53.
                      specialize (H53 _ H59).
                      destruct H53.
                      rewrite H60 in H61.
                      apply H36; trivial.
                         (*
                      

                   destruct H55.
                      apply valid_path_app_cons; trivial;
                        rewrite <- surjective_pairing; trivial.
                 ---- rewrite (surjective_pairing p2u) in *.
                      simpl.
                      unfold VType in *.
                      rewrite upd_Znth_same by omega.
                      replace (fst p2u) with src in *.
                      apply path_ends_app_cons; trivial.
                      destruct H55. simpl in H55; omega.
                 ---- rewrite <- path_cost_app_cons; trivial.
                      rewrite <- H57. omega.
                 ---- rewrite <- path_cost_app_cons; trivial.
                      rewrite upd_Znth_same by omega.
                      rewrite <- H57. omega.
                 ---- unfold VType in *.
                      rewrite Forall_forall. intros.
                      rewrite Forall_forall in H58, H53.
                      apply in_app_or in H59. destruct H59.
                      ++++ specialize (H58 _ H59).
                           specialize (H53 _ H59).
                           assert (snd x <> i). {
                             intro contra.
                             destruct H53.
                             rewrite contra in H60.
                             apply H36. trivial.
                           }
                           rewrite upd_Znth_diff; try omega.
                           rewrite H27.
                           apply (step_in_range2 g p2u); trivial.
                      ++++ simpl in H59. destruct H59; [| omega].
                           rewrite (surjective_pairing x) in *.
                           simpl. inversion H59.
                           rewrite upd_Znth_same; trivial.
                           omega. *)
             *** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H53.
                 specialize (H53 _ H55).
                 destruct H53; split.
                 ---- rewrite <- get_popped_irrel_upd; try omega; trivial.
                      1: { rewrite H26.
                           destruct H52.
                           apply (step_in_range g p2u); trivial. }
                      intro contra. unfold VType in *.
                      rewrite contra in H53.
                      apply H36. trivial.
                 ---- rewrite <- get_popped_irrel_upd; try omega; trivial.
                      1: { rewrite H26.
                           destruct H52.
                           apply (step_in_range2 g p2u); trivial. }
                      intro contra. unfold VType in *.
                      rewrite contra in H56.
                      apply H36. trivial.
             *** rewrite upd_Znth_same in H51 by omega.
                 destruct H52 as [_ [_ [_ [? _]]]].
                 rewrite <- H52. omega.
             *** rewrite upd_Znth_same by omega.
                 destruct H52 as [_ [_ [_ [? _]]]].
                 omega.
             *** intros.
                 admit.
                 (* come back soon. 
                  This is tricky admit #2, 
                  but it looks a lot better now! *)
         +++ assert (0 <= dst < i) by omega.
             (* we'll proceed by using the 
                old best-known path for dst *)
             specialize (H19 _ H51).
             unfold inv_unpopped in *.
             intros.
             rewrite upd_Znth_diff in H52 by omega.
             destruct (H19 H52) as [p2mom [? [? ?]]].
             unfold VType in *.
             remember (Znth dst prev_contents') as mom.
             exists p2mom. split3; [| |split3; [| |split]].
             *** destruct H53 as [? [? [? [? ?]]]].
                 split3; [| | split3]; trivial.
                 ---- rewrite upd_Znth_diff by omega;
                        rewrite <- Heqmom; trivial.
                 ---- rewrite (upd_Znth_diff dst i) by omega.
                      assert ((Znth dst prev_contents') <> i). {
                        (* the path could not have gone 
                           through i, since i is unpopped *)
                        intro.
                        apply H36.
                        (* same, will be okay once I 
                           have added in the fact that
                           mom is in popped
                         *)
                        admit.
                      }
                      rewrite upd_Znth_diff; try omega.
                      2: {
                        rewrite <- Heqmom.
                        rewrite H28.
                        destruct H2.
                        unfold vertex_valid in H2.
                        rewrite <- H2.
                        apply (valid_path_valid g p2mom); trivial.
                        destruct H56.
                        apply pfoot_in; trivial.
                      }
                      rewrite <- Heqmom.
                      trivial.
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H59.
                      specialize (H59 _ H60).
                      rewrite upd_Znth_diff; try omega.
                      1: unfold VType in *; rewrite H27;
                        apply (step_in_range2 g p2mom); trivial.
                      1: unfold VType in *; omega.
                      intro.
                      rewrite Forall_forall in H54.
                      specialize (H54 _ H60).
                      destruct H54 as [_ ?].
                      unfold VType in *.
                      rewrite H61 in H54.
                      apply H36. trivial.
             *** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H54.
                 specialize (H54 _ H56).
                 destruct H54.
                 repeat rewrite <- get_popped_irrel_upd; try omega; trivial.
                 ---- split; trivial.
                 ---- rewrite H26; destruct H53; apply (step_in_range2 g p2mom); trivial.
                 ---- intro contra. rewrite contra in H57.
                      apply H36; trivial.
                 ---- rewrite H26; destruct H53; apply (step_in_range g p2mom); trivial.
                 ---- intro contra. rewrite contra in H54.
                      apply H36; trivial.
             *** rewrite upd_Znth_diff by omega.
                 destruct H55; rewrite <- Heqmom; trivial.
             *** rewrite upd_Znth_diff by omega.
                 destruct H55 as [_ [? _]].
                 rewrite <- Heqmom; trivial.
             *** repeat rewrite upd_Znth_diff by omega.
                 destruct H55 as [_ [_ [? _]]].
                 rewrite <- Heqmom; trivial.
             *** intros. destruct H55 as [? [? [? ?]]].
                 rewrite upd_Znth_diff by omega.
                 rewrite <- Heqmom.
                 apply H61; trivial.
                 ---- destruct H56 as [? [? [? [? ?]]]].
                      split3; [| |split3]; trivial.
                      ++++ rewrite upd_Znth_diff in H64; try omega.
                           admit.
                           (* easy, but maybe even 
                            easier with change below...*)
                           intro.
                           (* Need to add that 
                              mom is in popped. *)
                           admit.
                      ++++ rewrite Forall_forall; intros.
                           rewrite Forall_forall in H65.
                           specialize (H65 _ H66).
                           unfold VType in *.
                           rewrite upd_Znth_diff in H65;
                             try omega.
                           rewrite H27.
                           apply (step_in_range2 g p2mom');
                             trivial.
                           intro.
                           admit.
     (* not sure *)
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H57.
                      specialize (H57 _ H62).
                      destruct H57.
                      destruct H56.
                      assert (0 <= snd x < Zlength priq_contents'). {
                        rewrite H26.
                        apply (step_in_range2 g p2mom');
                          trivial.
                      }
                      assert (0 <= fst x < Zlength priq_contents'). {
                        rewrite H26.
                        apply (step_in_range g p2mom');
                          trivial.
                      }
                      rewrite <- get_popped_irrel_upd in H57, H63; try omega.
                      split; trivial.
                      ++++ intro. rewrite get_popped_meaning in H63.
                           2: rewrite upd_Znth_Zlength; omega.
                           rewrite H67 in H63.
                           rewrite upd_Znth_same in H63.
                           omega.
                           omega.
                      ++++ intro. rewrite get_popped_meaning in H57.
                           2: rewrite upd_Znth_Zlength; omega.
                           rewrite H67 in H57.
                           rewrite upd_Znth_same in H57.
                           omega.
                           omega.                   
                 (*
                 rewrite Forall_forall; intros.
                 rewrite Forall_forall in H58.
                 specialize (H58 _ H59).
                 destruct H58.
                 rewrite <- get_popped_irrel_upd in H58;
                   try omega; trivial.
                 2: rewrite H26;
                   apply (step_in_range g p'); trivial.
                 2: { intro contra.
                      rewrite contra in H58.
                      rewrite get_popped_meaning in H58.
                      rewrite upd_Znth_same in H58 by omega.
                      omega.
                      rewrite upd_Znth_Zlength; omega.
                 }
                 split; trivial.
                 intro.
                 specialize (H60 H61).
                 rewrite <- get_popped_irrel_upd in H60;
                   try omega; trivial.
                 1: { rewrite H26.
                      apply (step_in_range2 g p'); trivial.
                 } 
                 intro.
                 rewrite H62 in H60. rewrite get_popped_meaning in H60.
                 2: rewrite upd_Znth_Zlength; omega.
                 rewrite upd_Znth_same in H60; omega. *)
     --- intros.
         assert (i <= dst < SIZE) by omega.
         destruct (Z.eq_dec dst i).
         1: subst dst; omega.
         rewrite upd_Znth_diff in H51 by omega.
         destruct (H20 _ H52 H51) as [p2mom [? [? ?]]].
         unfold VType in *.
         remember (Znth dst prev_contents') as mom.
         rewrite upd_Znth_diff by omega.
         exists p2mom.
         destruct H55 as [? [? [? ?]]].
         split3; [| | split3; [| | split]]; trivial.
         +++ destruct H53 as [? [? [? [? ?]]]].
             split3; [| | split3]; trivial.
             *** rewrite <- Heqmom. trivial.
             *** rewrite <- Heqmom.
                 rewrite upd_Znth_diff; try omega; trivial.
                 admit. (* doable, but... *)
                 intro. (* need to add info about mom in poped *)
                 admit.
             *** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H62.
                 specialize (H62 _ H63).
                 unfold VType in *.
                 rewrite upd_Znth_diff; try omega; trivial.
                 ---- rewrite H27.
                      apply (step_in_range2 g p2mom); trivial.
                 ---- rewrite Forall_forall in H54.
                      specialize (H54 _ H63).
                      destruct H54 as [? [? [? ?]]].
                      intro. rewrite H67 in H64.
                      apply H36. trivial.
         +++ rewrite Forall_forall; intros.
             rewrite Forall_forall in H54.
             specialize (H54 _ H59).
             destruct H54 as [? [? [? ?]]].
             destruct H53.
             split3; [| |split]; trivial;
             rewrite <- get_popped_irrel_upd;
             try omega; trivial.
             *** rewrite H26. apply (step_in_range g p2mom); trivial.
             *** intro. rewrite H64 in H54. apply H36; trivial.
             *** rewrite H26. apply (step_in_range2 g p2mom); trivial.
             *** intro. rewrite H64 in H60.
                 apply H36. trivial. 
         +++ intros. rewrite <- Heqmom; trivial.
         +++ rewrite <- Heqmom; trivial.
         +++ rewrite <- Heqmom.
             rewrite upd_Znth_diff; omega.
         +++ intros. rewrite <- Heqmom.
             apply H58.
             *** destruct H59 as [? [? [? [? ?]]]].
                 split3; [| |split3]; trivial.
                 ---- rewrite upd_Znth_diff in H64;
                        try omega; trivial.
                      admit. (* doable, but... *)
                      intro. (* need more info *)
                      admit.
                 ---- rewrite Forall_forall; intros.
                      rewrite Forall_forall in H65.
                      specialize (H65 _ H66).
                      unfold VType in *.
                      rewrite upd_Znth_diff in H65; try omega; trivial.
                      ++++ rewrite H27.
                           apply (step_in_range2 g p2mom'); trivial.
                      ++++ intro. rewrite Forall_forall in H60.
                           specialize (H60 _ H66).
                           destruct H60 as [_ ?].
                           rewrite H67 in H60.
                           rewrite get_popped_meaning in H60.
                           2: rewrite upd_Znth_Zlength; omega.
                           rewrite upd_Znth_same in H60; omega.
             *** rewrite Forall_forall; intros.
                 rewrite Forall_forall in H60.
                 specialize (H60 _ H62).
                 destruct H60 as [? [? [? ?]]].
                 rewrite <- get_popped_irrel_upd in H60, H63; try omega; trivial.
                 split3; [| |split]; trivial.
                 ---- rewrite H26.
                      destruct H59.
                      apply (step_in_range2 g p2mom');
                        trivial.
                 ---- intro. rewrite H66 in H63.
                      rewrite get_popped_meaning in H63.
                      rewrite upd_Znth_same in H63; omega.
                      rewrite upd_Znth_Zlength; omega.
                 ---- rewrite H26.
                      destruct H59.
                      apply (step_in_range g p2mom');
                        trivial.
                 ---- intro. rewrite H66 in H60.
                      rewrite get_popped_meaning in H60.
                      rewrite upd_Znth_same in H60; omega.
                      rewrite upd_Znth_Zlength; omega.
             *** trivial.
     --- apply get_popped_irrel_upd; try omega; assumption.
     --- split3; apply inrange_upd_Znth; trivial; try omega.
  ** rewrite Int.signed_repr in H35
      by (unfold inf in *; rep_omega).
     (* This is the branch where I didn't
        make a change to the i'th vertex *)
     forward.
     Exists prev_contents' priq_contents' dist_contents'.
     entailer!.
     remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
     split.
     --- intros.
         (* show that moving one more step 
            still preserves the for loop
            invariant *)
         destruct (Z.eq_dec dst i).
         2: apply H19; omega.
         subst dst.
         (* i already obeys the weaker inv_unpopped,
            ie inv_unpopped without going via u.

            Now I must show that it actually satisfies 
            inv_unpopped as it stands.
            
            ie, it is better off going without u
          *)
         unfold inv_unpopped; intros.
         assert (i <= i < SIZE) by omega.
         destruct (H20 i H49 H48) as [? [? [? [? [? [? ?]]]]]].
         (* now I must show that the same path
            is actually still okay *)
         exists x; split3; [| |split3; [| |split]]; trivial.
         +++ rewrite Forall_forall; intros.
             rewrite Forall_forall in H51.
             specialize (H51 _ H56).
             destruct H51 as [? [? [? ?]]].
             split; trivial.
         +++ intros. admit. (* interesting case *)
     --- intros. destruct (Z.eq_dec dst i).
         +++ subst dst. omega.
         +++ apply H20; omega.
           ++ (* [i] was not a neighbor of [u]. 
                 prove the for loop's invariant holds *)
             replace 8 with SIZE in H31 by omega.
             rewrite inf_eq2 in H31.
             forward.
             Exists prev_contents' priq_contents' dist_contents'.
             entailer!.
             remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
             split; intros.
             ** destruct (Z.eq_dec dst i).
                --- subst dst. 
             (* Will need to use the second half of the 
                for loop's invariant.          
                Whatever path worked for i then will 
                continue to work for i now:
                i cannot be improved
                by going via u *)
                    unfold inv_unpopped; intros.
                    assert (i <= i < SIZE) by omega.
                    destruct (H20 i H45 H44) as [? [? [? [? [? [? ?]]]]]].
                    exists x; split3; [| |split3; [| |split]]; trivial.
                    +++ rewrite Forall_forall; intros.
                        rewrite Forall_forall in H47.
                        specialize (H47 _ H52).
                        destruct H47 as [? [? [? ?]]].
                        split; trivial.
                    +++ intros. apply H51; trivial.
                        unfold VType in *.
                        rewrite Forall_forall; intros.     
                        rewrite Forall_forall in H53.
                        specialize (H53 _ H55).
                        destruct H53.
                        split3; [| |split]; trivial.
                        admit. admit.
                        (* interesting case -- 
                           show that the path neednt'
                           go through u *)
                --- apply H19; omega.
             ** destruct (Z.eq_dec dst i).
                --- omega. 
                --- apply H20; omega.
        -- (* from the for loop's inv, prove the while loop's inv. *)
              
          Intros prev_contents' priq_contents' dist_contents'.
          Exists prev_contents' priq_contents' dist_contents'.
          entailer!.
          remember (find priq_contents (fold_right Z.min (hd 0 priq_contents) priq_contents) 0) as u.
          unfold dijkstra_correct. 
          (* and now H14 is exactly the 
             second clause? *)
          (* plan:
             1. eestablish "inv2" for u's unpopped neighbors
             2. establish "inv1" for u itself  
             3. establish "inv1" for all the other previously-popped vertices
           *)
          split3; trivial.
          apply H16; trivial.
          admit.
(* need to add something about this
   unseen case to the for loop's invariant *)
      * (* after breaking, prove break's postcondition *)
        assert (isEmpty priq_contents = Vone). {
          destruct (isEmptyTwoCases priq_contents);
            rewrite H12 in H11; simpl in H11; now inversion H11.
        }
        clear H11.
        forward. Exists prev_contents priq_contents dist_contents.
        entailer!. apply (isEmptyMeansInf _ H12).
    + (* from the break's postcon, prove the overall postcon *)
      Intros prev_contents priq_contents dist_contents.
      forward. Exists prev_contents dist_contents priq_contents. entailer!. 
Abort.
