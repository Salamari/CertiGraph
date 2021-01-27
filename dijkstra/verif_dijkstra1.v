Require Import CertiGraph.graph.SpaceAdjMatGraph1.
Require Import CertiGraph.dijkstra.dijkstra_env.
Require Import CertiGraph.dijkstra.MathDijkGraph.
Require Import CertiGraph.dijkstra.dijkstra_math_proof.
Require Import CertiGraph.dijkstra.dijkstra_spec1.

Local Open Scope Z_scope.

Section DijkstraProof.
  
  (* The invariants have been dragged out of the 
     proof for readability and reuse
   *)

  Context {size: Z}.
  Context {inf: Z}.
  Context {Z_EqDec : EquivDec.EqDec Z eq}.

  Lemma body_getCell: semax_body Vprog (@Gprog size inf) f_getCell (@getCell_spec size inf).
  Proof.
    start_function.
    rewrite (SpaceAdjMatGraph_unfold _ id _ _ addresses u); trivial.
    assert (Zlength (map Int.repr (Znth u (@graph_to_mat size g id))) = size). {
      unfold graph_to_mat, vert_to_list.
      rewrite Znth_map; repeat rewrite Zlength_map.
      all: rewrite nat_inc_list_Zlength; lia.
    }
    assert (0 <= i < Zlength (map Int.repr (Znth u (@graph_to_mat size g id)))) by lia.
    assert (0 <= i < Zlength (Znth u (@graph_to_mat size g id))). {
      rewrite Zlength_map in H1. lia.
    }
    Intros.
    freeze FR := (iter_sepcon _ _) (iter_sepcon _ _).
    unfold list_rep.
    forward. forward. forward. thaw FR.
    rewrite (SpaceAdjMatGraph_unfold _ id _ _ addresses u); trivial.
    cancel.
  Qed.

  Definition keys_dist_linked_correctly i keys dist h :=
    forall k,
      Znth i keys = k ->
      find_item_by_key (heap_items h) k =
      [(k, Znth i dist, Int.repr i)] \/
      ~In k (proj_keys h).
    
  
  Definition dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr keys_ptr temp_item arr addresses :=
    EX i : Z,
    EX h : heap,
    EX keys: list key_type,
    EX dist_and_prev : list int,
    PROP (heap_capacity h = size;
         heap_size h = i;
         Permutation keys (proj_keys h);
         forall j,
           0 <= j < i ->
           keys_dist_linked_correctly j keys dist_and_prev h;
         dist_and_prev = list_repeat (Z.to_nat i) (Int.repr inf))
    LOCAL (temp _dist (pointer_val_val dist_ptr);
          temp _prev (pointer_val_val prev_ptr);
          temp _src (Vint (Int.repr src));
          temp _pq priq_ptr;
          temp _graph (pointer_val_val arr);
          temp _size (Vint (Int.repr size));
          temp _keys (pointer_val_val keys_ptr);
          temp _inf (Vint (Int.repr inf));
          temp _temp_item (pointer_val_val temp_item))
    SEP (valid_pq priq_ptr h;
         hitem_ (pointer_val_val temp_item);
        data_at Tsh
                (tarray tint size)
                (map Vint (map Int.repr keys) ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val keys_ptr);
        data_at Tsh
                (tarray tint size)
                (map Vint dist_and_prev ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val prev_ptr);
        data_at Tsh
                (tarray tint size)
                (map Vint dist_and_prev ++
                     (list_repeat (Z.to_nat (size-i)) Vundef))
                (pointer_val_val dist_ptr);
        @SpaceAdjMatGraph size CompSpecs sh id
                          g (pointer_val_val arr) addresses;
        free_tok (pointer_val_val keys_ptr) (size * sizeof tint);
        free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr))).

  Definition src_picked_first h src (popped: list V) :=
    0 < Zlength (heap_items h) ->
    exists min_item,
      In min_item (heap_items h) /\
      Forall (cmp_rel min_item) (heap_items h) /\
      (popped = [] -> src = Int.signed (snd min_item)).
        
  Definition dijk_forloop_inv (g: @DijkGG size inf) sh src keys
             dist_ptr prev_ptr keys_ptr priq_ptr graph_ptr temp_item addresses :=
    EX prev : list V,
    EX dist : list Z,
    EX popped : list V,
    EX h : heap,
    PROP (
        dijkstra_correct g src popped prev dist;
      
      Znth src dist = 0;
      Znth src prev = src;

      popped <> [] -> In src popped;
      heap_capacity h = size;
      Permutation keys (proj_keys h);
      
      forall i,
        vvalid g i ->
        keys_dist_linked_correctly i keys (map Int.repr dist) h;

      src_picked_first h src popped; 

      (* TODO:
         commenting out the two below for now, but I'll have to see
         if I need some new versions of these in the proofs later on *)

      (* A fact about the relationship b/w
         the priq and popped arrays *)
      (*
      forall v,
        vvalid g v ->
        In v popped <-> Znth v priq = Z.add inf 1;
       *)
      
      (* A fact about the relationship b/w 
         dist and priq arrays *)
      (*
      forall dst, vvalid g dst ->
                  ~ In dst popped ->
                  Znth dst priq = Znth dst dist;
       *)
      
      (* Information about the ranges of the three arrays *)
      @inrange_prev size inf prev;
      @inrange_dist inf dist)
         
         LOCAL (temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf));
               temp _temp_item (pointer_val_val temp_item))
         SEP (valid_pq priq_ptr h;
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr prev))
                     (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr keys))
                     (pointer_val_val keys_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             hitem_ (pointer_val_val temp_item);
             free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr));
             free_tok (pointer_val_val keys_ptr) (size * sizeof tint)).
  
  Definition dijk_forloop_break_inv (g: @DijkGG size inf) sh
             src keys dist_ptr prev_ptr keys_ptr priq_ptr
             graph_ptr temp_item addresses :=
    EX prev: list V,
    EX dist: list Z,
    EX popped: list V,
    EX h : heap,
    PROP (

        (* This fact comes from breaking while *)
        heap_size h = 0;
         
      (* And the correctness condition is established *)
      dijkstra_correct g src popped prev dist)
         LOCAL (temp _pq priq_ptr;
               temp _temp_item (pointer_val_val temp_item))
         SEP (data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id
                               g (pointer_val_val graph_ptr) addresses;
             valid_pq priq_ptr h;
             data_at Tsh (tarray tint (heap_capacity h)) (map Vint (map Int.repr keys))
                     (pointer_val_val keys_ptr);
             data_at_ Tsh (tarray tint (sizeof (Tstruct _structItem noattr) / sizeof tint))
                      (pointer_val_val temp_item);
             free_tok (pointer_val_val temp_item) (sizeof (Tstruct _structItem noattr));
             free_tok (pointer_val_val keys_ptr) (heap_capacity h * sizeof tint)).
  
  Definition dijk_inner_forloop_inv (g: @DijkGG size inf) sh
             src ti min_item keys
             dist_ptr prev_ptr priq_ptr keys_ptr h graph_ptr addresses :=
    EX i : Z,
    EX prev' : list V,
    EX dist' : list Z,
    EX popped' : list V,
    EX h' : heap,
    EX u : Z,

    PROP (
        0 < Zlength (heap_items h) ->
          In min_item (heap_items h) /\
          Forall (cmp_rel min_item) (heap_items h) /\
          u = Int.signed (snd min_item);

      
        (* inv_popped is not affected *)
        forall dst,
          vvalid g dst ->
          inv_popped g src popped' prev' dist' dst;
      
      (* inv_unpopped is restored for those vertices
         that the for loop has scanned and repaired *)
      forall dst,
        0 <= dst < i ->
        inv_unpopped g src popped' prev' dist' dst;
      
      (* a weaker version of inv_popped is
         true for those vertices that the
         for loop has not yet scanned *)
      forall dst,
        i <= dst < size ->
        inv_unpopped_weak g src popped' prev' dist' dst u;
      
      (* similarly for inv_unseen,
         the invariant has been
         restored until i:
         u has been taken into account *)
      forall dst,
        0 <= dst < i ->
        inv_unseen g src popped' prev' dist' dst;
      
      (* and a weaker version of inv_unseen is
         true for those vertices that the
         for loop has not yet scanned *)
      forall dst,
        i <= dst < size ->
        inv_unseen_weak g src popped' prev' dist' dst u;
      
      (* further, some useful facts about src... *)
      Znth src dist' = 0;
      Znth src prev' = src;
      popped' <> [] -> In src popped';

      src_picked_first h' src popped';
           
      (* a useful fact about u *)
      In u popped';

      (*
      (* A fact about the relationship b/w 
         priq and popped arrays *)
      forall v,
        vvalid g v ->
        In v popped' <-> Znth v priq' = Z.add inf 1;
      
      (* A fact about the relationship b/w 
         dist and priq arrays *)
      forall dst,
        vvalid g dst ->
        ~ In dst popped' ->
        Znth dst priq' = Znth dst dist';
       *)
      
      (* the lengths of the threee arrays *)
      (* Zlength priq' = size; *)
      Zlength dist' = size;
      Zlength prev' = size;
                                                           
      (* and ranges of the three arrays *)
      @inrange_prev size inf prev';
      (* @inrange_priq inf priq'; *)
      @inrange_dist inf dist')
         
         LOCAL (temp _u (Vint (Int.repr u));
               temp _dist (pointer_val_val dist_ptr);
               temp _prev (pointer_val_val prev_ptr);
               temp _src (Vint (Int.repr src));
               temp _pq priq_ptr;
               temp _graph (pointer_val_val graph_ptr);
               temp _size (Vint (Int.repr size));
               temp _inf (Vint (Int.repr inf)))
         
         SEP (valid_pq priq_ptr h';
             data_at Tsh
                      (tarray tint size)
                      (map Vint (map Int.repr prev'))
                      (pointer_val_val prev_ptr);
             data_at Tsh
                     (tarray tint size)
                     (map Vint (map Int.repr dist'))
                     (pointer_val_val dist_ptr);
             @SpaceAdjMatGraph size CompSpecs sh id 
                               g (pointer_val_val graph_ptr) addresses;
             hitem min_item (pointer_val_val ti) *
             data_at Tsh (tarray tint (heap_capacity h)) (map Vint (map Int.repr keys))
                     keys_ptr * free_tok (pointer_val_val ti) 12 *
             free_tok keys_ptr (heap_capacity h * 4)).
  
  (* DIJKSTRA PROOF BEGINS *)

  Lemma body_dijkstra: semax_body Vprog (@Gprog size inf) f_dijkstra (@dijkstra_spec size inf).
  Proof.
    start_function.
    pose proof (size_further_restricted g).
    pose proof (inf_bounds g).
    rename H1 into Hsz.
    rename H2 into Hinf.
    assert (Hmaxranges: Int.max_signed <= Int.max_unsigned) by now compute.
    forward_call ((sizeof(Tstruct _structItem noattr))).
    Intros ti. rename H1 into H_mc_ti.
    forward_call (size * sizeof(tint)).
    1: simpl; lia.
    Intro keys_pv.
    remember (pointer_val_val keys_pv) as pre_keys.
    forward_call (size).
    1: split. rep_lia.
       admit. (* Aquinas: Yes, probably you need to strengthen your precondition *)
    (* HELP
       Does this sound okay? Should I add to precon? 
       I have not given any thought to 
       Int.max_unsgined vs Int.max_signed
       in Dijkstra verifications.
     *)
    Intros temp.
    destruct temp as [priq_ptr h]; simpl fst in *; simpl snd in *.
    rename H1 into H_mc_keys.
    rename H2 into H_h_sz.
    rename H3 into H_h_cap.

    forward_for_simple_bound
      size
      (dijk_setup_loop_inv g sh src dist_ptr prev_ptr priq_ptr keys_pv ti graph_ptr addresses).
    - Exists h (@nil key_type) (@nil int).
      entailer!.
      1: { rewrite Zlength_nil_inv.
           apply Permutation_refl.
           rewrite proj_keys_Zlength; trivial.
      }
      remember (heap_capacity h) as size.
      rewrite app_nil_l, data_at__tarray.
      replace (size * sizeof tint / sizeof tint) with size.
      2: rewrite Z.div_mul; trivial; simpl; lia.
      entailer!. 
      apply (weaken_prehitem_ (pointer_val_val ti)).
      trivial.
      
    - rename keys into keys0.
      forward. forward.
      forward_call (priq_ptr, h0, inf, Int.repr i).
      1: lia.
      Intro temp'. destruct temp' as [h' key].
      forward.
      repeat rewrite upd_Znth_list_repeat; try lia.
      simpl fst in *. simpl snd in *.
      assert (Zlength keys0 = i). {
        unfold key_type in *.
        rewrite (Permutation_Zlength _ _ H4).
        now rewrite proj_keys_Zlength.
      }
      (* A number of tweaks to the keys array in SEP... *)
      rewrite upd_Znth_app2.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *.
           rewrite Zlength_list_repeat; lia.
      }
      replace (i - Zlength (map Vint (map Int.repr keys0))) with 0.
      2: { repeat rewrite Zlength_map.
           unfold key_type in *. lia.
      }
      replace (Z.to_nat (size - i)) with (Z.to_nat 1 + Z.to_nat (size - (i + 1)))%nat.
      2: lia. 
      rewrite <- (list_repeat_app _ (Z.to_nat 1) (Z.to_nat (size - (i + 1)))).
      simpl list_repeat at 1.
      rewrite upd_Znth_app1.
      2: { rewrite binary_heap_Zmodel.Zlength_one. lia. }
      replace (upd_Znth 0 [Vundef] (Vint (Int.repr key))) with [(Vint (Int.repr key))].
      2: { rewrite upd_Znth0. reflexivity. }
      (* and done *)
      
      Exists h' (keys0 ++ [key]) (dist_and_prev ++ [Int.repr inf]).
      entailer!;
              remember (heap_capacity h) as size;
        remember (heap_size h0) as i;
        symmetry in Heqsize; rename Heqsize into H_h_cap;
          symmetry in Heqi; rename Heqi into H3;
            clear H10 H11 H12 H13 H14 H15 H16 H17
              H18 H19 H20 H21 PNpriq_ptr.
      + split3; [| |split].
        * rewrite <- H3. unfold heap_size.
          pose proof (Permutation_Zlength _ _ H8).
          rewrite Zlength_cons, <- Z.add_1_r in H6.
          symmetry. trivial.
        * unfold proj_keys.         
(*
H4: Permutation keys0 (proj_keys h0)
H8: Permutation ((key, Int.repr inf, Int.repr i) :: heap_items h0) (heap_items h')
 *)
(*
forall a l1 l2, 
Permutation (a :: l1) l2 ->
exists l2a and l2b such that
       l2 = l2a ++ [a] ++ l2b. 
   and
        Permutation l1 (l2a ++ l2b)
 *)
          (* HELP if you have time *)
          admit.

        * red. intros.
          rewrite <- (list_repeat1 (Int.repr inf)).
          rewrite list_repeat_app, <- Z2Nat.inj_add by lia.
          rewrite Znth_list_repeat_inrange by lia.
          destruct (Z.eq_dec i j).
          -- subst j. left.
             admit.
(* H8: Permutation ((k, Int.repr inf, Int.repr i) :: heap_items h0) (heap_items h') *)
             (* HELP if you have time *)
          -- assert (0 <= j < i) by lia.
             clear H6 n.
             rewrite Znth_app1 in H10 by lia.
             red in H5.
             specialize (H5 _ H11 _ H10). 
             rewrite Znth_list_repeat_inrange in H5 by lia.
             admit.
          (* HELP if you have time *)
        * rewrite <- list_repeat1, list_repeat_app,
          Z2Nat.inj_add. trivial. lia. lia.
      + repeat rewrite map_app; rewrite app_assoc; cancel.
        rewrite list_repeat1, upd_Znth_app2,
        Zlength_map, Zlength_list_repeat, Z.sub_diag,
        upd_Znth_app1, upd_Znth0, <- app_assoc.
        cancel.
        rewrite binary_heap_Zmodel.Zlength_one. lia.
        lia.
        rewrite Zlength_map, Zlength_app,
        binary_heap_Zmodel.Zlength_one,
        Zlength_list_repeat, Zlength_list_repeat. lia.
        lia. lia.
    - (* At this point we are done with the
       first for loop. The arrays are all set to inf. *)
      Intros ha keys dist_and_prev.
      (* the keys array will not change *)
      (* pre_keys are no longer needed *)
      clear Heqpre_keys H_mc_keys pre_keys.
      remember (pointer_val_val keys_pv) as keys_ptr.

      rewrite Z.sub_diag, list_repeat_0, app_nil_r, app_nil_r.
      assert (H_keys_sz: Zlength keys = size). {
        unfold key_type in *.
        rewrite (Permutation_Zlength _ _ H3).
        rewrite proj_keys_Zlength; trivial.
      }
      assert (Htemp: 0 <= src < Zlength keys) by lia.
      forward. forward. forward.
      clear Htemp.
      forward_call (priq_ptr, ha, Znth src keys, Int.repr 0).
      Intros hb.
      rename H6 into H_ha_hb_rel.
      assert (H_hb_cap: heap_capacity hb = size) by lia.
      clear H7.
      (* Special values for src have been inserted *)
      
      (* We will now enter the main while loop.
       We state the invariant just below, in PROP.

       VST will first ask us to first show the
       invariant at the start of the loop
       *)
      
      forward_loop
      (dijk_forloop_inv g sh src keys dist_ptr prev_ptr keys_pv priq_ptr graph_ptr ti addresses)
      break: (dijk_forloop_break_inv g sh src keys dist_ptr prev_ptr keys_pv priq_ptr graph_ptr ti addresses).
      + unfold dijk_forloop_inv.
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) src).
        Exists (upd_Znth src (@list_repeat V (Z.to_nat size) inf) 0).
        Exists (@nil V) hb.
        repeat rewrite <- upd_Znth_map; entailer!.

        clear H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
              H18 PNpriq_ptr PNkeys_ptr.
        
        remember (heap_capacity h) as size.
        assert (Htemp: Zlength (list_repeat (Z.to_nat size) inf) = size). {
          rewrite Zlength_list_repeat; ulia.
        }
        
        split3; [| |split3; [| |split3]].
        * apply (dijkstra_correct_nothing_popped g src); trivial.
        * rewrite upd_Znth_same; ulia. 
        * rewrite upd_Znth_same; ulia.
        * (* Hrmm this seems false. Do I need it? *)
          admit.
        * red. intros.
          destruct (Z.eq_dec i src).
          -- subst i.
             rewrite upd_Znth_same.
             admit. (* HELP if you have time *)
             rewrite Zlength_map, Zlength_list_repeat; lia.
          -- rewrite upd_Znth_diff; trivial.
             2,3: rewrite Zlength_map, Zlength_list_repeat; try lia.
             rewrite map_list_repeat, Znth_list_repeat_inrange.
             2,3: apply (vvalid_meaning g); trivial.
             admit. (* HELP if you have time *)
        * red. intros.
          destruct (exists_min_in_list (heap_items hb) H5) as [min [? ?]].
          exists min. split3; trivial.
          intros _.
          (* ha is all infs (see H4)
             and hb is ha with src tweaked to 0 (see H_ha_hb_rel)
             and 0 < inf, 
             so this is true
           *)
          admit.
        * split; red; apply Forall_upd_Znth;
            try apply Forall_list_repeat; ulia.
        * repeat rewrite map_list_repeat; cancel.

      + (* Now the body of the while loop begins. *)
        unfold dijk_forloop_inv.
        rename H1 into H_ha_cap.
        rename H2 into H_ha_size.
        rename H3 into H_keys_ha.
        subst dist_and_prev.
        rename H4 into H_keys_dist_ha.

        Intros prev dist popped hc.
        (* may need a link between hc and hb? *)
        
        assert_PROP (Zlength prev = size).
        { entailer!. now repeat rewrite Zlength_map in *. }
        assert_PROP (Zlength dist = size).
        { entailer!. now repeat rewrite Zlength_map in *. }

        rename H5 into H_hc_cap.
        forward_call (priq_ptr, hc).
        forward_if. (* checking if it's time to break *)
        * (* No, don't break. *)

          assert_PROP (0 <= heap_size hc <= Int.max_unsigned). {
            unfold valid_pq.
            Intros arr junk lookup l_contents.
            entailer!. 
            unfold heap_size. 
            pose proof (Zlength_nonneg junk). 
            split; [apply Zlength_nonneg|]. 
            apply Z.le_trans with (m := heap_capacity hc).
            1: rewrite <- H16, Zlength_app; lia.
            lia.
          }
          rewrite Int.unsigned_repr in H5 by trivial.
          freeze FR := (data_at _ _ _ _)
                         (data_at _ _ _ _)
                         (data_at _ _ _ _)
                         (free_tok _ _)
                         (free_tok _ _)
                         (SpaceAdjMatGraph _ _ _ _ _).      
          forward_call (priq_ptr,
                        hc,
                        pointer_val_val ti). 
          1: lia.

          (* hd is skipped because it is "head" *)
          Intros temp. destruct temp as [he min_item]. 
          simpl fst in *. simpl snd in *.
          thaw FR.
          unfold hitem.
          forward.
          replace (data_at Tsh t_item (heap_item_rep min_item) (pointer_val_val ti)) with (hitem min_item (pointer_val_val ti)).
          2: unfold hitem; trivial.
          simpl.
          remember (Int.signed (snd min_item)) as u.
          
          
          (* u is the minimally chosen item from the
           "seen but not popped" category of vertices *)

          (* We prove a few useful facts about u: *)
          assert (H_u_valid: vvalid g u). {
            apply (vvalid_meaning g); trivial.
            replace size with (heap_capacity he) by lia.
            (* rewrite <- H14, H_hc_cap. *)
            admit.
            (* HELP if you have time
               should come from PQ. Is it already here? *)
          }
          
          assert (0 <= u < size). {
            apply (vvalid_meaning g) in H_u_valid; trivial.
          } 

          assert (~ (In u popped)). {
            intro.
            (*
            I used to get this via the link between 
            popped and priq. I may need to reestablish that
            TODO        
             *)
            admit.
          (*
            rewrite H_popped_priq_link in H13; trivial.
            rewrite <- isEmpty_in' in H11.
            destruct H11 as [? [? ?]].
            subst u.
            rewrite Znth_find in H13.
            1: pose proof (fold_min _ _ H11); lia.
            rewrite <- Znth_0_hd by ulia.
            apply min_in_list;
              [ apply incl_refl | apply Znth_In; ulia].
 *)
          }
                    
          assert (Htemp: 0 <= u < Zlength dist) by lia.
          pose proof (Znth_dist_cases _ _ Htemp H10).
          clear Htemp.
          
          (* This is the priq array with which
           we will enter the for loop.
           The dist and prev arrays are the same.
           Naturally, going in with this new priq
           and the old dist and prev means that
           dijkstra_correct is currently broken.
           The for loop will repair this and restore
           dijkstra_correct.
           *)


          forward_for_simple_bound
            size
            (dijk_inner_forloop_inv
            g sh src ti min_item keys
               dist_ptr prev_ptr priq_ptr keys_ptr hc graph_ptr addresses).
          -- (* We start the for loop as planned --
              with the old dist and prev arrays,
              and with a priq array where u has been popped *)
            (* We must prove the for loop's invariants for i = 0 *)
            Exists prev.
            Exists dist.
            Exists (u :: popped).
            Exists he.
            Exists u.
            entailer!.
            2: {
              replace (heap_capacity h) with (heap_capacity he).
              replace (heap_capacity hc) with (heap_capacity he).
              cancel. lia.
            }
            remember (Int.signed (snd min_item)) as u.
            remember (heap_capacity h) as size. 
            symmetry in Heqsize.
            clear H20 H21 H22 H23 H24 H25 H26 H27 H28
                  H29 H30 H31 H32 PNpriq_ptr.

            red in H8.
            assert (0 < Zlength (heap_items hc)) by admit.
            destruct (H8 H20) as [min_item' [_ [? ?]]].
            replace min_item' with min_item in *.
            rewrite <- Hequ in H22.
            2: { admit. (* TODO *)
            }
            
            split3; [| | split3; [| |split3; [| |split]]]; trivial.
            ++ intros.
               split3; trivial.
               admit.
               (* TODO not hard *)

            ++ (* if popped = [], then 
                prove inv_popped for [u].
                if popped <> [], then we're set
                *)
               destruct popped eqn:?.
               2: {
                 (* TODO update the lemma *)
                 (* apply (inv_popped_add_u _ _ _ _ _ _ priq); try ulia. *)
                 (* apply H_popped_src_1; inversion 1. *)
                 admit.
               }
               replace u with src in *.
               2: apply H22; trivial. 
               intros. intro.
               simpl in H24; destruct H24; [|lia].
               subst dst; clear H23.
               destruct H19; [left | right].
               ** exfalso. rewrite H19 in H2. ulia.
               ** exists (src, []). split3.
                  --- split3; [| |split3]; trivial.
                      +++ split; trivial.
                      +++ rewrite path_cost.path_cost_zero; ulia.
                      +++ apply Forall_forall.
                          inversion 1.
                  --- unfold path_in_popped.
                      intros. 
                      inversion H23.
                      +++ simpl in H24. 
                          subst step. simpl; left; trivial.
                      +++ destruct H24 as [? [? _]].
                          inversion H24.
                  --- red. intros. rewrite path_cost.path_cost_zero; try ulia.
                      apply path_cost_pos; trivial.
  
            ++ intros.
               apply (vvalid_meaning g) in H23.
               apply inv_unpopped_weak_add_unpopped; trivial.

            ++ intros.
               apply (vvalid_meaning g) in H23.
               apply (inv_unseen_weak_add_unpopped g prev _ _ src); trivial.

            ++ intros. clear H23.
               destruct popped eqn:?.
               2: right; apply H4; inversion 1.
               simpl. left. symmetry. apply H22; trivial.

            ++ red. intros.
               exists min_item; split3; trivial.
               admit. (* false... *)
               intro. inversion H24.
               
            ++ apply in_eq.

            ++ subst u.
               rewrite Int.repr_signed. trivial.

          -- (* We now begin with the for loop's body *)
            rewrite <- Hequ.
            freeze FR := (data_at _ _ _ _) (data_at _ _ _ _) (data_at _ _ _ _).
            Intros.
            rename H16 into H_inv_popped.
            rename H17 into H_inv_unpopped.
            rename H18 into H_inv_unpopped_weak.
            rename H19 into H_inv_unseen.
            rename H20 into H_inv_unseen_weak.
            rename H21 into H16.
            rename H22 into H17.
            rename H23 into H18.
            rename H24 into H19.
            rename H25 into H20.
            rename H26 into H_priq_popped_link.
            rename H27 into H_priq_dist_link.
            rename H31 into H21.
            rename H32 into H22.
            rename H33 into H23.
            rename H28 into H24.
            rename H29 into H25.
            rename H30 into H26.

            forward_call (sh, g, graph_ptr, addresses, u, i).
            remember (Znth i (Znth u (@graph_to_mat size g id))) as cost.

            assert (H_i_valid: vvalid g i). {
              apply (vvalid_meaning g); trivial.
            }

            rewrite <- elabel_Znth_graph_to_mat in Heqcost; try ulia.

            forward_if.
            ++ rename H27 into Htemp.
               assert (0 <= cost <= Int.max_signed / size). {
                 pose proof (edge_representable g (u, i)).
                 rewrite Heqcost in *.
                 apply (valid_edge_bounds g).
                 rewrite (evalid_meaning g). split; trivial.
                 rewrite Int.signed_repr in Htemp; trivial.
               }
               clear Htemp.
               assert (H_ui_valid: evalid g (u,i)). {
                 apply evalid_dijk with (cost0 := cost);
                   trivial.
               }
               
               assert (0 <= Znth u dist' <= inf). {
                 assert (0 <= u < Zlength dist') by lia.
                 apply (sublist.Forall_Znth _ _ _ H28) in H23.
                 assumption.
               }
               assert (0 <= Znth i dist' <= inf). {
                 assert (0 <= i < Zlength dist') by lia.
                 apply (sublist.Forall_Znth _ _ _ H29) in H23.
                 assumption.
               }
               assert (0 <= Znth u dist' + cost <= Int.max_signed). {
                 (* IMPORTANT:
                  the key point where 
                  we were forced to lower
                  inf's upper bound
                  *)
                 pose proof (inf_further_restricted g).
                 lia.
               }
               thaw FR.
               forward. forward. forward_if.

               ** rename H31 into H_improvement.
                  (* We know that we are definitely
                   going to make edits in the arrays:
                   we have found a better path to i, via u *)
                  rename H28 into Htemp.
                  assert (H28: 0 <= Znth u dist' < inf) by lia.
                  clear Htemp.

                  assert (H_i_not_popped: ~ In i (popped')). { 
                    apply (not_in_popped g src u i cost prev' dist'); trivial.
                  }
                  assert (Htemp : 0 <= i < Zlength dist') by lia.
                  pose proof (Znth_dist_cases i dist' Htemp H23).
                  clear Htemp.
                  rename H31 into icases.
                  rewrite <- H_priq_dist_link in icases; trivial.
                  
                  forward. forward. forward.
                  forward; rewrite upd_Znth_same; trivial.
                  1: entailer!.
                  1,3: repeat rewrite Zlength_map; lia.
                  forward_call ((pointer_val_val priq_ptr), i,
                                (Znth u dist' + cost), priq').

(* Now we must show that the for loop's invariant
   holds if we take another step,
   ie when i increments
                
   We will provide the arrays as they stand now:
   with the i'th cell updated in all three arrays,
   to log a new improved path via u 
 *)
                  1: split; [|red]; ulia.
                  Exists (upd_Znth i prev' u).
                  Exists (upd_Znth i priq' (Znth u dist' + cost)).
                  Exists (upd_Znth i dist' (Znth u dist' + cost)).
                  Exists popped'.
                  repeat rewrite <- upd_Znth_map.
                  entailer!.

                  clear H31 H32 H33 H34 H35 H36
                        H37 H38 H39 H40 H41 H42 H8.

                  remember (find priq (fold_right Z.min (hd 0 priq)
                                                  priq) 0) as u.
                  remember (Zlength priq) as size.
                  rename Heqsize into H8.
                  symmetry in H8.

                  remember (Znth u dist' + elabel g (u, i)) as newcost.
                  fold V in *. simpl id in *.
                  rewrite <- Heqnewcost in *.

                  assert (u <> i) by (intro; subst; lia).
                  
                  split3; [| | split3;
                               [| | split3;
                                    [| | split3;
                                         [| |split3;
                                             [| | split3]]]]]; intros.
                  (* 13 goals, where the 13th is 
                   3 range-based goals together *)
                  --- apply inv_popped_newcost; ulia.
                  --- apply inv_unpopped_newcost with (priq0 := priq'); ulia. 
                  --- now apply inv_unpopped_weak_newcost.
                  --- apply inv_unseen_newcost; ulia.
                  --- apply inv_unseen_weak_newcost; ulia. 
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- rewrite upd_Znth_diff; try lia;
                        intro; subst src; lia.
                  --- assert (H33 := H32).
                      rewrite (vvalid_meaning g) in H33.
                      split; intros; destruct (Z.eq_dec v i).
                      +++ exfalso. subst v.
                          apply H_i_not_popped; trivial.
                      +++ rewrite upd_Znth_diff; try ulia.
                          apply H_priq_popped_link; trivial.
                      +++ exfalso. subst v.
                          rewrite upd_Znth_same in H34; ulia.
                      +++ rewrite upd_Znth_diff in H34; try ulia.
                          apply <- H_priq_popped_link; trivial.
                  --- destruct (Z.eq_dec dst i).
                      1: subst dst; repeat rewrite upd_Znth_same; ulia.
                      repeat rewrite upd_Znth_diff; trivial; try lia.
                      apply H_priq_dist_link; trivial.
                      all: rewrite (vvalid_meaning g) in H32; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- rewrite upd_Znth_Zlength; ulia.
                  --- split3; apply Forall_upd_Znth;  ulia.

               ** (* This is the branch where we didn't
                   make a change to the i'th vertex. *)
                 rename H31 into H_non_improvement.
                 forward. 
                 (* The old arrays are just fine. *)
                 Exists prev' priq' dist' popped'.
                 entailer!.
                 remember (find priq (fold_right Z.min
                                                 (hd 0 priq) priq) 0) as u.
                 remember (Zlength priq) as size.
                 
                 clear H31 H32 H33 H34 H35 H36
                       H37 H38 H39 H40 H41 H42 H8.
                 rename Heqsize into H8.
                 symmetry in H8.
                 
                 assert (elabel g (u, i) < inf). {
                   apply Z.le_lt_trans with (m := Int.max_signed / size);
                     trivial.
                   apply H27.
                   apply (inf_further_restricted g).
                 }
                 split3; [| |split].
                 --- intros. apply inv_unpopped_new_dst
                               with (u0 := u) (i0 := i); trivial.
                 --- intros. destruct (Z.eq_dec dst i).
                     +++ subst dst. lia.
                     +++ apply H_inv_unpopped_weak; lia.
                 --- intros. destruct (Z.eq_dec dst i).
                     2: apply H_inv_unseen; lia.

                     unfold inv_unseen; intros.
                     subst dst.

                     assert (i <= i < size) by lia.
                     destruct (Z.eq_dec m u).
                     2: now apply (H_inv_unseen_weak _ H38) with (m:=m).
                     subst m.
                     rename p2m into p2u.
                     rewrite H34 in H_non_improvement.
                     assert (0 <= u < size) by lia.
                     rewrite path_cost_glue_one_step.
                     destruct H37 as [_ [_ [_ [? _]]]].
                     simpl id in *. ulia.
                 --- intros.
                     assert (i <= dst < size) by lia.
                     apply H_inv_unseen_weak; trivial.
            ++  (* i was not a neighbor of u.
                 We must prove the for loop's invariant holds *)
              forward.
              Exists prev' priq' dist' popped'.
              thaw FR.
              entailer!.
              remember (find priq (fold_right Z.min (hd 0 priq) priq) 0) as u.
              remember (Zlength priq) as size.

              clear H28 H29 H30 H31 H32 H33
                    H34 H35 H36 H37 H38 H39 H8.
              rename Heqsize into H8.
              symmetry in H8.

              rewrite Int.signed_repr in H27.
              2: apply edge_representable.
              split3; [| |split]; intros.
              ** destruct (Z.eq_dec dst i).
                 --- subst dst. 
(* Will need to use the second half of the 
   for loop's invariant.          
   Whatever path worked for i then will 
   continue to work for i now:
   i cannot be improved by going via u 
 *)
                     unfold inv_unpopped; intros.
                     assert (i <= i < size) by lia.
                     destruct (H_inv_unpopped_weak i H31 H29 H30).
                     1: left; trivial.
                     destruct H32 as [? [[? [? [? [? [? ?]]]]]?]].
                     remember (Znth i prev') as mom.

                     assert (Znth mom dist' < inf). {
                       pose proof (edge_cost_pos g (mom, i)).
                       ulia.
                     }
                     
                     right. split3; [| |split3; [| |split3]]; trivial.
                     
                     intros.
                     destruct (@Znth_dist_cases inf mom' dist')
                       as [e | e]; trivial.
                     1: apply (vvalid_meaning g) in H41; ulia.
                     1: { rewrite e.
                          pose proof (edge_cost_pos g (mom', i)).
                          ulia.
                     }
                     
                     destruct (zlt (Znth mom' dist' +
                                    elabel g (mom', i)) inf).
                     2: ulia.
                     
                     destruct (Z.eq_dec mom' u).
                     1: { subst mom'.
                          assert (0 <= Znth u dist'). {
                            apply (sublist.Forall_Znth _ _ u) in H23.
                            simpl in H23. apply H23.
                            lia.
                          }
                          simpl id in *. ulia.
                     }
                     apply H39; trivial.
                 --- apply H_inv_unpopped; lia.
              ** destruct (Z.eq_dec dst i);
                   [| apply H_inv_unpopped_weak]; lia. 
              ** destruct (Z.eq_dec dst i).
                 2: apply H_inv_unseen; lia.
                 subst dst.
                 assert (i <= i < size) by lia.
                 unfold inv_unseen; intros.
                 destruct (Z.eq_dec m u).
                 2: now apply (H_inv_unseen_weak _ H29)
                   with (m:=m).
                 
                 subst m.
                 assert (0 <= Znth u dist'). {
                   apply (sublist.Forall_Znth _ _ u) in H23.
                   apply H23.
                   ulia.
                 }
                 rewrite path_cost_glue_one_step.
                 destruct H34 as [? _].
                 pose proof (path_cost_pos _ _ H34).
                 simpl id in *. ulia.
              ** apply H_inv_unseen_weak; lia.
          -- (* From the for loop's invariant, 
              prove the while loop's invariant. *)
            Intros prev' priq' dist' popped'.
            Exists prev' priq' dist' popped'.
            entailer!.
            remember (find priq (fold_right Z.min (hd 0 priq) priq) 0)
              as u.
            unfold dijkstra_correct.
            split3; [auto | apply H16 | apply H18];
              try rewrite <- (vvalid_meaning g); trivial.
           
        * (* After breaking from the while loop,
           prove break's postcondition *)
          forward.
          unfold dijk_forloop_break_inv.
          Exists prev dist popped hc.
          assert (heap_capacity hc = heap_capacity h) by lia.
          assert_PROP (0 <= heap_size hc <= Int.max_unsigned). {
            unfold valid_pq.
            Intros arr junk lookup l_contents.
            entailer!. 
            unfold heap_size. 
            pose proof (Zlength_nonneg junk). 
            split; [apply Zlength_nonneg|]. 
            apply Z.le_trans with (m := heap_capacity hc).
            1: rewrite <- H17, Zlength_app; lia.
            lia.
          }
          rewrite H13. entailer!.
          clear -H5 H14.
          rewrite Int.unsigned_repr in H5 by trivial.
          unfold heap_size in *.
          pose proof (Zlength_nonneg (heap_items hc)).
          lia.
          
          admit.
          (* HELP is this the coercion you proved? *)
      + (* from the break's postcon, prove the overall postcon *)
        unfold dijk_forloop_break_inv.
        Intros prev dist popped hc.
        freeze FR := (valid_pq _ _)
                       (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (data_at _ _ _ _)
                       (SpaceAdjMatGraph _ _ _ _ _)
                       (free_tok (pointer_val_val keys_pv) _).
        (* TODO: add freeN... *)
        admit.

        (*freeze FR := (data_at _ _ _ (pointer_val_val prev_ptr))
                       (data_at _ _ _ (pointer_val_val dist_ptr))
                       (SpaceAdjMatGraph _ _ _ _ _).
        forward_call (Tsh, priq_ptr, size, priq).
        entailer!.
        thaw FR.
        forward.
        Exists prev dist popped. entailer!.
        intros. destruct (H2 _ H9) as [? _]; trivial.
         *)
  Admitted.

End DijkstraProof.
