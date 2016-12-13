Require Import RamifyCoq.lib.EquivDec_ext.
Require Import RamifyCoq.msl_ext.abs_addr.
Require Import RamifyCoq.msl_ext.seplog.
Require Import RamifyCoq.msl_application.Graph.
Require Import RamifyCoq.msl_application.GList.
Require Import VST.veric.SeparationLogic.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.msl_ext.alg_seplog.
Require Import RamifyCoq.sample_mark.env_unionfind.
Require Import RamifyCoq.veric_ext.SeparationLogic.
Require Import RamifyCoq.floyd_ext.DataatSL.
Require Import RamifyCoq.floyd_ext.share.

Local Open Scope logic.

Section pSGG_VST.

Instance PointerVal_EqDec: EquivDec.EqDec pointer_val eq.
  hnf; intros.
  apply PV_eq_dec.
Defined.

Instance PointerValE_EqDec: EquivDec.EqDec (pointer_val * unit) eq.
  hnf; intros. destruct x, y. 
  destruct u, u0. destruct (PV_eq_dec p p0); [left | right]; congruence.
Defined.

Instance SGBA_VST: SpatialGraphBasicAssum pointer_val (pointer_val * unit).
  refine (Build_SpatialGraphBasicAssum pointer_val (pointer_val * unit) _ _).
Defined.

End pSGG_VST.

Instance pSGG_VST: pSpatialGraph_GList.
  refine (Build_pSpatialGraph_GList pointer_val NullPointer mpred SGBA_VST).
Defined.

Definition vgamma2cdata (rpa : nat * addr) : reptype node_type :=
  match rpa with
  | (r, pa) => (Vint (Int.repr (Z.of_nat r)), pointer_val_val pa)
  end.

Section sSGG_VST.

  Definition binode (sh: share) (p: addr) (rpa: nat * addr): mpred :=
    data_at sh node_type (vgamma2cdata rpa) (pointer_val_val p).

  Instance SGP_VST (sh: share) : SpatialGraphPred addr (addr * unit) (nat * addr) unit pred.
  refine (Build_SpatialGraphPred _ _ _ _ _ (binode sh) (fun _ _ => emp)).
  Defined.

  Instance MSLstandard sh : MapstoSepLog (AAV (SGP_VST sh)) (binode sh).
  Proof.
    intros. apply mkMapstoSepLog. intros.
    apply derives_precise with (memory_block sh (sizeof node_type) (pointer_val_val p)); [| apply memory_block_precise].
    apply exp_left; intros [? ?]. unfold binode. apply data_at_memory_block.
  Defined.

  Lemma sepcon_unique_vertex_at sh: writable_share sh -> sepcon_unique2 (@vertex_at _ _ _ _ _ (SGP_VST sh)).
  Proof.
    intros. hnf; intros. simpl.
    destruct y1 as [? ?], y2 as [? ?].
    unfold binode.
    rewrite data_at_isptr.
    normalize.
    apply data_at_conflict.
    + apply sepalg.nonidentity_nonunit.
      apply readable_nonidentity, writable_readable.
      auto.
    + change (sizeof node_type) with 8.
      apply pointer_range_overlap_refl; auto; omega.
  Qed.

Instance SGA_VST (sh: share) : SpatialGraphAssum (SGP_VST sh).
  refine (Build_SpatialGraphAssum _ _ _ _ _ _ _ _ _ _ _).
Defined.

Instance SGAvs_VST (sh: wshare): SpatialGraphAssum_vs (SGP_VST sh).
  apply sepcon_unique_vertex_at; auto.
Defined.

Instance SGAvn_VST (sh: wshare): SpatialGraphAssum_vn (SGP_VST sh) NullPointer.
  intros [? ?].
  simpl.
  unfold binode.
  rewrite data_at_isptr.
  normalize.
Defined.

End sSGG_VST.

Hint Extern 10 (@sepcon_unique2 _ _ _ _ _ (@vertex_at _ _ _ _ _ _)) => apply sepcon_unique_vertex_at; auto.

Instance sSGG_VST (sh: wshare): @sSpatialGraph_GList pSGG_VST nat unit.
  refine (Build_sSpatialGraph_GList pSGG_VST _ _ (SGP_VST sh) (SGA_VST sh) (SGAvs_VST sh) (SGAvn_VST sh)).
Defined.

Global Opaque pSGG_VST sSGG_VST.
