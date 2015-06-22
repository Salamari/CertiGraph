Require Export RamifyCoq.msl_ext.seplog.
Require Export RamifyCoq.msl_ext.log_normalize.
Require Export RamifyCoq.msl_ext.alg_seplog.
Require Export RamifyCoq.veric_ext.seplog.
Require Import VST.veric.SeparationLogic.

Instance PSLveric: PreciseSepLog mpred := algPreciseSepLog compcert_rmaps.RML.R.rmap.
Instance OSLveric: OverlapSepLog mpred := algOverlapSepLog compcert_rmaps.RML.R.rmap.
Instance DSLveric: DisjointedSepLog mpred := algDisjointedSepLog compcert_rmaps.RML.R.rmap.
Instance COSLveric: CorableOverlapSepLog mpred := algCorableOverlapSepLog compcert_rmaps.RML.R.rmap.

Instance LiftPreciseSepLog' T {ND: NatDed T}{SL: SepLog T}{PSL: PreciseSepLog T} :
           PreciseSepLog (LiftEnviron T) := LiftPreciseSepLog _ _.
Instance LiftOverlapSepLog' T {ND: NatDed T}{SL: SepLog T}{PSL: PreciseSepLog T}{OSL: OverlapSepLog T} :
           OverlapSepLog (LiftEnviron T) := LiftOverlapSepLog _ _.
Instance LiftDisjointedSepLog' T {ND: NatDed T}{SL: SepLog T}{PSL: PreciseSepLog T}{OSL: OverlapSepLog T}{DSL: DisjointedSepLog T} :
           DisjointedSepLog (LiftEnviron T) := LiftDisjointedSepLog _ _.

Global Opaque PSLveric OSLveric DSLveric COSLveric.

Local Open Scope logic.

Lemma exp_mapsto_precise: forall sh t p, precise (EX v: val, mapsto sh t p v).
Proof. exact exp_mapsto_precise. Qed.

Lemma disj_mapsto_: forall sh env t1 t2 p1 p2,
  ~ pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
  disjointed (EX v1: val, mapsto sh t1 p1 v1) (EX v2: val, mapsto sh t2 p2 v2).
Proof. exact disj_mapsto_. Qed.

Lemma mapsto_conflict: forall sh env t1 t2 p1 p2 v1 v2,
  pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
  mapsto sh t1 p1 v1 * mapsto sh t2 p2 v2 |-- FF.
Proof. exact mapsto_conflict. Qed.

Lemma memory_block_precise: forall sh p n, precise (memory_block sh n p).
Proof. exact memory_block_precise. Qed.

Lemma disj_memory_block: forall sh p1 n1 p2 n2, ~ pointer_range_overlap p1 n1 p2 n2 -> disjointed (memory_block sh n1 p1) (memory_block sh n2 p2).
Proof. exact disj_memory_block. Qed.

Lemma memory_block_conflict: forall sh p1 n1 p2 n2, pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 * memory_block sh n2 p2 |-- FF.
Proof. exact memory_block_conflict. Qed.



