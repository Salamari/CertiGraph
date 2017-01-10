COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = lib msl_ext msl_application graph heap_model_direct
INCLUDE_COMPCERT = -R $(COMPCERT_DIR) compcert
INCLUDE_VST = -R $(VST_DIR) VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -R $(d) RamifyCoq.$(d)) -R "." RamifyCoq
NORMAL_FLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_RAMIFYCOQ)

LIB_FILES = \
  Coqlib.v Equivalence_ext.v List_Func_ext.v Ensembles_ext.v List_ext.v EnumEnsembles.v Relation_ext.v relation_list.v EquivDec_ext.v Morphisms_ext.v

MSL_EXT_FILES = \
  abs_addr.v seplog.v log_normalize.v ramify_tactics.v msl_ext.v iter_sepcon.v \
  sepalg.v ramification_lemmas.v \
  overlapping.v precise.v alg_seplog.v \
  overlapping_direct.v precise_direct.v alg_seplog_direct.v

MSL_APPLICATION_FILES = \
  Graph.v Graph_Mark.v GraphBi.v GraphBi_Mark.v DagBi_Mark.v Graph_Copy.v GraphBi_Copy.v GList.v

VERIC_EXT_FILES = \
  res_predicates.v seplog.v SeparationLogic.v

FLOYD_EXT_FILES = \
  MapstoSL.v DataatSL.v semax_ram_lemmas.v semax_ram_tac.v exists_trick.v closed_lemmas.v comparable.v ramification.v share.v

HEAP_MODEL_DIRECT_FILES = \
  SeparationAlgebra.v mapsto.v SeparationLogic.v

GRAPH_FILES = \
  graph_model.v path_lemmas.v graph_gen.v graph_relation.v reachable_computable.v find_not_in.v reachable_ind.v subgraph2.v \
  spanning_tree.v dag.v marked_graph.v weak_mark_lemmas.v dual_graph.v graph_morphism.v \
  local_graph_copy.v tree_model.v list_model.v BiGraph.v MathGraph.v FiniteGraph.v GraphAsList.v LstGraph.v

DATA_STRUCTURE_FILES = \
  spatial_graph_unaligned_bi_VST.v spatial_graph_dispose_bi.v

SAMPLE_MARK_FILES = \
  env_mark_bi.v verif_mark_bi.v env_garbage_collector.v env_dispose_bi.v verif_dispose_bi.v verif_mark_bi_dag.v env_copy_bi.v verif_copy_bi.v spatial_graph_bi_mark.v spatial_graph_bi_copy.v unionfind.v env_unionfind.v spatial_graph_glist.v

HIP_FILES = \
  hip_graphmark.v hip_graphmark_proofs.v spanningtree.v

CERTIGC_FILES = \
  gc.v data_at_test.v
  
CLIGHT_FILES = sample_mark/mark_bi.v sample_mark/garbage_collector.v sample_mark/dispose_bi.v sample_mark/copy_bi.v

C_FILES = $(CLIGHT_FILES:%.v=%.c)

NORMAL_FILES = \
  $(MSL_EXT_FILES:%.v=msl_ext/%.v) \
  $(MSL_APPLICATION_FILES:%.v=msl_application/%.v) \
  $(VERIC_EXT_FILES:%.v=veric_ext/%.v) \
  $(FLOYD_EXT_FILES:%.v=floyd_ext/%.v) \
  $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.v) \
  $(DATA_STRUCTURE_FILES:%.v=data_structure/%.v) \
  $(SAMPLE_MARK_FILES:%.v=sample_mark/%.v) \
  $(HIP_FILES:%.v=hip/%.v) \
  $(GRAPH_FILES:%.v=graph/%.v) \
  $(CERTIGC_FILES:%.v=CertiGC/%.v) \
  $(LIB_FILES:%.v=lib/%.v)

$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(CLIGHT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CLIGHT_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo) \
  $(CLIGHT_FILES:%.v=%.vo)

depend:
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend
	@$(COQDEP) $(CLIGHT_FLAG) $(CLIGHT_FILES) >> .depend

clean:
	@rm */*.vo */*.glob */.*.aux

.DEFAULT_GOAL := all

include .depend
