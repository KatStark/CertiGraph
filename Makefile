COMPCERT_DIR = "../CompCert"
VST_DIR = "../VST"
CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc -w -overriding-logical-loadpath
COQDEP=$(COQBIN)coqdep

DIRS = lib msl_ext msl_application graph heap_model_direct
INCLUDE_COMPCERT = -Q $(COMPCERT_DIR) compcert
INCLUDE_VST = -Q $(VST_DIR) VST
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -Q $(d) RamifyCoq.$(d)) -Q "." RamifyCoq
NORMAL_FLAG = $(INCLUDE_RAMIFYCOQ) $(INCLUDE_VST) $(INCLUDE_COMPCERT)
CLIGHT_FLAG = $(INCLUDE_COMPCERT) $(INCLUDE_RAMIFYCOQ)

LIB_FILES = \
  Coqlib.v Equivalence_ext.v List_Func_ext.v Ensembles_ext.v List_ext.v EnumEnsembles.v Relation_ext.v relation_list.v EquivDec_ext.v Morphisms_ext.v

MSL_EXT_FILES = \
  log_normalize.v iter_sepcon.v ramification_lemmas.v abs_addr.v seplog.v \
  ramify_tactics.v msl_ext.v sepalg.v overlapping.v precise.v alg_seplog.v \
  overlapping_direct.v precise_direct.v alg_seplog_direct.v

MSL_APPLICATION_FILES = \
  Graph.v Graph_Mark.v GraphBi.v GraphBi_Mark.v DagBi_Mark.v Graph_Copy.v GraphBi_Copy.v GList.v GList_UnionFind.v ArrayGraph.v UnionFindGraph.v

VERIC_EXT_FILES = \
  res_predicates.v seplog.v SeparationLogic.v

FLOYD_EXT_FILES = closed_lemmas.v share.v
  # MapstoSL.v DataatSL.v semax_ram_lemmas.v semax_ram_tac.v exists_trick.v closed_lemmas.v ramification.v share.v

HEAP_MODEL_DIRECT_FILES = \
  SeparationAlgebra.v mapsto.v SeparationLogic.v

GRAPH_FILES = \
  graph_model.v path_lemmas.v graph_gen.v graph_relation.v reachable_computable.v find_not_in.v reachable_ind.v subgraph2.v \
  spanning_tree.v dag.v marked_graph.v weak_mark_lemmas.v dual_graph.v graph_morphism.v \
  local_graph_copy.v tree_model.v list_model.v BiGraph.v MathGraph.v FiniteGraph.v GraphAsList.v LstGraph.v UnionFind.v graph_isomorphism.v\
  undirected_graph.v undirected_uf_lemmas.v

DATA_STRUCTURE_FILES = \
  spatial_graph_unaligned_bi_VST.v spatial_graph_dispose_bi.v

SAMPLE_MARK_FILES = \
  env_mark_bi.v verif_mark_bi.v env_garbage_collector.v env_dispose_bi.v verif_dispose_bi.v verif_mark_bi_dag.v env_copy_bi.v spatial_graph_bi_mark.v spatial_graph_bi_copy.v \
  unionfind.v env_unionfind.v spatial_graph_glist.v uf_arr_specs.v verif_unionfind.v verif_unionfind_slim.v verif_unionfind_rank.v \
  unionfind_iter.v env_unionfind_iter.v verif_summatrix.v spatial_graph_uf_iter.v verif_unionfind_iter.v verif_unionfind_iter_rank.v \
  unionfind_arr.v env_unionfind_arr.v spatial_array_graph.v verif_unionfind_arr.v \
  verif_copy_bi.v binary_heap_model.v binary_heap_Zmodel.v binary_heap.v env_binary_heap.v verif_binary_heap.v binary_heap_pro.v env_binary_heap_pro.v

HIP_FILES = \
  hip_graphmark.v hip_graphmark_proofs.v spanningtree.v

# Using "clightgen -DCOMPCERT -normalize -isystem . gc.c" to generate gc.v

CERTIGC_FILES = \
  gc.v data_at_test.v spatial_gcgraph.v verif_conversion.v verif_Is_from.v \
  gc_spec.v verif_create_space.v verif_create_heap.v verif_make_tinfo.v env_graph_gc.v verif_Is_block.v verif_garbage_collect.v verif_resume.v \
  GCGraph.v verif_forward.v verif_do_scan.v verif_forward_roots.v verif_do_generation.v gc_correct.v

KRUSKAL_FILES = \
  WeightedEdgeListGraph.v \
  kruskal_edgelist.v env_kruskal_edgelist.v spatial_wedgearray_graph.v kruskal_uf_specs.v \
  verif_kruskal_edgelist.v

DIJKSTRA_FILES = \
  dijkstra.v \
  DijkstraArrayGraph.v \
  env_dijkstra_arr.v spatial_dijkstra_array_graph.v \
  dijkstra_constants.v path_cost.v dijkstra_spec.v verif_dijkstra.v

PRIQ_FILES = \
  priq_arr.v priq_arr_specs.v priq_arr_utils.v verif_priq_arr.v 


CLIGHT_FILES = sample_mark/mark_bi.v sample_mark/garbage_collector.v sample_mark/dispose_bi.v sample_mark/copy_bi.v sample_mark/summatrix.v

C_FILES = $(CLIGHT_FILES:%.v=%.c)

NORMAL_FILES = \
  $(MSL_EXT_FILES:%.v=msl_ext/%.v) \
  $(MSL_APPLICATION_FILES:%.v=msl_application/%.v) \
  $(FLOYD_EXT_FILES:%.v=floyd_ext/%.v) \
  $(DATA_STRUCTURE_FILES:%.v=data_structure/%.v) \
  $(SAMPLE_MARK_FILES:%.v=sample_mark/%.v) \
  $(SAMPLE_EDGE_WEIGHT_FILES:%.v=sample_edge_weight/%.v) \
  $(GRAPH_FILES:%.v=graph/%.v) \
  $(LIB_FILES:%.v=lib/%.v) \
  $(HEAP_MODEL_DIRECT_FILES:%.v=heap_model_direct/%.v) \
  $(CERTIGC_FILES:%.v=CertiGC/%.v) \
  $(KRUSKAL_FILES:%.v=kruskal/%.v) \
  $(DIJKSTRA_FILES:%.v=dijkstra/%.v) \
  $(PRIQ_FILES:%.v=priq/%.v)

$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

$(CLIGHT_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(CLIGHT_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo) \
  $(CLIGHT_FILES:%.v=%.vo)

# A minimal list of files that need to built within VST for our build to work.
# Please add to this as needed.
VST_CRITICAL_FILES = \
  progs/conclib.v floyd/reassoc_seq.v compcert/cfrontend/ClightBigstep.v msl/msl_direct.v msl/alg_seplog_direct.v

.PHONY: vstandme7
vstandme7:
	cd $(VST_DIR) && make $(VST_CRITICAL_FILES:%.v=%.vo) -j7 && cd - && make -j7

.PHONY: vstandme3
vstandme3:
	cd $(VST_DIR) && make $(VST_CRITICAL_FILES:%.v=%.vo) -j3 && cd - && make -j3

.depend depend:
	@echo 'coqdep ... >.depend'
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend
	@$(COQDEP) $(CLIGHT_FLAG) $(CLIGHT_FILES) >> .depend

clean:
	@rm */*.vo */*.glob */.*.aux .depend

.DEFAULT_GOAL := all

include .depend
