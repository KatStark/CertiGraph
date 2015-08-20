Require Import Coq.Sets.Ensembles.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require RamifyCoq.graph.marked_graph. Import RamifyCoq.graph.marked_graph.MarkGraph.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.graph.subgraph2.
Require Import RamifyCoq.graph.reachable_ind.
Require Import RamifyCoq.graph.spanning_tree.
Require Import RamifyCoq.data_structure.general_spatial_graph.
Require Import RamifyCoq.data_structure.spatial_graph_bi.

Instance MGS: MarkGraphSetting bool.
  apply (Build_MarkGraphSetting bool
          (eq true)
          (fun _ => true)
          (fun _ => false));
  intros.
  + destruct x; [left | right]; congruence.
  + auto.
  + congruence.
Defined.

Section SPATIAL_GRAPH_DISPOSE_BI.
  
  Context {pSGG_Bi: pSpatialGraph_Graph_Bi}.
  Context {sSGG_Bi: sSpatialGraph_Graph_Bi}.

  Local Open Scope logic.

  (* Existing Instances SGP SGA. *)

  Lemma graph_ramify_aux1': forall (g: Graph) (l: addr) (P : addr -> Prop) {V_DEC: Decidable (vvalid g l)},
      unmarked g l ->
      Included (reachable g l) P -> Included P (vvalid g) ->
      (vertices_at g P : pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g l)) -*
       (EX g': Graph, !! spanning_tree g l g' && vertices_at g' P)).
  Proof.
    intros. apply existential_partialgraph_update_prime; auto.
    + intro. apply RFG_reachable_decicable'. apply RGF. auto.
    + intros. apply H0. auto.
    + intros g' y ? ?. apply H1 in H3. unfold In in H3.
      rewrite <- (spanning_tree_vvalid g l g'); auto.
      apply Graph_reachable_by_dec; auto.
    + intros g' ?. destruct H2 as [[? ?] [? ?]]. specialize (H5 H).
      destruct H5. apply Graph_partialgraph_vi_spec.
      - apply si_stronger_partialgraph_simple with (fun n : addr => ~ g |= l ~o~> n satisfying (unmarked g)); auto.
        intro v. unfold In. intro. destruct H7.
        intro. apply H8. apply reachable_by_is_reachable in H9. auto.
      - intros. specialize (H3 v).
        assert (~ g |= l ~o~> v satisfying (unmarked g)). {
          intro. destruct H10. apply H12.
          apply reachable_by_is_reachable in H11. auto.
        } specialize (H3 H11). simpl in H3.
        destruct (vlabel g v), (vlabel g' v); try tauto.
        symmetry. tauto.
  Qed.

  Lemma graph_ramify_aux1_left: forall (g: Graph) x d l r,
      vvalid g x -> unmarked g l ->
      vgamma g x = (d, l, r) ->
      (graph x g: pred) |-- graph l g *
      ((EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g l)) -*
       (EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g x))).
  Proof.
    intros. apply graph_ramify_aux1'; auto.
    + apply weak_valid_vvalid_dec. apply (gamma_left_weak_valid g x d l r); auto.
    + intros v. unfold In. intro. apply edge_reachable with l; auto. split; [| split]; auto.
      - apply reachable_head_valid in H2; auto.
      - rewrite (gamma_step g x d l r); auto.
    + intro v. unfold In. intro. apply reachable_foot_valid in H2. auto.
  Qed.

  (* Lemma graph_ramify_aux1_right: forall (g: Graph) x d l r, *)
  (*     vvalid g x -> unmarked g r -> *)
  (*     vgamma g x = (d, l, r) -> *)
  (*     (graph x g: pred) |-- graph l g * *)
  (*     ((EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g l)) -* *)
  (*      (EX g': Graph, !! spanning_tree g l g' && vertices_at g' (reachable g x))). *)
  
End SPATIAL_GRAPH_DISPOSE_BI.
