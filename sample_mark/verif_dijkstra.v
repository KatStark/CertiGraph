Require Import Coq.ZArith.ZArith.
Require Export Coq.Program.Basics.
Require Import RamifyCoq.graph.graph_model.
Require Import RamifyCoq.graph.path_lemmas.
Require Import RamifyCoq.sample_mark.dijkstra.
Require Import RamifyCoq.msl_application.DijkstraGraph.
Require Import Coq.Lists.List.
Import ListNotations.

Definition inf := Integers.Int.max_signed.

Coercion pg_lg: LabeledGraph >-> PreGraph.
Coercion lg_gg: GeneralGraph >-> LabeledGraph.

Definition vert_rep (g : Graph) (v : LV) : list Z :=
  let edges := v.(edges) in
  map (fun x => match x with Some x => (Z.of_nat x) | None => inf end) edges.

Fixpoint graph_rep_helper (g : Graph) (v : LV) (acc : list (list Z)) : list (list Z) :=
  let neighbors := choose v.(edges) in
  let myrep := vert_rep g v in
  fold_left (graph_rep_helper g) neighbors [myrep].

(* Spatial representation: from Graph to list (list Z) *)
Definition graph_rep (g : Graph) : list (list Z) :=
  let source := (glabel g).(src) in
  graph_rep_helper g source [].

  


(* First, refer to spatial gc graph to figure out a spatial representation *)

(* Spec:  *)
(* 	\exists mypath. path_ends g mypath src dst, *)
(* 		\forall path. path_ends g path src dest ->  *)
(* 			path_cost path <= past_cost mypath -> *)
(* 				mypath = path *)


                                           
