Require Import Coq.ZArith.BinInt.
Require Import Coq.Classes.EquivDec.
Require Import Coq.micromega.Lia.

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.

Require Import CertiGraph.lib.List_ext.
Require Import CertiGraph.graph.graph_model.
Require Export CertiGraph.graph.FiniteGraph.
Require Import CertiGraph.graph.path_lemmas.

Section Mathematical_AdjMat_Model.

  Coercion pg_lg: LabeledGraph >-> PreGraph.
  Coercion lg_gg: GeneralGraph >-> LabeledGraph. 

  Local Open Scope Z_scope.

  (* Most of the types are constrained because 
     we want easy AdjMat representation. *)
  Definition V : Type := Z.
  Definition E : Type := V * V.
  Definition DV: Type := unit.
  Definition DE : Type := Z.
  Definition DG: Type := unit.

  Instance V_EqDec : EqDec V eq. Proof. hnf. intros. apply Z.eq_dec. Defined.
  Instance E_EqDec: EqDec E eq.
  Proof. apply (prod_eqdec V_EqDec V_EqDec). Defined.

  Context {size : Z}. 
  Context {inf : Z}.
  (* The instantiator will have to supply a max number of vertices
     and a special "infinity" value to indicate unreachability 
   *)
  
  (* This is the basic LabeledGraph for all our AdjMat representations. *)
  Definition AdjMatLG := (@LabeledGraph V E _ _ DV DE DG).
  (* We need some further restrictions, which we will place 
     in the GeneralGraph's soundness condition.  
   *)

  (* Each field of the class is a "plugin"
     which further restricts various aspects of the graph
   *)
  Class SoundAdjMat (g: AdjMatLG) :=
    {
    sr: (* size_representable *)
      0 < size <= Int.max_signed;
    ir: (* inf_representable *)
      Int.min_signed <= inf <= Int.max_signed; 
    vm: (* vvalid_meaning *)
      forall v, vvalid g v <-> 0 <= v < size;
    em: (* evalid_meaning *)
      forall e, evalid g e <-> 
                Int.min_signed <= elabel g e <= Int.max_signed /\
                elabel g e <> inf;
    ese: (* evalid_strong_evalid *)
      forall e, evalid g e -> strong_evalid g e;
    iew: (* invalid_edge_weight *)
      forall e, ~ evalid g e <-> elabel g e = inf;
    esf: (* edge_src_fst *)
      forall e, src g e = fst e;
    eds: (* edge_dst_snd *)
      forall e, dst g e = snd e;
    fin:
      FiniteGraph g
    }.
  
  (* Academic example of how to instantiate the above *)
  Definition AdjMatGG := (GeneralGraph V E DV DE DG (fun g => SoundAdjMat g)).
  (* In reality, clients may want to:
     1. create a new soundness condition where one of the 
        plugins is "SoundAdjMat" above
     2. add further program-specific restrictions in 
        other plugins
     3. use this new accreted soundness condition to 
        build their GeneralGraph, as shown above.
   *)

  
  (* Getters for the plugins *)

  Definition size_representable (g: AdjMatGG) :=
    @sr g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition inf_representable (g: AdjMatGG) :=
    @ir g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition vvalid_meaning (g: AdjMatGG) :=
    @vm g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_meaning (g: AdjMatGG) :=
    @em g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition evalid_strong_evalid (g: AdjMatGG) :=
    @ese g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition invalid_edge_weight (g: AdjMatGG) :=
    @iew g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_src_fst (g: AdjMatGG) :=
    @esf g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition edge_dst_snd (g: AdjMatGG) :=
    @eds g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  Definition finGraph (g: AdjMatGG) :=
    @fin g ((@sound_gg _ _ _ _ _ _ _ _ g)).

  
  (* Some lemmas from the above soundness plugins *)
  
  Lemma valid_path_app_cons:
    forall (g: AdjMatGG) src links2u u i,
      valid_path g (src, links2u) ->
      pfoot g (src, links2u) = u ->
      strong_evalid g (u,i) ->
      valid_path g (src, links2u +:: (u,i)).
  Proof.
    intros.
    apply valid_path_app.
    split; [assumption|].
    simpl; split; trivial.
    destruct H1.
    rewrite (edge_src_fst g); simpl; assumption.
  Qed.
  
  Lemma path_ends_app_cons:
    forall (g: AdjMatGG) a b c a' a2b,
      a = a' ->
      path_ends g (a, a2b) a b ->
      path_ends g (a, a2b +:: (b, c)) a' c.
  Proof.
    split; trivial.
    rewrite pfoot_last.
    rewrite (edge_dst_snd g); trivial.
  Qed.
  
  Lemma step_in_range:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (fst x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [? _]].
    rewrite <- (edge_src_fst g); trivial.
  Qed.
  
  Lemma step_in_range2:
    forall (g: AdjMatGG) x x0,
      valid_path g x ->
      In x0 (snd x) ->
      vvalid g (snd x0).
  Proof.
    intros.
    rewrite (surjective_pairing x) in H.
    pose proof (valid_path_strong_evalid g _ _ _ H H0).
    destruct H1 as [? [_ ?]].
    rewrite <- (edge_dst_snd g); trivial.
  Qed.

  Instance Finite_AdjMatGG (g: AdjMatGG): FiniteGraph g.
  Proof. apply (finGraph g). Qed.

  Lemma UAdjMatGG_VList:
    forall (g: AdjMatGG), Permutation (VList g) (nat_inc_list (Z.to_nat size)).
  Proof.
    intros. apply NoDup_Permutation. apply NoDup_VList. apply nat_inc_list_NoDup.
    intros. rewrite VList_vvalid.
    rewrite (vvalid_meaning g).
    rewrite nat_inc_list_in_iff. rewrite Z_to_nat_max.
    destruct (Z.lt_trichotomy size 0). rewrite Z.max_r by
        lia. split; intros; lia.
    destruct H. rewrite H. unfold Z.max; simpl. split; lia.
    rewrite Z.max_l by lia. split; auto.
  Qed.
  
  Lemma evalid_form: (*useful for a = (u,v) etc*)
    forall (g: AdjMatGG) e, evalid g e -> e = (src g e, dst g e).
  Proof.
    intros.
    rewrite (edge_src_fst g).
    rewrite (edge_dst_snd g).
    destruct e; simpl; auto.
  Qed.
  
  Lemma evalid_vvalid:
    forall (g: AdjMatGG) u v, evalid g (u,v) -> vvalid g u /\ vvalid g v.
  Proof.
    intros. apply (evalid_strong_evalid g) in H. destruct H.
    rewrite (edge_src_fst g), (edge_dst_snd g) in H0 by auto.
    simpl in H0; auto.
  Qed.

  Lemma weight_representable:
    forall (g: AdjMatGG) e, Int.min_signed <= elabel g e <= Int.max_signed.
  Proof.
    intros. destruct (evalid_dec g e).
    apply (evalid_meaning g e); auto.
    rewrite (invalid_edge_weight g) in n.
    replace (elabel g e) with inf in * by trivial.
    pose proof (inf_representable g). trivial. 
  Qed.
  
End Mathematical_AdjMat_Model.
