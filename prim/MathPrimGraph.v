Require Import CertiGraph.prim.prim_env.
Require Export CertiGraph.graph.MathUAdjMatGraph.

Local Open Scope logic.
Local Open Scope Z_scope.

Section MathPrimGraph.

  Context {size : Z}.
  Context {inf : Z}.

  (* Here is the LabeledGraph *)
  Definition PrimLG := UAdjMatLG.

  (* The soundness condition *)
  Class SoundPrim (g: PrimLG) :=
    {
    basic:
      (* first, we can take UAdjMat's soundness wholesale *)
      @SoundUAdjMat size inf g;
    
    veb:
      (* from the AdjMat soundness above we 
         already know e is representable, 
         but for Prim we need a further constraint. 
       *)
      forall e, evalid g e <-> elabel g e < inf;
    
    ifr: (* inf is further restricted *)
      0 <= inf < Int.max_signed                          
    }.

  (* And here is the GeneralGraph that we will use *)
  Definition PrimGG := (GeneralGraph V E DV DE DG (fun g => SoundPrim g)).
  
  (* A handy coercion: *)
  Identity Coercion AdjMatLG_DijkLG: PrimLG >-> UAdjMatLG.
  
  (* We can drag out the soundness condition *)
  Definition SoundPrim_PrimGG (g: PrimGG) := (@sound_gg _ _ _ _ _ _ _ _ g).

  (* We can always drag out SoundAdjMat *)
  Definition SoundUAdjMat_PrimGG (g: PrimGG) :=
    @basic g (SoundPrim_PrimGG g).

  (* A PrimGG can be weakened into a UAdjMatGG *)
  Definition UAdjMatGG_PrimGG (g: PrimGG) : UAdjMatGG :=
    Build_GeneralGraph DV DE DG SoundUAdjMat g (SoundUAdjMat_PrimGG g).

  Coercion UAdjMatGG_PrimGG: PrimGG >-> UAdjMatGG.

  (* Great! So now when we want to access a UAdjMat or AdjMat
     plugin, we can simply use the UAdjMat/AdjMat getter 
     and pass it a PrimGG. The coercion will be seamless. 
   *)

  (* For the four Prim-specific plugins, we create getters: *)
  Definition valid_edge_bounds (g: PrimGG) :=
    @veb g (SoundPrim_PrimGG g).

  Definition inf_further_restricted (g: PrimGG) :=
    @ifr g (SoundPrim_PrimGG g).
  
  (* We often need finiteness so we drag it up *)
  Instance Finite_PrimGG (g: PrimGG): FiniteGraph g.
  Proof. apply (finGraph g). Qed.

  Context {inf_bound: 0 <= inf < Int.max_signed}.
  Context {size_bound: 0 < size <= Int.max_signed}.

  Instance SoundPrim_edgeless:
    SoundPrim (@edgeless_lgraph size inf).
  Proof.
    constructor; trivial.
    - apply @SoundUAdjMat_edgeless; trivial. rep_lia.
    - split; intros; [inversion H | simpl in H; lia].
  Qed.

  (* Should really find a cleverer way than duplication... *)
  
  (*  Definition edgeless_graph: PrimGG :=
      @Build_GeneralGraph V E V_EqDec E_EqDec unit Z unit
                        SoundPrim
                        edgeless_lgraph
                        SoundPrim_edgeless.
   *)

  (* Or else you end up in this mad route of more duplication. *)
  (*
    Lemma edgeless_partial_lgraph:
    forall (g: PrimGG), is_partial_lgraph edgeless_graph g.
  Proof.
    intros. split3.
    - unfold is_partial_graph.
      split3; [| |split]; try inversion 1.
      apply (vvalid_meaning g); trivial.
    - unfold preserve_vlabel; intros.
      destruct vlabel; destruct vlabel. auto.
    - unfold preserve_elabel.
      inversion 1.
  Qed.
   *)
  
  (* And now some lemmas from the above *)
  
  Lemma evalid_inf_iff:
    forall (g: PrimGG) e, evalid g e <-> elabel g e < inf.
  Proof. apply valid_edge_bounds. Qed.

  Lemma weight_inf_bound:
    forall (g: PrimGG) e, elabel g e <= inf.
  Proof.
    intros. destruct (evalid_dec g e).
    apply Z.lt_le_incl. 
    apply (valid_edge_bounds g); trivial.
    apply (invalid_edge_weight g) in n. 
    replace (elabel g e) with inf in * by trivial. lia.
  Qed.

  Corollary eformat_adj_elabel:
    forall (g: PrimGG) u v,
      adjacent g u v <-> elabel g (eformat (u,v)) < inf.
  Proof.
    intros. rewrite (eformat_adj g).
    apply evalid_inf_iff.
  Qed.
  
  Lemma exists_labeled_spanning_uforest_pre:
    forall (l: list E) (g: PrimGG),
      Permutation l (EList g) ->
      exists (t: PrimGG), labeled_spanning_uforest t g.
  Proof. Admitted.
  (*
    induction l; intros.
    - (*nil case*)
      exists edgeless_graph.
      (* Hm, how do I state, above, that edgeless_graph
         from MathUAdjMat is actually a bona-fide PrimGG? 
         I have already showed that it satisfies 
         PrimGG's soundness condition...
       *)
      split. split.
      apply edgeless_partial_lgraph.
      split. apply uforest'_edgeless_graph.
      unfold spanning; intros. destruct (V_EqDec u v).
      hnf in e. subst v. split; intros; apply connected_refl.
      apply connected_vvalid in H0. rewrite (vvalid_meaning g) in *. apply H0.
      apply connected_vvalid in H0. rewrite (vvalid_meaning g) in *. apply H0.
      unfold complement, equiv in c. split; intros. exfalso. destruct H0.
      unfold connected_by_path in H0. destruct H0. destruct H1. destruct x. inversion H1.
      destruct x. inversion H1. inversion H2. subst v0. contradiction.
      destruct H0. destruct H0. destruct H0. destruct H0.
      rewrite <- EList_evalid in H0. rewrite <- H in H0. contradiction.
      pose proof (@edgeless_graph_disconnected (inf_representable g) (size_representable g) u v c).
      contradiction.
      unfold preserve_vlabel, preserve_elabel; split; intros.
      destruct vlabel. destruct vlabel. auto.
      pose proof (@edgeless_graph_evalid (inf_representable g) (size_representable g) e).
      contradiction.
      (*inductive step*)
      set (u:=src g a). set (v:=dst g a).
      assert (connected g u v). apply adjacent_connected. exists a.
      unfold u; unfold v; apply strong_evalid_adj_edge.
      apply (evalid_strong_evalid g). rewrite <- EList_evalid, <- H. left; auto.
      set (remove_a:=(@UAdjMatGG_eremove g a)).
      assert (Ha_evalid: evalid g a). { rewrite <- EList_evalid. apply (Permutation_in (l:=(a::l))).
                                        apply H. left; auto. }
                                      specialize IHl with remove_a.
      destruct IHl as [t ?]. {
        unfold remove_a. pose proof (@eremove_EList g a Ha_evalid l H).
        apply NoDup_Permutation. assert (NoDup (a::l)). apply (Permutation_NoDup (l:=EList g)).
        apply Permutation_sym; auto. apply NoDup_EList. apply NoDup_cons_1 in H2; auto.
        apply NoDup_EList.
        intros. rewrite EList_evalid. split; intros.
        pose proof (Permutation_in (l:=l) (l':=_) x H1 H2). rewrite EList_evalid in H3; auto.
        apply Permutation_sym in H1.
        apply (Permutation_in (l:=_) (l':=l) x H1). rewrite EList_evalid; auto.
      }
      assert (Htg: is_partial_lgraph t g). {
        destruct H1. destruct H2. destruct H1. destruct H4. split.
        split. intros. apply H1 in H6. auto.
        split. intros. destruct H1. destruct H7. apply H7. auto.
        split. intros. apply H1 in H7. simpl in H7. auto. auto.
        intros. apply H1 in H7. simpl in H7. auto. auto.
        unfold preserve_vlabel, preserve_elabel; split; intros.
        destruct vlabel. destruct vlabel. auto.
        rewrite H3 by auto. simpl. destruct (E_EqDec e a). unfold equiv in e0.
        subst e. assert (evalid remove_a a). apply H1; auto.
        simpl in H7. unfold removeValidFunc in H7. destruct H7; contradiction.
        auto.
      }
      destruct (connected_dec remove_a u v).
      (*already connected*)
      ++
        exists t. destruct H1.  destruct H3. destruct H1. destruct H5.
        split. split.
        (*partial_graph*)
        apply Htg.
        (*uforest*)
        split. auto.
        (*spanning*)
        unfold spanning in *. intros. rewrite <- H6. split; intros.
        {(*---------->*)
          destruct H7 as [p ?].
          apply (connected_by_upath_exists_simple_upath) in H7. destruct H7 as [p' [? ?]]. clear p.
          assert (exists l, fits_upath g l p'). apply (connected_exists_list_edges g p' u0 v0); auto.
          destruct H9 as [l' ?]. destruct (in_dec E_EqDec a l').
          **(*yes: split the path*)
            assert (NoDup l'). apply (simple_upath_list_edges_NoDup g p' l'); auto.
            apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
            destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. subst l'. fold u in H11. fold v in H11.
            assert (~ In a l1). unfold not; intros.
            apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14. apply H14.
            apply in_or_app. left; left; auto.
            assert (~ In a l2). unfold not; intros.
            apply NoDup_app_r in H10. apply (NoDup_app_not_in E (a::nil) l2 H10 a).
            left; auto. auto.
            destruct H11; destruct H11.
            ****
              apply (connected_trans _ u0 u). exists p1. split.
              apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
              apply (connected_trans _ u v). auto.
              exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
            ****
              apply (connected_trans _ u0 v). exists p1. split.
              apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
              apply (connected_trans _ v u). apply connected_symm; auto.
              exists p2. split. apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
          **(*no: fits_upath_transfer*)
            exists p'. split. apply (remove_edge_valid_upath _ a p' l'); auto. apply H7. apply H7.
        } { (*<---*)
          destruct H7 as [p [? ?]]. exists p. split.
          apply remove_edge_unaffected in H7; auto. auto.
        }
        (*labels*)
        apply Htg.
      ++
        assert (vvalid g u /\ vvalid g v). apply connected_vvalid in H0; auto. destruct H3.
        assert (u <= v). apply (undirected_edge_rep g). auto.
        set (w:= elabel g a). 
        assert (Int.min_signed <= w < inf). unfold w. split.
        pose proof (weight_representable g a). apply H6.
        admit. (* needs evalid e < inf *)
        rewrite (vvalid_meaning g) in H3, H4.
        rewrite <- (vvalid_meaning t) in H3, H4.
        assert (Ha: a = (u,v)). unfold u, v; apply (evalid_form g); auto. rewrite Ha in *.
        set (adde_a:=@UAdjMatGG_adde t u v H3 H4 H5 w H6).
        exists adde_a. split. split.
        apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto.
        split.
        (*uforest*)
        apply add_edge_uforest'; auto. apply H1.
        unfold not; intros.
        apply (is_partial_lgraph_connected t remove_a) in H7. contradiction.
        split. apply H1. apply H1.
        (*spanning*)
        unfold spanning; intros. assert (Ht_uv: ~ evalid t (u,v)). unfold not; intros.
        assert (evalid remove_a (u,v)). apply H1; auto.
        simpl in H8. rewrite Ha in H8. unfold removeValidFunc in H8. destruct H8; contradiction.
        split; intros.
        { (*-->*) destruct H7 as [p ?]. apply connected_by_upath_exists_simple_upath in H7.
          destruct H7 as [p' [? ?]]. clear p.
          assert (exists l', fits_upath g l' p'). apply connected_exists_list_edges in H7; auto.
          destruct H9 as [l' ?]. assert (NoDup l'). apply simple_upath_list_edges_NoDup in H9; auto.
          destruct (in_dec E_EqDec a l').
          **
            apply (fits_upath_split2 g p' l' a u0 v0) in H9; auto.
            destruct H9 as [p1 [p2 [l1 [l2 [? [? [? [? ?]]]]]]]]. fold u in H11. fold v in H11. subst l'.
            assert (~ In a l1). unfold not; intros. apply (NoDup_app_not_in E l1 ((a::nil)++l2) H10 a) in H14.
            apply H14. apply in_or_app. left; left; auto.
            assert (~ In a l2). unfold not; intros. apply NoDup_app_r in H10.
            apply (NoDup_app_not_in E (a::nil) l2 H10 a). left; auto. auto.
            destruct H11; destruct H11.
            ****
              apply (connected_trans _ u0 u). apply add_edge_connected; auto.
              apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
              apply (connected_trans _ u v). apply adjacent_connected.
              exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
              apply add_edge_connected; auto. apply H1. exists p2. split.
              apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
            ****
              apply (connected_trans _ u0 v). apply add_edge_connected; auto.
              apply H1. exists p1. split. apply (remove_edge_valid_upath _ a p1 l1); auto. apply H11. apply H11.
              apply (connected_trans _ v u). apply adjacent_connected. apply adjacent_symm.
              exists a. rewrite Ha. apply add_edge_adj_edge1. auto. auto.
              apply add_edge_connected; auto. apply H1. exists p2. split.
              apply (remove_edge_valid_upath _ a p2 l2); auto. apply H16. apply H16.
          **
            apply add_edge_connected; auto.
            apply H1. exists p'. split. 2: apply H7.
            apply (remove_edge_valid_upath g a p' l'); auto. apply H7.
        } {
          apply (is_partial_lgraph_connected adde_a g).
          apply adde_partial_lgraph; auto. unfold w. rewrite Ha; auto. auto.
        }
        (*labels*)
        unfold preserve_vlabel, preserve_elabel; split; intros.
        destruct vlabel; destruct vlabel; auto.
        simpl. unfold update_elabel, equiv_dec.
        destruct (E_EqDec (u,v) e). hnf in e0. subst e. unfold w; rewrite Ha; auto.
        apply Htg. simpl in H7. unfold addValidFunc in H7. destruct H7. apply H7.
        unfold complement, equiv in c. symmetry in H7; contradiction.
  Abort.*)

  Definition minimum_spanning_forest (t g: PrimGG) :=
    labeled_spanning_uforest t g /\
    forall (t': PrimGG),
      labeled_spanning_uforest t' g ->
      Z.le (sum_DE Z.add t 0) (sum_DE Z.add t' 0).

  Corollary exists_labeled_spanning_uforest:
    forall (g: PrimGG), exists (t: PrimGG), labeled_spanning_uforest t g.
  Proof. 
  intros. apply (exists_labeled_spanning_uforest_pre (EList g)). apply Permutation_refl.
  Qed.
  
  (* needs UAdjMatGG and NoDup_incl_ordered_powerlist, which means it should probably stay right here *) 
  Lemma exists_msf:
    forall {E_EqDec : EqDec E eq} (g: PrimGG),
    exists (t: PrimGG), minimum_spanning_forest t g.
  Proof.
    intros. pose proof (NoDup_incl_ordered_powerlist (EList g) (NoDup_EList g)).
    destruct H as [L ?].
    (*now what I need is the subset of L that exists t, labeled_spanning_uforest t g ...*)
    destruct (list_decidable_prop_reduced_list
                (fun l' => NoDup l' /\ incl l' (EList g) /\ (forall x y, In x l' -> In y l' ->
                                                                         (find l' x 0 <= find l' y 0 <-> find (EList g) x 0 <= find (EList g) y 0)))
                (fun l => (exists (t: PrimGG), labeled_spanning_uforest t g /\ Permutation l (EList t)))
                L
             ).
  Admitted.
  (* 
    apply exists_dec.
    intros; split; intros. rewrite <- H in H0. destruct H0 as [? [? ?]].
    split. apply H0. split. apply H1. apply H2.
    rewrite <- H. auto.
    rename x into Lspan.
    assert (Lspan <> nil). unfold not; intros. {
      destruct (exists_labeled_spanning_uforest g) as [t ?].
      destruct (test2 (EList t) (EList g)) as [lt ?]. apply NoDup_EList. apply NoDup_EList.
      apply partial_graph_incl. apply H2. destruct H3.
      assert (In lt Lspan). apply H0. split. split. apply (Permutation_NoDup (l:=EList t)).
      apply Permutation_sym; auto. apply NoDup_EList.
      split. unfold incl; intros. apply (Permutation_in (l':=EList t)) in H5; auto.
      apply (partial_graph_incl t g) in H5; auto. apply H2. apply H4.
      exists t. split; auto.
      rewrite H1 in H5; contradiction.
    }
    pose proof (exists_Zmin Lspan (fun l => fold_left Z.add (map (elabel g) l) 0) H1).
    destruct H2 as [lmin [? ?]].
    apply H0 in H2. destruct H2. destruct H2 as [? [? ?]]. destruct H4 as [msf [? ?]].
    exists msf. unfold minimum_spanning_forest. split. apply H4. intros.
    destruct (test2 (EList t') (EList g)) as [lt' ?]. apply NoDup_EList. apply NoDup_EList.
    apply partial_graph_incl. apply H8. destruct H9.
    rewrite (sum_DE_equiv msf lmin). 2: apply Permutation_sym; auto.
    rewrite (sum_DE_equiv t' lt'). 2: apply Permutation_sym; auto.
    replace (map (elabel msf) lmin) with (map (elabel g) lmin).
    replace (map (elabel t') lt') with (map (elabel g) lt').
    apply H3. apply H0. split. split.
    apply (Permutation_NoDup (l:=EList t')). apply Permutation_sym; auto. apply NoDup_EList.
    split. unfold incl; intros. apply (Permutation_in (l':=EList t')) in H11; auto.
    apply (partial_graph_incl t' g) in H11. auto. apply H8.
    apply H10. exists t'. split; auto.
    symmetry; apply partial_lgraph_elabel_map. split. apply H8. apply H8.
    apply Permutation_incl; auto.
    symmetry; apply partial_lgraph_elabel_map. split. apply H4. apply H4.
    apply Permutation_incl; auto.
  Qed.
   *)
  
  Lemma msf_if_le_msf:
    forall (t g: PrimGG),
      labeled_spanning_uforest t g ->
      (forall t', minimum_spanning_forest t' g ->
                  sum_DE Z.add t 0 <= sum_DE Z.add t' 0) ->
      minimum_spanning_forest t g.
  Proof. 
    intros. unfold minimum_spanning_forest. split. auto.
    intros. destruct (@exists_msf E_EqDec g) as [msf ?].
    apply (Z.le_trans _ (sum_DE Z.add msf 0)). auto.
    apply H2. auto.
  Qed.
  
  Corollary msf_if_le_msf':
    forall {E_EqDec : EqDec E eq} (t t' g: PrimGG),
      labeled_spanning_uforest t g ->
      minimum_spanning_forest t' g ->
      sum_DE Z.add t 0 <= sum_DE Z.add t' 0 ->
      minimum_spanning_forest t g.
  Proof.
    intros. apply msf_if_le_msf; auto.
    intros. apply (Z.le_trans _ (sum_DE Z.add t' 0)). auto.
    apply H0. apply H2.
  Qed.
  
End MathPrimGraph.
