Require Import CertiGraph.CertiGC.gc_spec.

Lemma body_make_tinfo: semax_body Vprog Gprog f_make_tinfo make_tinfo_spec.
Proof.
  start_function.
  forward_call (sh, gv).
  Intros vret. destruct vret as [h p]. simpl fst. simpl snd.
  forward_call (thread_info_type, gv).
  Intros t. if_tac.
  - subst t. forward_if False.
    2: exfalso; first [rewrite Int64.eq_true in H; inversion H | apply H; trivial].
    unfold all_string_constants; Intros;
      forward_call ((gv ___stringlit_9),
                     (map init_data2byte (gvar_init v___stringlit_9)), sh);
      exfalso; assumption.
  - Intros. forward_if True; [contradiction | forward; entailer! |]. Intros.
    forward. forward. rewrite Znth_0_cons. forward. forward. rewrite Znth_0_cons.
    forward. forward. Exists t h p. entailer!.
Qed.
