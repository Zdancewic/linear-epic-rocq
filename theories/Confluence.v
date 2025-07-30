From Stdlib Require Import
  Arith            
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Morphisms
  Program.Basics
  List
  Lia.

From LEpic Require Import
  Contexts
  Syntax.


Lemma wf_step : forall m n t t' (G : lctxt m),
    wf_term m n G (zero n) t ->
    step m n t t' ->
    wf_term m n G (zero n) t'.
Proof.
  intros.
  inversion H0; subst. 
  specialize (wf_seq_term t t1') as Ht1'.
  apply Ht1' with (m := m) (n := n) (G := G) (D := zero n) in H1;
  try assumption.
  apply wf_prim_step with (m := m) (n := n) (G := G) (t := t1') (t' := t');
  try assumption.
Qed.

(* Renamings lemmas *)

Lemma wf_ren_shift :
forall m m' 
       (bf : Renamings.ren m' m')
       (HWF : Renamings.wf_ren bf),
  Renamings.wf_ren (Renamings.ren_shift m bf).
Proof.
  intros.
  unfold Renamings.wf_ren in *.
  intros x; split; intros H.
  - unfold Renamings.ren_shift, ctxt_app, Renamings.ren_id.
    destruction.
    assert (x - m < m') by lia.
    specialize (HWF (x - m)); destruct HWF as [HWF1 HWF2].
    apply HWF1 in H0; try lia.
  - unfold Renamings.ren_shift, ctxt_app, Renamings.ren_id.
    destruction.
    assert (~ x - m < m') by lia.
    specialize (HWF (x - m)); destruct HWF as [HWF1 HWF2].
    apply HWF2 in H0; try lia.
Qed.
    
Lemma bij_ren_shift :
forall m m' 
       (bf : Renamings.ren m' m')
       (HWF : Renamings.wf_ren bf)
       (HBF : Renamings.bij_ren bf),
  Renamings.bij_ren (Renamings.ren_shift m bf).
Proof.
  intros. 
  inversion HBF; destruct H as [Hx Hx'].
  unfold Renamings.bij_ren.
  exists (Renamings.ren_shift m x).
  split.
  - apply wf_ren_shift; assumption.
  - unfold Renamings.ren_inverses in *.
    intros x0 Hx0; split.
    + unfold Renamings.ren_shift, Renamings.ren_id, ctxt_app.
      destruction.
      specialize (Hx' (x0 - m)).
      assert (x0 - m < m') by lia; apply Hx' in H.
      destruct H as [Hxbf1 Hxbf2].
      replace (m + bf (x0 - m) - m) with (bf (x0 - m)) by lia. 
      rewrite Hxbf1; lia.
    + unfold Renamings.ren_shift, Renamings.ren_id, ctxt_app.
      destruction.
      specialize (Hx' (x0 - m)).
      assert (x0 - m < m') by lia; apply Hx' in H.
      destruct H as [Hxbf1 Hxbf2].
      replace (m + x (x0 - m) - m) with (x (x0 - m)) by lia. 
      rewrite Hxbf2; lia.
Qed.

Lemma bij_app_id_shift : 
  forall (n n' : nat) (br : Renamings.ren n' n')
         (HWF : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
  (Renamings.bij_app (Renamings.ren_id n) br) = (Renamings.ren_shift n br).
Proof.
  intros.
  unfold Renamings.bij_app, Renamings.ren_shift, Renamings.ren_id, ctxt_app.
  apply functional_extensionality.
  intros x; destruction.
Qed.

Lemma bij_ren_inv_elt : 
  forall (m x : nat) (bf : Renamings.ren m m) 
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf),
    x < m -> 
    bf (Renamings.bij_inv bf HBF x) = x.
Proof.
  intros. 
  destruct HBF as [r_inv [HR HI]].
  simpl.
  apply HI in H.
  destruct H.
  symmetry. auto.
Qed.

Lemma bij_bij_app : 
  forall (m n : nat) (bf : Renamings.ren n n)
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf),
    Renamings.bij_ren (Renamings.bij_app (Renamings.ren_id m) bf).
Proof. 
  intros.
  unfold Renamings.bij_ren.
  exists (Renamings.bij_app (Renamings.ren_id m) (Renamings.bij_inv bf HBF)).
  split.
  - apply Renamings.wf_bij_app. 
    apply Renamings.wf_ren_id.
    apply Renamings.wf_bij_ren_inv; auto.
  - unfold Renamings.ren_inverses in *.
    intros x Hx; split.
    + destruct (lt_dec x m).
      unfold Renamings.bij_app, ctxt_app, Renamings.ren_id.
      destruction.
      unfold Renamings.bij_app, ctxt_app, Renamings.ren_id.
      destruction.
      replace (m + bf (x - m) - m) with (bf (x - m)) by lia.
      rewrite <- Renamings.bij_ren_inv_elt with (n := n) (x := (x - m)) (r := bf) (BR := HBF);
      try assumption; try lia.
    + destruct (lt_dec x m).
      unfold Renamings.bij_app, ctxt_app, Renamings.ren_id.
      destruction.
      unfold Renamings.bij_app, ctxt_app, Renamings.ren_id.
      destruction.
      replace (m + Renamings.bij_inv bf HBF (x - m) - m) with 
              (Renamings.bij_inv bf HBF (x - m)) by lia.
      rewrite -> bij_ren_inv_elt with (m := n) (bf := bf) (HBF := HBF) (x := (x - m));
      try assumption; try lia.
Qed.

Lemma bij_ren_inv' :
  forall n (r : Renamings.ren n n) (BR: Renamings.bij_ren r),
    Renamings.wf_ren r ->
    (Renamings.ren_compose r (Renamings.bij_inv r BR)) = (Renamings.ren_id n).
Proof.
  intros.
  destruct BR as [r_inv [HR HI]].
  simpl.
  apply functional_extensionality.
  intros.
  unfold Renamings.ren_compose, compose, Renamings.ren_id.
  destruct (lt_dec x n).
  - apply HI. assumption.
  - assert (r x = n). { apply H. assumption. }
    rewrite H0.
    apply HR.
    lia.
Qed.


(* peq/seq lemmas *)

Import Renamings.

Lemma peq_renaming_tpo : 
  (forall (m n : nat) (t : term),
      ws_term m n t ->
      forall  (bf : Renamings.ren m m) (br : Renamings.ren n n)
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
         (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)))
  /\
    (forall (m n : nat) (P : proc),
        ws_proc m n P ->
        forall (bf : Renamings.ren m m) (br : Renamings.ren n n)
          (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
          (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
          peq_proc m n bf br P (rename_fvar_proc bf (rename_rvar_proc br P)))
  /\
    (forall (m n : nat) (o : oper),
        ws_oper m n o ->
        forall  (bf : Renamings.ren m m) (br : Renamings.ren n n)  
           (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
          peq_oper m n bf br o (rename_fvar_oper bf (rename_rvar_oper br o))).
Proof.
  apply ws_tpo_ind; intros; simpl.
  - rewrite <- bij_app_id_shift with (n := m') (br := bf); try assumption.
    rewrite <- bij_app_id_shift with (n := n') (br := br); try assumption.
    pose proof (wf_ren_id m').
    pose proof (wf_ren_id n').
    pose proof (bij_ren_id m').
    pose proof (bij_ren_id n').
    eapply peq_bag with (bf':=ren_id m')(br':=ren_id n'); auto.
    apply H.
    + apply wf_bij_app; auto.
    + apply bij_ren_app; auto.
    + apply wf_bij_app; auto.
    + apply bij_ren_app; auto.
  - eapply peq_def; auto.
  - eapply peq_app; auto.
  - eapply peq_par; auto.
  - eapply peq_emp; auto.
  - eapply peq_tup; auto.
  - eapply peq_bng; auto.
  - eapply peq_lam; auto.
    apply H; auto.
    apply wf_ren_id.
    apply bij_ren_id.
Qed.    

Lemma peq_renaming_term :
forall (t : term),
forall (m n : nat)
  (HWS: ws_term m n t)
       (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)).
Proof.
  intros. 
  apply peq_renaming_tpo; auto.
Qed. 

Lemma peq_renaming_proc :
forall (P : proc),
forall (m n : nat)
  (HWS: ws_proc m n P) 
       (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_proc m n bf br P (rename_fvar_proc bf (rename_rvar_proc br P)).
Proof.
  intros. 
  apply peq_renaming_tpo; auto.
Qed.

Lemma peq_renaming_oper :
forall (o : oper),
forall (m n : nat)
  (HWS: ws_oper m n o) 
       (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_oper m n bf br o (rename_fvar_oper bf (rename_rvar_oper br o)).
Proof.
  intros. 
  apply peq_renaming_tpo; auto.
Qed.

Lemma tpo_seq_rename_fvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall m 
      (bf : Renamings.ren m m)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf),
      (rename_fvar_term bf t1) ≈t
      (rename_fvar_term bf t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall m
      (bf : Renamings.ren m m)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf),
      (rename_fvar_proc bf P1) ≈p
      (rename_fvar_proc bf P2)))   
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall m 
      (bf : Renamings.ren m m)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf),
      (rename_fvar_oper bf o1) ≈o
      (rename_fvar_oper bf o2))).
Proof.
  apply seq_tpo_ind; intros.
  - simpl. apply seq_bag. 
    specialize (H (m + m0) (Renamings.ren_shift m bf)).
    assert (Renamings.wf_ren (Renamings.ren_shift m bf)) by (apply wf_ren_shift; assumption).
    assert (Renamings.bij_ren (Renamings.ren_shift m bf)) by (apply bij_ren_shift; assumption).
    specialize (H H0 X). assumption.
  - reflexivity.
  - specialize (H m bf HWF HBF). 
    symmetry; assumption.
  - specialize (H m bf HWF HBF). 
    specialize (H0 m bf HWF HBF). 
    specialize (Transitive_seq_proc (rename_fvar_proc bf P1) (rename_fvar_proc bf P2) (rename_fvar_proc bf P3));
    auto.
  - apply seq_par_comm.
  - apply seq_par_assoc1.
  - apply seq_par_assoc2.
  - simpl.
    specialize (H m bf HWF HBF). 
    specialize (H0 m bf HWF HBF).     
    apply seq_par_cong; try assumption.
  - simpl.
    specialize (H m bf HWF HBF).
    apply seq_def; assumption.
  - reflexivity.
  - simpl. 
    specialize (H m bf HWF HBF).
    apply seq_lam; assumption.
Qed.

Lemma seq_rename_fvar_term : 
forall t1 t2,
  t1 ≈t t2 ->
  (forall m
    (bf : Renamings.ren m m)
    (HWF : Renamings.wf_ren bf)
    (HBF : Renamings.bij_ren bf),
    (rename_fvar_term bf t1) ≈t
    (rename_fvar_term bf t2)).
Proof.
  apply tpo_seq_rename_fvar.
Qed.


Lemma tpo_seq_rename_rvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall n
      (br : Renamings.ren n n)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_term br t1) ≈t
      (rename_rvar_term br t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall n
      (br : Renamings.ren n n)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_proc br P1) ≈p
      (rename_rvar_proc br P2))) 
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall n
      (br : Renamings.ren n n)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_oper br o1) ≈o
      (rename_rvar_oper br o2))).
Proof.
  apply seq_tpo_ind; intros.
  - apply seq_bag.  eapply H.
    apply wf_ren_shift. auto.
    apply bij_ren_shift; auto.
  - reflexivity.
  - specialize (H n br HWR HBR); firstorder.
  - specialize (H n br HWR HBR);
    specialize (H0 n br HWR HBR).
    specialize (Transitive_seq_proc (rename_rvar_proc br P1)
                                    (rename_rvar_proc br P2)
                                    (rename_rvar_proc br P3)).
    firstorder.
  - simpl. apply seq_par_comm.
  - simpl. apply seq_par_assoc1.
  - simpl. apply seq_par_assoc2.
  - simpl.
    specialize (H n br HWR HBR);
    specialize (H0 n br HWR HBR).
    apply seq_par_cong; try assumption.
  - simpl.    
    specialize (H n br HWR HBR).
    apply seq_def; assumption.
  - auto.
  - simpl.
    apply seq_lam; auto.
    eapply H.
    apply wf_ren_id.
    apply bij_ren_id.
Qed.

Lemma seq_rename_rvar_term : 
forall t1 t2,
  t1 ≈t t2 ->
  (forall n
    (br : Renamings.ren n n)
    (HWR : Renamings.wf_ren br)
    (HBR : Renamings.bij_ren br),
    (rename_rvar_term br t1) ≈t
    (rename_rvar_term br t2)).
Proof.
  apply tpo_seq_rename_rvar.
Qed.

Lemma seq_rename_rvar_proc : 
forall P1 P2,
  P1 ≈p P2 ->
  (forall n
    (br : Renamings.ren n n)
    (HWR : Renamings.wf_ren br)
    (HBR : Renamings.bij_ren br),
    (rename_rvar_proc br P1) ≈p
    (rename_rvar_proc br P2)).
Proof.
  apply tpo_seq_rename_rvar.
Qed.

Lemma seq_rename_rvar_oper : 
forall o1 o2,
  o1 ≈o o2 ->
  (forall n
    (br : Renamings.ren n n)
    (HWR : Renamings.wf_ren br)
    (HBR : Renamings.bij_ren br),
    (rename_rvar_oper br o1) ≈o
    (rename_rvar_oper br o2)).
Proof.
  apply tpo_seq_rename_rvar.
Qed.

Lemma seq_renaming_term :
forall t1 t2,
  t1 ≈t t2 ->
  (forall m n
    (bf : Renamings.ren m m)
    (br : Renamings.ren n n)
    (HWF : Renamings.wf_ren bf)
    (HBF : Renamings.bij_ren bf)
    (HWR : Renamings.wf_ren br)
    (HBR : Renamings.bij_ren br),
    (rename_fvar_term bf (rename_rvar_term br t1)) ≈t
    (rename_fvar_term bf (rename_rvar_term br t2))).
Proof.
  intros.
  specialize (seq_rename_rvar_term t1 t2 H n br HWR HBR) as Hr.
  specialize (seq_rename_fvar_term (rename_rvar_term br t1) (rename_rvar_term br t2)
              Hr m bf HWF HBF) as Hf.
  assumption.
Qed.


Lemma peq_implies_seq: 
 (forall (t : term),
  forall (t' : term) (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n)
         (HT : peq_term m n bf br t t')
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
         (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    exists (t'' : term), 
    (peq_term m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) t t'') /\ 
    (t ≈t t''))
  /\
 (forall (P : proc),
  forall (P' : proc) (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) 
         (HP : peq_proc m n bf br P P')
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
         (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    exists (P'' : proc), 
    (peq_proc m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) P P'') /\ 
    (P ≈p  P''))
  /\
 (forall (o : oper),
  forall (o' : oper) (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) 
         (Ho : peq_oper m n bf br o o')
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
         (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    exists (o'' : oper), 
    (peq_oper m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) o o'') /\ 
    (o ≈o o'')).
Proof.
  apply tpo_ind; intros.
  - inversion HT. existT_eq; subst.
    specialize (H P' (m + m0) (n + n0) (bij_app bf' bf) (bij_app br' br) EQP).
    assert (Renamings.wf_ren (Renamings.bij_app bf' bf)) by 
    (apply Renamings.wf_bij_app; auto; try assumption).
    assert (Renamings.wf_ren (Renamings.bij_app br' br)) by 
    (apply Renamings.wf_bij_app; auto; try assumption).
    specialize (H H0 (Renamings.bij_ren_app bf' bf WFF' HWF HBF' HBF) 
                  H1 (Renamings.bij_ren_app br' br WFR' HWR HBR' HBR)).
    destruct H as [P'' [Hpeq Hseq]].
    exists (bag m n P'').
    split.
    + simpl. 
      eapply peq_bag with (bf' := (Renamings.bij_inv bf' HBF'))
                          (br' := (Renamings.bij_inv br' HBR')); auto.
      apply Renamings.wf_bij_ren_inv; auto. 
      apply Renamings.bij_inv_bij; auto. 
      apply Renamings.wf_bij_ren_inv; auto. 
      apply Renamings.bij_inv_bij; auto.
      rewrite <- Renamings.bij_inv_app 
        with (HWF1 := WFF')(HWF2 := HWF).
      rewrite <- Renamings.bij_inv_app 
        with (HWF1 := WFR')(HWF2 := HWR).
      assumption.
    + apply seq_bag; assumption.
  - inversion HP; existT_eq; subst.
    specialize (H o' m n bf br H7 HWF HBF HWR HBR).
    destruct H as [o'' [Hpeq Hseq]].
    exists (def ((Renamings.bij_inv br HBR) r) o'').
    split.
    + eapply peq_def; auto.
    + (* apply seq_def. *)
      admit.
  - inversion HP; existT_eq; subst.
    exists (app ((Renamings.bij_inv bf HBF) f) ((Renamings.bij_inv br HBR) r)).
    split.
    + apply peq_app; auto.
    + 
      admit.
  - inversion HP; existT_eq; subst.
    specialize (H P1' m n bf br H7 HWF HBF HWR HBR).
    destruct H as [P1'' [Hpeq1 Hseq1]].
    specialize (H0 P2' m n bf br H9 HWF HBF HWR HBR).
    destruct H0 as [P2'' [Hpeq2 Hseq2]].
    exists (par P1'' P2'').
    split.
    + apply peq_par; auto.
    + apply seq_par_cong; auto.
  - inversion Ho; existT_eq; subst.
    exists (emp).
    split.
    + apply peq_emp; auto.
    + reflexivity.
  - inversion Ho; existT_eq; subst.
    exists (tup ((Renamings.bij_inv br HBR) r1) ((Renamings.bij_inv br HBR) r2)).
    split.
    + apply peq_tup; auto.
    + replace (tup (bij_inv br HBR r1) (bij_inv br HBR r2)) with 
      (rename_rvar_oper (Renamings.bij_inv br HBR) (tup r1 r2)) by reflexivity.

      admit.
  - inversion Ho; existT_eq; subst.
    exists (bng ((Renamings.bij_inv bf HBF) f)).
    split.
    + apply peq_bng; auto.
    + 
      admit.
  - inversion Ho; existT_eq; subst.
    assert (Renamings.wf_ren (Renamings.ren_id 1)) by (apply Renamings.wf_ren_id).
    specialize (H t' m 1 bf (Renamings.ren_id 1) H5 HWF HBF H0 
                (Renamings.bij_ren_id 1)).
    destruct H as [t'' [Hpeq Hseq]].
    exists (lam t'').
    split.
    + apply peq_lam; auto.
    + apply seq_lam; auto.
Admitted. 


Lemma peq_renaming_inv_tpo :
  (forall (m n:nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (t u : term)
    (HT : peq_term m n bf br t u),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    peq_term m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) u t)
  /\
  (forall (m n :nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (P Q : proc)
    (HP : peq_proc m n bf br P Q),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    peq_proc m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) Q P)
  /\
  (forall (m n:nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (o o' : oper)
    (Ho : peq_oper m n bf br o o'),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    peq_oper m n (Renamings.bij_inv bf HBF) (Renamings.bij_inv br HBR) o' o).
Proof.
  apply peq_tpo_ind; intros.
  - apply peq_bag with (bf' := Renamings.bij_inv bf' HBF') (br' := Renamings.bij_inv br' HBR').
    apply Renamings.wf_bij_ren_inv.
    apply Renamings.bij_inv_bij; auto.
    apply Renamings.wf_bij_ren_inv.
    apply Renamings.bij_inv_bij; auto.
    rewrite <- Renamings.bij_inv_app 
      with (HWF1 := WFF')(HWF2 := HWF).    
    rewrite <- Renamings.bij_inv_app 
      with (HWF1 := WFR')(HWF2 := HWR).
    apply H.
    apply Renamings.wf_bij_app; auto.
    apply Renamings.wf_bij_app; auto.
  - assert (r = ((Renamings.bij_inv br HBR) (br r))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    constructor; auto.
    apply HWR; auto.
  - assert (r = ((Renamings.bij_inv br HBR) (br r))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H at 2.
    assert (f = ((Renamings.bij_inv bf HBF) (bf f))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    constructor; auto.
    apply HWF; auto.
    apply HWR; auto.
  - constructor; auto.
  - constructor; auto.
  - assert (r1 = ((Renamings.bij_inv br HBR) (br r1))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H at 2.
    assert (r2 = ((Renamings.bij_inv br HBR) (br r2))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    econstructor.
    apply HWR; auto.
    apply HWR; auto.
  - assert (f = ((Renamings.bij_inv bf HBF) (bf f))).
    { apply Renamings.bij_ren_inv_elt; auto. }
    rewrite H at 2.
    constructor; auto.
    apply HWF; auto.
  - constructor; auto.
    rewrite <- Renamings.bij_inv_id.
    apply H; auto.
    apply Renamings.wf_ren_id.
Qed.


(* Alpha Equivalence *)
Definition aeq (m n : nat) (t1 t2 : term) :=
  exists t1', t1 ≈t t1' /\ peq_t m n t1' t2.

(* aeq should be an equivalence relation *)
Lemma reflexive_aeq : 
  forall m n (x : term), ws_term m n x -> aeq m n x x.
Proof.
  intros. 
  unfold aeq.
  exists x.
  split.
  apply Reflexive_seq_term.
  apply peq_t_refl; assumption.
Qed.

#[global] Instance aeq_Symmetric (m n : nat) : Symmetric (aeq m n).
Proof.
  unfold Symmetric.
  intros x y Hxy.
  unfold aeq in *.
  destruct Hxy as [x0 [Hx0 Hx0y]]; symmetry in Hx0.
  destruct Hx0y.

  (* 
  specialize (peq_renaming_term m n bf br x0 HWF HBF HWR HBR) as H'.
  specialize (seq_renaming_term x0 x Hx0 m n bf br HWF HBF HWR HBR) as H''.
  specialize (peq_t_intro m n x0 
              (rename_fvar_term bf (rename_rvar_term br x0))
              bf br HWF HBF HWR HBR H') as Hx0'.
  specialize (peq_renaming_term m n bf br x HWF HBF HWR HBR) as Hx.
  specialize (peq_t_intro m n x
              (rename_fvar_term bf (rename_rvar_term br x))
              bf br HWF HBF HWR HBR Hx) as Hx'. 
  *)

Admitted.

(* Uses aeq_Symmetric. *)
#[global] Instance aeq_Transitive (m n : nat) : Transitive (aeq m n).
Proof.
  unfold Transitive.
  intros x y z Hxy Hyz. 
  inversion Hxy; inversion Hyz; subst.
  destruct H as [Hx0 Hx0y].
  destruct H0 as [Hx1 Hx1z].
  unfold aeq.
  assert (aeq m n x1 x0).
  { unfold aeq.
    symmetry in Hx1; symmetry in Hx0y. 
    exists y.
    split; try assumption. }
  assert (H' : aeq m n x1 x0) by (apply H).
  apply aeq_Symmetric in H'.
  destruct H as [x2 [Hx2 Hx2x0]].
  destruct H' as [x3 [Hx3 Hx3x1]].
  assert (x ≈t x3). 
  { specialize (Transitive_seq_term x x0 x3 Hx0 Hx3);
    firstorder. }
  assert (peq_t m n x3 z).
  { specialize (Transitive_peq_term x3 x1 z Hx3x1 Hx1z);
    firstorder. }
  exists x3; split; try assumption.
Qed.


(* seq lemmas for confluence *)
Lemma seq_term_inv:
  forall m1 n1 P1 m2 n2 P2,
    (bag m1 n1 P1) ≈t (bag m2 n2 P2) ->
    m1 = m2 /\ n1 = n2 /\ P1 ≈p P2.
Proof.
  intros.
  repeat split.
  all : (inversion H; try reflexivity).
  assumption.
Qed. 


(* P1 | def ro eq P2 | def ro -> P1 eq P2 lemma? 
  with symmetric version? *)
Lemma seq_proc_par_inv_l :
  forall P1 P2 Q1 Q2,
    (Q1 ≈p Q2) -> 
    (((par P1 Q1) ≈p (par P2 Q2)) -> 
    P1 ≈p P2) /\
    (((par Q1 P1) ≈p (par Q2 P2)) -> 
    P2 ≈p P1).
Proof.
  intros.
  revert P1 P2.
  induction H.
  - intros. 
    inversion Hpar; try reflexivity.
(* 
  Running into the same issue with proof state either:
  H : par P2 P ≈p par (def r o) P
  H0 : P0 = par (def r o) P
  H1 : P1 = par P2 P

  or else:
  H : par P2 P ≈p par P1 P
  H0 : P3 = par P1 P
  H1 : P0 = par P2 P

  Have tried: 
  - inducting on HQ...
    + inverting Hpar.
    + inducting on P1.
  - inducting on P1. 
    + inverting Hpar.
    + inducting on HQ.
    + induction on P2...
      * inverting Hpar.
      * inducting on HQ -> inverting Hpar.

  I am thinking that Hpar might need to change. Despite having HQ; Hpar is not enough
  when it is inverted.
*)
Admitted.  


(* Confluence *)
Lemma confluence :
  forall m n (t t1 t2: term) (G : lctxt m) (D : lctxt n)
    (HWF : wf_term m n G D t)
    (HS1 : step m n t t1)
    (HS2 : step m n t t2),
  exists m', exists n',
    (aeq m' n' t1 t2) 
    \/
      (exists t1', exists t2', 
        (step m n t1 t1') /\
          (step m n t2 t2') /\
          aeq m' n' t1' t2').
Proof.
  intros.
  inversion HS1; subst.
  inversion HS2; subst.
  inversion H0; inversion H2; subst.
  - destruct (Nat.eq_dec r r0).
    + subst.
      assert (m' = m'0 /\ n' = n'0 /\ P ≈p P0).
      { rewrite H in H1.
        apply seq_term_inv in H1.
        destruct H1 as [EQ1 [EQ2 HP]].
        subst.
        repeat split; auto.
        apply seq_proc_par_inv_l in HP.
        assumption. }
      destruct H3 as [EQ1 [EQ2 HP]].
      subst.
      exists m. exists n. left.
      unfold aeq.
      exists (bag m'0 n'0 P0).
      split.
      * apply seq_bag. assumption.
      * apply peq_t_refl.
        specialize (wf_ws_term m n G D t) as Ht.
        apply Ht in HWF; clear Ht.
        (* step and ws interact? w/o assumptions of wfdness. *)
        admit. (* TODO: get this from HWF somehow *)
    + admit. (* two cases, r = r0 -> no step, r <> r0 -> complementary steps *)
  - admit. (* deduce r <> r0 -> complementary step *)
  - admit.
  - admit. (* symmetric with case 2 *)
  - admit. (* two cases, r = r0 -> no step, analogous to 1.a, other case r <> r0 *)
  - admit. (* analogous to case 3 but with more renaming involved *)
  - admit. (* symmetric to case 3 *)
  - admit. (* symmetric to case 6 *)
  - admit. (* three subcases?
               if: r = r0 ->
                       if r' = r0' then no step
                       if r' <> r0' then two different calls to the same function
                   r <> r0 ->
                       two calls to different functions *)
Admitted.
