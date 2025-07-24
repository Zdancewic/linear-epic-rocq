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

(* peq/seq lemmas *)
Lemma peq_renaming_tpo : 
(forall (t : term),
  forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)))
/\
(forall (P : proc),
  forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_proc m n bf br P (rename_fvar_proc bf (rename_rvar_proc br P)))
/\
(forall (o : oper),
  forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n)  
         (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
         (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
          peq_oper m n bf br o (rename_fvar_oper bf (rename_rvar_oper br o))).
Proof.
  apply tpo_ind; intros.
  - simpl.
    
  
Admitted. 

Lemma peq_renaming_term :
forall (t : term),
  forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n)
       (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
       (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
        peq_term m n bf br t (rename_fvar_term bf (rename_rvar_term br t)).
Proof.
  apply peq_renaming_tpo.
Qed.


Lemma tpo_seq_rename_fvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_fvar_term bf t1) ≈t
      (rename_fvar_term bf t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_fvar_proc bf P1) ≈p
      (rename_fvar_proc bf P2)))   
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_fvar_oper bf o1) ≈o
      (rename_fvar_oper bf o2))).
Proof.
  apply seq_tpo_ind; intros.
  - simpl. apply seq_bag. 
    
    (* replace P1, P2 with ren_id *)
Admitted.

Lemma tpo_seq_rename_rvar : 
  (forall t1 t2,
    t1 ≈t t2 ->
    (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_term br t1) ≈t
      (rename_rvar_term br t2)))
  /\
  (forall P1 P2,
    P1 ≈p P2 ->
      (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_proc br P1) ≈p
      (rename_rvar_proc br P2))) 
  /\
  (forall o1 o2,
    o1 ≈o o2 ->
      (forall m n
      (bf : Renamings.ren m m)
      (br : Renamings.ren n n)
      (HWF : Renamings.wf_ren bf)
      (HBF : Renamings.bij_ren bf)
      (HWR : Renamings.wf_ren br)
      (HBR : Renamings.bij_ren br),
      (rename_rvar_oper br o1) ≈o
      (rename_rvar_oper br o2))).
Proof.
  apply seq_tpo_ind; intros.
  - apply seq_bag; assumption.
  - reflexivity.
  - specialize (H m n bf br HWF HBF HWR HBR); firstorder.
  - specialize (H m n bf br HWF HBF HWR HBR);
    specialize (H0 m n bf br HWF HBF HWR HBR).
    specialize (Transitive_seq_proc (rename_rvar_proc br P1)
                                    (rename_rvar_proc br P2)
                                    (rename_rvar_proc br P3)).
    firstorder.
  - simpl. apply seq_par_comm.
  - simpl. apply seq_par_assoc1.
  - simpl. apply seq_par_assoc2.
  - simpl.
    specialize (H m n bf br HWF HBF HWR HBR);
    specialize (H0 m n bf br HWF HBF HWR HBR).
    apply seq_par_cong; try assumption.
  - simpl.    
    specialize (H m n bf br HWF HBF HWR HBR).
    apply seq_def; assumption.
  - auto.
  - simpl; auto.     
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
Admitted.


Lemma peq_implies_seq: 
 (forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (t t' : term)
    (HT : peq_term m n bf br t t'),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    t ≈t (rename_fvar_term (Renamings.bij_inv bf HBF)
                           (rename_rvar_term (Renamings.bij_inv br HBR) t')))
  /\
 (forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (P P' : proc)
    (HP : peq_proc m n bf br P P'),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    P ≈p (rename_fvar_proc (Renamings.bij_inv bf HBF)
                           (rename_rvar_proc (Renamings.bij_inv br HBR) P')))  
  /\
 (forall (m n : nat) (bf : Renamings.ren m m) (br : Renamings.ren n n) (o o' : oper)
    (Ho : peq_oper m n bf br o o'),
    forall (HWF : Renamings.wf_ren bf) (HBF : Renamings.bij_ren bf)
           (HWR : Renamings.wf_ren br) (HBR : Renamings.bij_ren br),
    o ≈o (rename_fvar_oper (Renamings.bij_inv bf HBF)
                           (rename_rvar_oper (Renamings.bij_inv br HBR) o'))).
Proof.
  apply peq_tpo_ind; intros.
  - simpl. 
    assert (Renamings.wf_ren (Renamings.bij_app bf' bf)).
    { apply Renamings.wf_bij_app; try assumption. }
    assert (Renamings.bij_ren (Renamings.bij_app bf' bf)).
    { apply Renamings.bij_ren_app; try assumption. }
    assert (Renamings.wf_ren (Renamings.bij_app br' br)).
    { apply Renamings.wf_bij_app; try assumption. }
     assert (Renamings.bij_ren (Renamings.bij_app br' br)).
    { apply Renamings.bij_ren_app; try assumption. }
    specialize (H H0 X H1 X0).
    (* find appropriate lemma here 
      rewrite -> Renamings.bij_inv_app in H. *)
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

  specialize (peq_implies_seq x0 y m n bf br EQ) as H.
  symmetry in H.
  specialize (peq_renaming_term m n bf br x0 HWF HBF HWR HBR) as H'.
  specialize (seq_renaming_term x0 x Hx0 m n bf br HWF HBF HWR HBR) as H''.
  specialize (peq_t_intro m n x0 
              (rename_fvar_term bf (rename_rvar_term br x0))
              bf br HWF HBF HWR HBR H') as Hx0'.
  specialize (peq_renaming_term m n bf br x HWF HBF HWR HBR) as Hx.
  specialize (peq_t_intro m n x
              (rename_fvar_term bf (rename_rvar_term br x))
              bf br HWF HBF HWR HBR Hx) as Hx'.

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


Lemma seq_proc_par_inv_l :
  forall P1 P2 Q,
    (par P1 Q) ≈p (par P2 Q) ->
    P1 ≈p P2.
Proof.
  intros.
  remember (par P1 Q) as P1'.
  remember (par P2 Q) as P2'.
  revert P1 P2 Q HeqP1' HeqP2'.
  induction H; intros.
  rewrite HeqP1' in HeqP2'.
  inversion HeqP2'.
  reflexivity.
  specialize (seq_par_comm P1 Q) as HP; symmetry in HP.
  specialize (Transitive_seq_proc (par Q P1) (par P1 Q) (par P2 Q) HP H) as HP1.
  clear HP.
  specialize (seq_par_comm P2 Q) as HQ.
  specialize (Transitive_seq_proc (par Q P1) (par P2 Q) (par Q P2) HP1 HQ) as HQ1.
  clear HQ.
  specialize (seq_par_cong Q Q P1 P2) as HPQ.
  specialize (Reflexive_seq_proc Q) as HQ; apply HPQ in HQ.


  eapply seq_bag in H.
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
