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


Definition aeq (m n : nat) (t1 t2 : term) :=
  exists t1', t1 ≈t t1' /\ peq_t m n t1' t2.

(* aeq Should be an equivalence relation *)
Lemma reflexive_aeq : 
  forall m n (t: term), ws_term m n t -> aeq m n t t.
Proof.
  intros. 
  unfold aeq.
  exists t.
  split.
  apply Reflexive_seq_term.
  apply peq_t_refl; assumption.
Qed.

#[global] Instance aeq_Symmetric (m n : nat) : Symmetric (aeq m n).
Proof.
  unfold Symmetric.
  intros x y Hxy.
  inversion Hxy.
  destruct H as [Hx0 Hx0y].
  assert (aeq m n x x0).
  { symmetry in Hx0.
    unfold aeq.
    symmetry in Hx0; exists x0.
    split. assumption. admit. }
  unfold aeq.
  symmetry in Hx0; symmetry in Hx0y.
Admitted.

#[global] Instance aeq_Transitive (m n : nat) : Transitive (aeq m n).
Proof.
  unfold Transitive.
  intros x y z Hxy Hyz. 
  inversion Hxy; inversion Hyz; subst.
  destruct H as [Hx0 Hx0y].
  destruct H0 as [Hx1 Hx1z].
  assert (aeq m n x1 x0).
  { unfold aeq.
    symmetry in Hx1; symmetry in Hx0y. 
    exists y.
    split; try assumption. }
  destruct H as [x2 [Hx2 Hx2x0]].
Admitted.


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
  
Admitted.  

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
