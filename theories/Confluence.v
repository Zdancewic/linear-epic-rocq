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
  (* TODO: hopefuly easy corrolary of prior lemmas *)
Admitted.


Definition aeq (m n : nat) (t1 t2 : term) :=
  exists t1', t1 ≈t t1' /\ peq_t m n t1' t2.

(* aeq Should be an equivalence relation *)
#[global] Instance aeq_Reflexive (m n : nat) : Reflexive (aeq m n).
Proof.
Admitted.

(* should be able to declare instances for Symmetric and Transitive too *)


Lemma seq_term_inv:
  forall m1 n1 P1 m2 n2 P2,
    (bag m1 n1 P1) ≈t (bag m2 n2 P2) ->
    m1 = m2 /\ n1 = n2 /\ P1 ≈p P2.
Proof.
Admitted.  

Lemma seq_proc_par_inv_l :
  forall P1 P2 Q,
    (par P1 Q) ≈p (par P2 Q) ->
    P1 ≈p P2.
Proof.
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
        assumption.
      }
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
