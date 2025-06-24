From Stdlib Require Import
  Arith            
  Classes.RelationClasses
  Logic.FunctionalExtensionality
  Morphisms
  Program.Basics
  List
  Lia.

From LEpic Require Import Contexts.

Definition rvar := nat.
Definition fvar := nat.

(* Raw de Bruijn Syntax ------------------------------------------------------ *)

(* Terms are represented using de Bruijn indexes.

   There are two types of identifiers:

   Unrestricted (a.k.a. non-linear) Identifiers
    - these represent names of lambdas
    - by convention, we use [m : nat] to represent the number of such 
      identifies in scope within a term
    - we use [f] (for "function") and variants as the metavariable
      for writing down function identifiers

   Linear Identifiers
    - these represent "cuts" or "resource names" in the semantics
    - by convention, we use [n : nat] to represent the number of such
      identifiers in scope within a term
    - we use [r] (for "resource") and variants as the metavariable
      for writing down function identifiers 

   # Terms:

   A "term" [t] is a "bag" [bag m n P], consisting of a processes [P]. 
   It binds [m] (fresh) function identifiers and [n] (fresh) resource
   identifiers.

   # Processes:

   A process [P] is one of:
     - a definition [def r o] (written informally as "r <- o"),
       which defines the resource [r] as the operand [o]

     - a function application [f r].  Functions always take one
       argument, [r], and the function identifer [f] should be
       bound to a lambda somwehere in the context

     - two processes running "in parallel": [par P1 P2]

   # Operands:

   An operand [o] provides a definition of a resource identifier and
   can be one of:

     - emp          the empty tuple ()
     - [tup r1 r2]  a "tuple" (pair) of resources
     - [bng f]      the name of a function
     - [lam t]      an lambda, which is a term parameterized by one resource


  (* SAZ: We could contemplate defining Rocq notations for terms. *) 

 *)

Inductive term :=
| bag (m n:nat) (P:proc)   (* nu. {f1...fm} {r1..rn} P *)

with proc :=
| def (r:rvar) (o:oper)  (* r <- o *)
| app (f:fvar) (r:rvar)  (* f r *)
| par (P1 P2 : proc)     (* P1 | P2 *)

with oper :=
| emp                    (* empty tuple *)
| tup (r1 r2:rvar)       (* (r1,r2) *)
| bng (f:fvar)           (* !f *)
| lam (t : term).        (* lam r. t *)

Scheme term_ind_m := Induction for term Sort Prop
  with proc_ind_m := Induction for proc Sort Prop
  with oper_ind_m := Induction for oper Sort Prop.

Combined Scheme tpo_ind from term_ind_m, proc_ind_m, oper_ind_m.

Scheme term_rect_m := Induction for term Sort Type
  with proc_rect_m := Induction for proc Sort Type
  with oper_rect_m := Induction for oper Sort Type.

Combined Scheme tpo_rect from term_rect_m, proc_rect_m, oper_rect_m.

Scheme term_rec_m := Induction for term Sort Set
  with proc_rec_m := Induction for proc Sort Set
  with oper_rec_m := Induction for oper Sort Set.

Combined Scheme tpo_rec from term_rec_m, proc_rec_m, oper_rec_m.



(* Scoping *)

(* Well scoping - just checks that de Bruijn variables are in bounds.

   [ws_term m n t] means that term [t] is well-scoped with at most
   [m] function identifiers and [n] resource identifiers.

   (and similarly for [ws_proc] and [ws_oper]).

   A de Bruijn variable is "in scope" if it is less than the number
   of variables in the context.
 *)
Unset Elimination Schemes.
Inductive ws_term : nat -> nat -> term -> Prop :=
| ws_bag :
  forall m n
    m' n'
    P
    (WS : ws_proc (m' + m) (n' + n) P),
    ws_term m n (bag m' n' P)

with ws_proc : nat -> nat -> proc -> Prop :=
| ws_def :
  forall m n
    (r : rvar) (HR : r < n)
    (o : oper) (WSO : ws_oper m n o),
    ws_proc m n (def r o)

| ws_app :
  forall m n
    (f : fvar) (HF : f < m)
    (r : rvar) (HR : r < n),
    ws_proc m n (app f r)

| ws_par :
  forall m n
    (P1 P2 : proc)
    (WSP1 : ws_proc m n P1)
    (WSP2 : ws_proc m n P2),
    ws_proc m n (par P1 P2)
            
with ws_oper : nat -> nat -> oper -> Prop :=
|ws_emp :
  forall m n,
    ws_oper m n emp

| ws_tup :
  forall m n
    (r1 : rvar) (HR1 : r1 < n)
    (r2 : rvar) (HR2 : r2 < n),
    ws_oper m n (tup r1 r2)

| ws_bng :
  forall m n
    (f : fvar)
    (HF : f < m),
    ws_oper m n (bng f)
            
| ws_lam :
  forall m n
    (t : term)
    (WST : ws_term m 1 t),
    ws_oper m n  (lam t).
Set Elimination Schemes.

Scheme ws_term_ind := Induction for ws_term Sort Prop
    with ws_proc_ind := Induction for ws_proc Sort Prop
                        with ws_oper_ind := Induction for ws_oper Sort Prop.

Combined Scheme ws_tpo_ind from ws_term_ind, ws_proc_ind, ws_oper_ind.

(* Structural Equivalence --------------------------------------------------- *)

(* Defines "structural" equivalence of the syntax.  The syntax is considered
   up to reordering of the process components within a bag.  That is,
   we can permute and re-associate the [par] operator.

   Note that such permutations do not affect the meaning of de Bruijn
   indices.

   These relations define equivalence relations on syntax.
 *)

Inductive seq_term : term -> term -> Prop :=
| seq_bag :
  forall m n P1 P2,
    seq_proc P1 P2 ->
    seq_term (bag m n P1) (bag m n P2)

with seq_proc : proc -> proc -> Prop :=
| seq_proc_refl :
  forall (P : proc),
    seq_proc P P

| seq_proc_symm :
  forall P1 P2,
    seq_proc P1 P2 ->
    seq_proc P2 P1
             
| seq_proc_trans :
  forall P1 P2 P3,
    seq_proc P1 P2 ->
    seq_proc P2 P3 ->
    seq_proc P1 P3
             
| seq_par_comm :
  forall (P1 P2 : proc),
    seq_proc (par P1 P2) (par P2 P1)

| seq_par_assoc1 :
  forall (P1 P2 P3 : proc),
    seq_proc (par P1 (par P2 P3)) (par (par P1 P2) P3)

| seq_par_assoc2 :
  forall (P1 P2 P3 : proc),
    seq_proc (par (par P1 P2) P3) (par P1 (par P2 P3))
             
| seq_par_cong :
  forall P1 P1' P2 P2',
    seq_proc P1 P1' ->
    seq_proc P2 P2' ->
    seq_proc (par P1 P2) (par P1' P2')

| seq_def :
  forall r o1 o2,
    seq_oper o1 o2 ->
    seq_proc (def r o1) (def r o2)
             
with seq_oper : oper -> oper -> Prop :=
| seq_oper_refl :
  forall o,
    seq_oper o o

| seq_lam :
  forall t1 t2,
    seq_term t1 t2 ->
    seq_oper (lam t1) (lam t2)
.

Scheme seq_term_mut_ind := Induction for seq_term Sort Prop
    with seq_proc_mut_ind := Induction for seq_proc Sort Prop
                        with seq_oper_mut_ind := Induction for seq_oper Sort Prop.

Combined Scheme seq_tpo_ind from seq_term_mut_ind, seq_proc_mut_ind, seq_oper_mut_ind.

Hint Constructors seq_term seq_proc seq_oper : core.

Infix "≈t" := seq_term (at level 55).
Infix "≈p" := seq_proc (at level 55).
Infix "≈o" := seq_oper (at level 55).

Lemma tpo_seq_reflexive :
  (forall (t : term), t ≈t t) /\
    (forall (P : proc), P ≈p P) /\
    (forall (o : oper), o ≈o o).
Proof.
  apply tpo_ind; intros; auto.
Qed.

#[global] Instance Reflexive_seq_term : Reflexive (seq_term).
Proof.
  unfold Reflexive.
  apply tpo_seq_reflexive.
Qed.

#[global] Instance Reflexive_seq_proc : Reflexive (seq_proc).
Proof.
  unfold Reflexive.
  apply tpo_seq_reflexive.
Qed.

#[global] Instance Reflexive_seq_oper : Reflexive (seq_oper).
Proof.
  unfold Reflexive.
  apply tpo_seq_reflexive.
Qed.

Lemma tpo_seq_transitive :
  (forall (t1 t2 t3 : term), t1 ≈t t2 -> t2 ≈t t3 -> t1 ≈t t3) /\
    (forall (P1 P2 P3 : proc), P1 ≈p P2 -> P2 ≈p P3 -> P1 ≈p P3) /\
    (forall (o1 o2 o3 : oper), o1 ≈o o2 -> o2 ≈o o3 -> o1 ≈o o3).
Proof.
  apply tpo_ind; intros.
  - inversion H0. subst.
    inversion H1. subst.
    constructor. eapply H; eauto. 
  - eapply seq_proc_trans; eauto.
  - eapply seq_proc_trans; eauto.
  - eapply seq_proc_trans; eauto.
  - inversion H; subst.
    inversion H0; subst.
    reflexivity.
  - inversion H; subst.
    inversion H0; subst.
    reflexivity.
  - inversion H; subst.
    inversion H0; subst.
    reflexivity.
  - inversion H1; subst; auto.
    inversion H0; subst; auto.
    econstructor.
    eapply H; eauto.
Qed.

#[global] Instance Transitive_seq_term : Transitive (seq_term).
Proof.
  unfold Transitive.
  apply tpo_seq_transitive.
Qed.

#[global] Instance Transitive_seq_proc : Transitive (seq_proc).
Proof.
  unfold Transitive.
  apply tpo_seq_transitive.
Qed.

#[global] Instance Transitive_seq_oper : Transitive (seq_oper).
Proof.
  unfold Transitive.
  apply tpo_seq_transitive.
Qed.

Lemma tpo_seq_symmetric :
  (forall (t1 t2 : term), t1 ≈t t2 -> t2 ≈t t1) /\
    (forall (P1 P2 : proc), P1 ≈p P2 -> P2 ≈p P1) /\
    (forall (o1 o2 : oper), o1 ≈o o2 -> o2 ≈o o1).
Proof.
  apply tpo_ind; intros; auto.
  - inversion H0. subst.
    constructor. apply H. assumption.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - inversion H0; subst; auto.
Qed.

#[global] Instance Symmetric_seq_term : Symmetric (seq_term).
Proof.
  unfold Symmetric.
  apply tpo_seq_symmetric.
Qed.

#[global] Instance Symmetric_seq_proc : Symmetric (seq_proc).
Proof.
  unfold Symmetric.
  apply tpo_seq_symmetric.
Qed.

#[global] Instance Symmetric_seq_oper : Symmetric (seq_oper).
Proof.
  unfold Symmetric.
  apply tpo_seq_symmetric.
Qed.

(* structural equivalence "inversion" lemmas:
   - these lemmas extract information about the structure of a
     piece of syntax that is known to be structurally equivalent
     to a more defined piece of syntax.
 *)

Lemma seq_proc_inv_def' : forall P1 P2,
    P1 ≈p P2 ->
    (forall r o, P1 = def r o -> exists o', P2 = def r o' /\ o ≈o o') /\
      (forall r o, P2 = def r o -> exists o', P1 = def r o' /\ o ≈o o').
Proof.
  intros P1 P2 H.
  induction H; intros.
  - split; intros; exists o; auto.
  - split; intros.
    + apply IHseq_proc in H0. assumption.
    + apply IHseq_proc in H0. assumption.
  - split; intros.
    apply IHseq_proc1 in H1.
    destruct H1 as [o' [HP2 Ho']].
    apply IHseq_proc2 in HP2.
    destruct HP2 as [o'' [HP3 Ho'']].
    exists o''. split; eauto. eapply transitivity; eauto.
    apply IHseq_proc2 in H1.
    destruct H1 as [o' [HP2 Ho']].
    apply IHseq_proc1 in HP2.
    destruct HP2 as [o'' [HP3 Ho'']].
    exists o''. split; eauto. eapply transitivity; eauto.
  - split; intros; inversion H.
  - split; intros; inversion H.
  - split; intros; inversion H.
  - split; intros; inversion H1.
  - split; intros.
    + inversion H0. subst. exists o2. split; auto.
    + inversion H0. subst. exists o1. split; auto.
      apply symmetry.
      assumption.
Qed.

Lemma seq_proc_inv_def_l : forall P o r,
    P ≈p def r o -> exists o', P = def r o' /\ o ≈o o'.
Proof.
  intros.
  apply seq_proc_inv_def' in H.
  destruct H as [_ H].
  apply H. reflexivity.
Qed.  

Lemma seq_proc_inv_def_r : forall P o r,
    def r o ≈p P -> exists o', P = def r o' /\ o ≈o o'.
Proof.
  intros.
  apply seq_proc_inv_def' in H.
  destruct H as [H _].
  apply H. reflexivity.
Qed.  

Lemma seq_proc_inv_app' : forall P1 P2,
    P1 ≈p P2 ->
    (forall f r, P1 = app f r -> P2 = app f r) /\
      (forall f r, P2 = app f r -> P1 = app f r).
Proof.
  intros P1 P2 H.
  induction H.
  - split; intros; auto.
  - split; intros; subst.
    + eapply IHseq_proc; auto.
    + eapply IHseq_proc; auto.
  - split; intros.
    + eapply IHseq_proc2.
      eapply IHseq_proc1.
      auto.
    + eapply IHseq_proc1.
      eapply IHseq_proc2.
      auto.
  - split; intros; inversion H.
  - split; intros; inversion H.
  - split; intros; inversion H.
  - split; intros; inversion H1.
  - split; intros; inversion H0.
Qed.    


Lemma seq_proc_inv_app_r : forall f r P,
    app f r ≈p P -> P = app f r.
Proof.
  intros.
  apply seq_proc_inv_app' in H.
  apply H.
  reflexivity.
Qed.

Lemma seq_proc_inv_app_l : forall f r P,
    P ≈p app f r -> P = app f r.
Proof.
  intros.
  apply seq_proc_inv_app' in H.
  apply H.
  reflexivity.
Qed.

(* Well Formedness ---------------------------------------------------------- *)

(* These relations check the useage (linearity / definition) constraints as well
   as scoping of the variables.

   The type [lctxt k] defines a "linearity context" for [k] de Bruijn variables
   it maps each identifier to its "usage", i.e. the number of times it is "used"
   in the scope.

   # Unrestricted Contexts: [G]

   By convention, we use [G] (or maybe [Γ] on paper) to range over unrestricted
   identifier contexts.

    Within a given scope, each unrestricted identifer [f] must be *defined*
   (i.e. appear under a [bng]) exactly once, though it may be called an
   arbitrary number of times.  The usage for each [f] is therefore the
   number of times it is *defined* in a scope.  (We will need a separate judgment
   to determine whether a given [f] is not used at all, which will justify
   a "garbage collection" rule for unrestricted contexts.)

   # Restricted / Linear Contexts: [D]

   By convention, we use [D] (or maybe [Δ] on paper) to range over unrestricted
   identifier contexts.

   Within a given scope, each linear / restricted identifier [r] must be
   mentioned exactly twice.  (Or not mentioned at all.)  Unlike for 
   [f]'s, if [D r = 0] then there should be no occurrence of the restricted
   variable in a given scope, and we can immediately "strengthen" the
   context to discard it.
 *)

Unset Elimination Schemes.
Inductive wf_term : forall (m n:nat), lctxt m -> lctxt n -> term -> Prop :=
| wf_bag :
  forall m n
    (G : lctxt m)
    (D : lctxt n)
    m' n'
    (G' : lctxt m')
    (D' : lctxt n')
    (UG' : forall x, x < m' -> (G' x) = 1)
    (UD' : forall x, x < n' -> (D' x) = 2 \/ (D' x) = 0)
    (P : proc)
    (WFP : wf_proc (m' + m) (n' + n) (G' ⊗ G) (D' ⊗ D) P),
    wf_term m n G D (bag m' n' P)

with wf_proc : forall (m n:nat), lctxt m -> lctxt n -> proc -> Prop :=
| wf_def :
  forall m n
    (G : lctxt m)
    (D : lctxt n) (D' : lctxt n)
    (r : rvar) (HR : r < n)
    (o : oper)
    (HD : D ≡[n] (one n r) ⨥ D')
    (WFO : wf_oper m n G D' o),
    wf_proc m n G D (def r o)

| wf_app :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (f : fvar) (HF : f < m)
    (r : rvar) (HR : r < n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (one n r)),
    wf_proc m n G D (app f r)

| wf_par :
  forall m n
    (G1 G2 G : lctxt m)
    (D1 D2 D : lctxt n)
    (P1 P2 : proc)
    (WFP1 : wf_proc m n G1 D1 P1)
    (WFP2 : wf_proc m n G2 D2 P2)
    (HG : G ≡[m] (G1 ⨥ G2))
    (HD : D ≡[n] (D1 ⨥ D2))
  ,
    wf_proc m n G D (par P1 P2)
            
with wf_oper : forall (m n:nat), lctxt m -> lctxt n -> oper -> Prop :=
| wf_emp :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (zero n)),
    wf_oper m n G D emp

| wf_tup :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (r1 : rvar) (HR1 : r1 < n)
    (r2 : rvar) (HR2 : r2 < n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (one n r1 ⨥ one n r2)),
    wf_oper m n G D (tup r1 r2)

| wf_bng :
  forall m n
    (G : lctxt m) (D : lctxt n)    
    (f : fvar)
    (HF : f < m)
    (HG : G ≡[m] (one m f))
    (HD : D ≡[n] (zero n)),
    wf_oper m n G D (bng f)
            
| wf_lam :
  forall m n
    (G : lctxt m) (D : lctxt n)
    (HG : G ≡[m] (zero m))
    (HD : D ≡[n] (zero n))
    (t : term)
    (WFT : wf_term m 1 (zero m) (1[0 ↦ 1]) t),
    wf_oper m n G D (lam t).
Set Elimination Schemes.

Scheme wf_term_ind := Induction for wf_term Sort Prop
    with wf_proc_ind := Induction for wf_proc Sort Prop
                        with wf_oper_ind := Induction for wf_oper Sort Prop.

Combined Scheme wf_tpo_ind from wf_term_ind, wf_proc_ind, wf_oper_ind.

(* A helpful tactic for dealing with equivalences of existT terms that
   arise when inverting wf judgments.
 *)
Ltac existT_eq :=
      repeat match goal with 
      | [H : existT _ _ _ = existT _ _ _ |- _ ] =>
          apply Eqdep_dec.inj_pair2_eq_dec in H; [| apply Nat.eq_dec]
      end.

(* Prove that well-formedness respects structural equivalence. *)

(* It seems that the trick for this proof is to close under commutatitivy explicitly. *)
Lemma tpo_wf_seq :
  (forall t1 t2,
      t1 ≈t t2 ->
     (forall m n G D,
      wf_term m n G D t1 ->
      wf_term m n G D t2)
     /\
     (forall m n G D,
      wf_term m n G D t2 ->
      wf_term m n G D t1))
       
  /\
    (forall P1 P2,
        P1 ≈p P2 ->
        (forall m n G D,
            wf_proc m n G D P1 ->
            wf_proc m n G D P2)

        /\
          (forall m n G D,
            wf_proc m n G D P2 ->
            wf_proc m n G D P1)
    )
      
  /\
    (forall o1 o2,
        o1 ≈o o2 ->
        (forall m n G D,
            wf_oper m n G D o1 ->
            wf_oper m n G D o2)
        /\
        (forall m n G D,
            wf_oper m n G D o2 ->
            wf_oper m n G D o1)
    ).
Proof.
  apply seq_tpo_ind; intros.
  - destruct H as [HL HR].
    split; intros.
    + inversion H; subst.
      eapply wf_bag; eauto.
    + inversion H; subst.
      eapply wf_bag; eauto.
  - repeat split; intros; try assumption.
  - tauto.
  - destruct H as [HL1 HR1].
    destruct H0 as [HL2 HR2].
    split; intros.
    + eapply HL2. eapply HL1. assumption.
    + eapply HR1. eapply HR2. assumption.
  - split; intros.
    + inversion H; 
      existT_eq;
      subst.
      rewrite sum_commutative in HG. rewrite (@sum_commutative _ D1 D2) in HD.
      eapply wf_par; eauto.
    + inversion H; existT_eq; subst.
      rewrite sum_commutative in HG. rewrite (@sum_commutative _ D1 D2) in HD.
      eapply wf_par; eauto.
  - split; intros.
    + inversion H; existT_eq; subst. inversion WFP2; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      reflexivity.
      reflexivity.
      rewrite <- sum_assoc. rewrite <- HG0. assumption.
      rewrite <- sum_assoc. rewrite <- HD0. assumption.
      
    + inversion H; existT_eq; subst. inversion WFP1; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      reflexivity.
      reflexivity.
      rewrite sum_assoc. rewrite <- HG0. assumption.
      rewrite sum_assoc. rewrite <- HD0. assumption.
  - split; intros.
    + inversion H; existT_eq; subst. inversion WFP1; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      reflexivity.
      reflexivity.
      rewrite sum_assoc. rewrite <- HG0. assumption.
      rewrite sum_assoc. rewrite <- HD0. assumption.
    + inversion H; existT_eq; subst. inversion WFP2; existT_eq; subst.
      eapply wf_par; eauto.
      eapply wf_par; eauto.
      reflexivity.
      reflexivity.
      rewrite <- sum_assoc. rewrite <- HG0. assumption.
      rewrite <- sum_assoc. rewrite <- HD0. assumption.
  - destruct H as [HL1 HR1].
    destruct H0 as [HL2 HR2].
    split; intros.
    + inversion H; existT_eq; subst.
      eapply wf_par; eauto.
    + inversion H; existT_eq; subst.
      eapply wf_par; eauto.
  - destruct H as [HL HR].
    split; intros.
    + inversion H; existT_eq; subst.
      eapply wf_def; eauto.
    + inversion H; existT_eq; subst.
      eapply wf_def; eauto.
  - split; intros; auto.
  - destruct H as [HL HR].
    split; intros.
    + inversion H; existT_eq; subst.
      apply wf_lam; auto.
    + inversion H; existT_eq; subst.
      apply wf_lam; auto.
Qed.

Lemma wf_seq_term : 
  (forall t1 t2,
      t1 ≈t t2 ->
     (forall m n G D,
      wf_term m n G D t1 ->
      wf_term m n G D t2)).
Proof.
  apply tpo_wf_seq.
Qed.

Lemma wf_seq_proc :
   (forall P1 P2,
        P1 ≈p P2 ->
        (forall m n G D,
            wf_proc m n G D P1 ->
            wf_proc m n G D P2)).
Proof.
  apply tpo_wf_seq.
Qed.  

Lemma wf_seq_oper :
    (forall o1 o2,
        o1 ≈o o2 ->
        (forall m n G D,
            wf_oper m n G D o1 ->
            wf_oper m n G D o2)).
Proof.
  apply tpo_wf_seq.
Qed.  
 
Lemma tpo_equiv_wf :
  (forall m n G1 D1 t,
      wf_term m n G1 D1 t ->
      forall G2 D2,
      G1 ≡[m] G2 ->
      D1 ≡[n] D2 ->
      wf_term m n G2 D2 t)
  /\
    (forall m n G1 D1 P,
        wf_proc m n G1 D1 P ->
        forall G2 D2,
      G1 ≡[m] G2 ->
      D1 ≡[n] D2 ->
        wf_proc m n G2 D2 P)
  /\
    (forall m n G1 D1 o,
        wf_oper m n G1 D1 o ->
        forall G2 D2,
      G1 ≡[m] G2 ->
      D1 ≡[n] D2 ->
        wf_oper m n G2 D2 o).
Proof.
  apply wf_tpo_ind; intros; eauto.
  - apply wf_bag with (G' := G')(D' := D'); auto.
    apply H.
    rewrite H0. reflexivity.
    rewrite H1. reflexivity.
  - eapply wf_def; eauto.
    eapply transitivity. symmetry. apply H1. apply HD.
    apply H; auto. reflexivity.
  - eapply wf_app; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
  - eapply wf_par; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
  - eapply wf_emp; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
  - eapply wf_tup; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
  - eapply wf_bng; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
  - eapply wf_lam; eauto.
    eapply transitivity. symmetry.  eauto. eauto.
    eapply transitivity. symmetry.  eauto. eauto.
Qed.  

#[global] Instance Proper_wf_term {m n:nat}: Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> seq_term ==> iff) (wf_term m n).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply tpo_equiv_wf; eauto.
    eapply wf_seq_term; eauto.
  - symmetry in H.
    symmetry in H0.
    symmetry in H1.
    eapply tpo_equiv_wf; eauto.
    eapply wf_seq_term; eauto.
Qed.  
  

#[global] Instance Proper_wf_term_proc {m n : nat} : Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> seq_proc ==> iff) (wf_proc m n).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply tpo_equiv_wf; eauto.
    eapply wf_seq_proc; eauto.
  - symmetry in H.
    symmetry in H0.
    symmetry in H1.
    eapply tpo_equiv_wf; eauto.
    eapply wf_seq_proc; eauto.
Qed.

#[global] Instance Proper_wf_term_oper {m n : nat} : Proper ((@ctxt_eq nat m) ==> (@ctxt_eq nat n) ==> seq_oper ==> iff) (wf_oper m n).
Proof.
  repeat red; intros; subst.
  split; intros.
  - eapply tpo_equiv_wf; eauto.
    eapply wf_seq_oper; eauto.
  - symmetry in H.
    symmetry in H0.
    symmetry in H1.
    eapply tpo_equiv_wf; eauto.
    eapply wf_seq_oper; eauto.
Qed.

(* Every well formed piece of syntax is also well scoped *)
Lemma tpo_wf_ws :
  (forall m n G D t,
      wf_term m n G D t ->
      ws_term m n t)
  /\
    (forall m n G D P,
        wf_proc m n G D P ->
        ws_proc m n P)
  /\
    (forall m n G D o,
        wf_oper m n G D o ->
        ws_oper m n o).
Proof.
  apply wf_tpo_ind; intros; constructor; auto.
Qed.  


(* renaming ----------------------------------------------------------------- *)

(* The operational semantics involve renaming resource identifiers.

   Renamings, in general, are defined in [Contexts.v], but  for de Bruijn
   indices, a renaming  amounts to function that takes a variable and
   returns a variable.

   The type [ren n n'] "renames" a variable in scope [n] to be a variable
   in scope [n'].  (In general, [n] and [n'] might be different.)

   The following functions just "map" a renaming over all the occurrences
   of the (free) identifiers in a term.
*)

Import Renamings.

(* z{y/x} *)
Definition rename_var (x:var) (y:var) (z:var) :=
  if Nat.eq_dec z x then y else z.

(* Linear resource variables are only locally scoped within the bag
   of a term, so operations that rename them don't need to traverse
   nested subterms.
 *)

Definition rename_rvar_oper {n n'} (v : ren n n') (o:oper) :=
  match o with
  | emp => emp
  | tup r1 r2 => tup (v r1) (v r2)
  | bng f => bng f
  | lam t => lam t
  end.

Fixpoint rename_rvar_proc {n n'} (v : ren n n') P : proc :=
  match P with
  | def r o => def (v r) (rename_rvar_oper v o)
  | app f r => app f (v r)
  | par P1 P2 => par (rename_rvar_proc v P1) (rename_rvar_proc v P2)
  end.

(* terms don't have any free rvars to rename *)
Definition rename_rvar_term {n n'} (v : ren n n') (t : term) := t.

(* Unrestricted identifiers *are* lexically scoped in the sense
   that an identifier introduced in an outer scope might be mentioned
   in an inner, nested term (e.g. under a [lam]).  That means
   we have to "shift" renamings as we traverse through the syntax,
   ensuring that we only rename the "free" occurences.
*)

Fixpoint rename_fvar_term {m m'} (v : ren m m') (t : term) : term :=
  match t with
  | bag m'' n P => bag m'' n (rename_fvar_proc (ren_shift m'' v) P)
  end

with rename_fvar_proc {m m'} (v : ren m m') (P : proc) : proc :=
       match P with
       | def r o => def r (rename_fvar_oper v o)
       | app f r => app (v f) r
       | par P1 P2 => par (rename_fvar_proc v P1) (rename_fvar_proc v P2)
       end

with rename_fvar_oper {m m'} (v : ren m m') (o : oper) : oper :=
       match o with
       | emp => emp
       | tup r1 r2 => tup r1 r2
       | bng f => bng (v f)
       | lam t => lam (rename_fvar_term v t)
       end.

Lemma rename_rvar_oper_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (o : oper),
    rename_rvar_oper v2 (rename_rvar_oper v1 o) = @rename_rvar_oper n n'' (ren_compose v1 v2) o.
Proof.
  intros.
  destruct o; simpl; try reflexivity.
Qed.

Lemma rename_rvar_proc_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (P : proc),
    rename_rvar_proc v2 (rename_rvar_proc v1 P) = @rename_rvar_proc n n'' (ren_compose v1 v2) P.
Proof.
  intros.
  induction P; try reflexivity.
  - simpl. rewrite rename_rvar_oper_compose.
    reflexivity.
  - simpl.
    rewrite IHP1. rewrite IHP2.
    reflexivity.
Qed.

Lemma rename_fvar_compose_tpo :
  (forall (t:term),
    forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
      rename_fvar_term v2 (rename_fvar_term v1 t) = @rename_fvar_term m m'' (ren_compose v1 v2) t)
  /\
    (forall (P:proc),
      forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
        rename_fvar_proc v2 (rename_fvar_proc v1 P) = @rename_fvar_proc m m'' (ren_compose v1 v2) P)
  /\ (forall (o:oper),
      forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
        rename_fvar_oper v2 (rename_fvar_oper v1 o) = @rename_fvar_oper m m'' (ren_compose v1 v2) o).
Proof.
  apply tpo_ind; intros; try reflexivity; simpl.
  - rewrite H. rewrite ren_compose_shift. reflexivity.
  - rewrite H. reflexivity.
  - rewrite H.
    rewrite H0.
    reflexivity.
  - rewrite H.
    reflexivity.
Qed.

Lemma rename_fvar_compose_term :
    forall (t:term),
    forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
      rename_fvar_term v2 (rename_fvar_term v1 t) = @rename_fvar_term m m'' (ren_compose v1 v2) t.
Proof.
  apply rename_fvar_compose_tpo.
Qed.

Lemma rename_fvar_compose_proc :
  forall (P:proc),
  forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
    rename_fvar_proc v2 (rename_fvar_proc v1 P) = @rename_fvar_proc m m'' (ren_compose v1 v2) P.
Proof.
  apply rename_fvar_compose_tpo.
Qed.
  
Lemma rename_fvar_compose_oper : 
  forall (o:oper),
  forall m m' m'' (v1 : ren m m') (v2 : ren m' m''),
    rename_fvar_oper v2 (rename_fvar_oper v1 o) = @rename_fvar_oper m m'' (ren_compose v1 v2) o.
Proof.
  apply rename_fvar_compose_tpo.
Qed.
  

(* Renamings of linear and unrestricted variables commute with each other. *) 

Lemma rename_rvar_fvar_commute_tpo :
  (forall (t:term),
    forall m m' n n' (fv : ren m m') (rv : ren n n'),
      rename_rvar_term rv (rename_fvar_term fv t) = rename_fvar_term fv (rename_rvar_term rv t))
  /\
    (forall (P:proc),
      forall m m' n n' (fv : ren m m') (rv : ren n n'),
        rename_rvar_proc rv (rename_fvar_proc fv P) = rename_fvar_proc fv (rename_rvar_proc rv P))
  /\ (forall (o:oper),
      forall m m' n n' (fv : ren m m') (rv : ren n n'),
        rename_rvar_oper rv (rename_fvar_oper fv o) = rename_fvar_oper fv (rename_rvar_oper rv o)).
Proof.
  apply tpo_ind; intros; try reflexivity; simpl.
  - rewrite H.
    reflexivity.
  - rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Lemma rename_rvar_fvar_commute_term :
  forall (t:term),
    forall m m' n n' (fv : ren m m') (rv : ren n n'),
      rename_rvar_term rv (rename_fvar_term fv t) = rename_fvar_term fv (rename_rvar_term rv t).
Proof.
  apply rename_rvar_fvar_commute_tpo.
Qed.

Lemma rename_rvar_fvar_commute_proc :
  forall (P:proc),
      forall m m' n n' (fv : ren m m') (rv : ren n n'),
        rename_rvar_proc rv (rename_fvar_proc fv P) = rename_fvar_proc fv (rename_rvar_proc rv P).
Proof.
  apply rename_rvar_fvar_commute_tpo.
Qed.

Lemma rename_rvar_fvar_commute_oper :
  forall (o:oper),
      forall m m' n n' (fv : ren m m') (rv : ren n n'),
        rename_rvar_oper rv (rename_fvar_oper fv o) = rename_fvar_oper fv (rename_rvar_oper rv o).
Proof.
  apply rename_rvar_fvar_commute_tpo.
Qed.

  
(* Renaming by the identity does nothing. *)

Lemma rename_rvar_id_term :
  forall (t:term), forall n, rename_rvar_term (ren_id n) t = t.
Proof.
  intros. reflexivity.
Qed.

Lemma map_ren_id :
  forall (rs : list rvar)
    (n : nat)
    (HRS : Forall (fun x : nat => x < n) rs),
    map (ren_id n) rs = rs.
Proof.
  induction rs; intros; simpl; auto.
  inversion HRS. subst.
  rewrite IHrs; auto.
  unfold ren_id.
  destruct (lt_dec a n); auto.
  lia.
Qed.  
  
Lemma rename_rvar_id_oper : 
  forall (o:oper), forall m n, ws_oper m n o -> rename_rvar_oper (ren_id n) o = o.
Proof.
  intros.
  destruct o; auto.
  inversion H; subst.
  simpl. rewrite ren_id_id; auto.
  rewrite ren_id_id; auto.
Qed.  
  
Lemma rename_rvar_id_proc :
  forall (P:proc), forall m n, ws_proc m n P -> rename_rvar_proc (ren_id n) P = P.
Proof.
  intros.
  induction P; intros; auto; simpl.
  - inversion H; subst.
    erewrite rename_rvar_id_oper; eauto.
    rewrite ren_id_id; auto.
  - inversion H; subst.
    rewrite ren_id_id; auto.
  - inversion H; subst.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
Qed.
  
Lemma rename_fvar_id_tpo :
  (forall (t:term),
    forall m n, ws_term m n t -> rename_fvar_term (ren_id m) t = t)
  /\
    (forall (P:proc),
      forall m n, ws_proc m n P -> rename_fvar_proc (ren_id m) P = P)
  /\ (forall (o:oper),
      forall m n, ws_oper m n o -> rename_fvar_oper (ren_id m) o = o).
Proof.
  apply tpo_ind; intros; try reflexivity; simpl.
  - rewrite ren_shift_id.
    inversion H0; subst.
    erewrite H; eauto.
  - inversion H0; subst.
    erewrite H; eauto.
  - inversion H; subst.
    rewrite ren_id_id; auto.
  - inversion H1; subst.
    erewrite H; eauto.
    erewrite H0; eauto.
  - inversion H; subst.
    rewrite ren_id_id; auto.
  - inversion H0; subst.
    erewrite H; eauto.
Qed.
  
Lemma rename_fvar_id_term :
 forall (t:term),
 forall m n, ws_term m n t -> rename_fvar_term (ren_id m) t = t.
Proof.
  apply rename_fvar_id_tpo.
Qed.

Lemma rename_fvar_id_proc :
 forall (P:proc),
 forall m n, ws_proc m n P -> rename_fvar_proc (ren_id m) P = P.
Proof.
  apply rename_fvar_id_tpo.
Qed.

Lemma rename_fvar_id_oper :
 forall (o:oper),
 forall m n, ws_oper m n o -> rename_fvar_oper (ren_id m) o = o.
Proof.
  apply rename_fvar_id_tpo.
Qed.


(* nu equivalence -------------------------------------------------------- *)
(* The "nu-bound" variables within a bag can be permuted without affecting the
meaning of the term.

   That means that [bag m n t] is "permutation equivalent" to [be m n t'] when
   we rename the  [m] free function identifiers and [n] free resource identifiers
   up to some bijection.

*)   

Unset Elimination Schemes.
Inductive peq_term :
  forall (m n:nat) (bf : ren m m) (br : ren n n) , term -> term -> Prop :=
| peq_bag :
  forall m n m' n'
    (bf : ren m m)
    (br : ren n n)
    (bf' : ren m' m')
    (WFF' : wf_ren bf')
    (HBF' : bij_ren bf')
    (br' : ren n' n')
    (WFR' : wf_ren br')
    (HBR' : bij_ren br')
    (P  P': proc)
    (EQP : peq_proc (m' + m) (n' + n) (bij_app bf' bf) (bij_app br' br) P P')
  ,
    peq_term m n bf br (bag m' n' P) (bag m' n' P')
             
with peq_proc : forall (m n : nat) (bf : ren m m) (br : ren n n), proc -> proc -> Prop :=
| peq_def : forall m n r (HR : r < n) o o'
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br o o' ->
    peq_proc m n bf br (def r o) (def (br r) o')

| peq_app : forall m n f (HF : f < m) r (HR : r < n)
    (bf : ren m m)
    (br : ren n n),
    peq_proc m n bf br (app f r) (app (bf f) (br r))

| peq_par : forall m n P1 P1' P2 P2'
    (bf : ren m m)
    (br : ren n n),
    peq_proc m n bf br P1 P1' ->
    peq_proc m n bf br P2 P2' ->
    peq_proc m n bf br (par P1 P2) (par P1' P2')
             
with peq_oper : forall (m n : nat) (bf : ren m m) (br : ren n n), oper -> oper -> Prop :=
| peq_emp :
  forall m n
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br emp emp

| peq_tup :
  forall m n
    r1 (HR1 : r1 < n)
    r2 (HR2 : r2 < n)
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br (tup r1 r2) (tup (br r1) (br r2))

| peq_bng :
  forall m n f (HF : f < m)
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br (bng f) (bng (bf f))

| peq_lam :
  forall m n t t'
    (bf : ren m m)
    (br : ren n n),
    peq_term m 1 bf (ren_id 1) t t' ->
    peq_oper m n bf br (lam t) (lam t').
Set Elimination Schemes.

Hint Constructors peq_term peq_proc peq_oper : core.

Scheme peq_term_ind := Induction for peq_term Sort Prop
    with peq_proc_ind := Induction for peq_proc Sort Prop
                         with peq_oper_ind := Induction for peq_oper Sort Prop.

Combined Scheme peq_tpo_ind from peq_term_ind, peq_proc_ind, peq_oper_ind.

Lemma peq_compose_tpo :
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (t t' : term)
     (HT: peq_term m n bf br t t'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br)
      (bf' : ren m m) (br' : ren n n) (t'' : term)
      (WFF' : wf_ren bf') (WFR' : wf_ren br')
      (BF' : bij_ren bf') (BR' : bij_ren br')      
      (HT' : peq_term m n bf' br' t' t''),
      peq_term m n (ren_compose bf bf') (ren_compose br br') t t'')
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (P P' : proc)
     (HT: peq_proc m n bf br P P'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br)      
      (bf' : ren m m) (br' : ren n n) (P'' : proc)
      (WFF' : wf_ren bf') (WFR' : wf_ren br')
      (BF' : bij_ren bf') (BR' : bij_ren br')            
      (HT' : peq_proc m n bf' br' P' P''),
      peq_proc m n (ren_compose bf bf') (ren_compose br br') P P'')
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (o o' : oper)
     (HT: peq_oper m n bf br o o'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br)      
      (bf' : ren m m) (br' : ren n n) (o'' : oper)
      (WFF' : wf_ren bf') (WFR' : wf_ren br')
      (BF' : bij_ren bf') (BR' : bij_ren br')            
      (HT' : peq_oper m n bf' br' o' o''),
      peq_oper m n (ren_compose bf bf') (ren_compose br br') o o'').
Proof.
  apply peq_tpo_ind; intros.
  - inversion HT'.
    existT_eq. subst.
    econstructor.
    + eapply wf_ren_compose. apply WFF'. apply WFF'1.
    + apply bij_ren_compose; auto.
    + eapply wf_ren_compose. apply WFR'. apply WFR'1.
    + apply bij_ren_compose; auto.
    + rewrite <- bij_ren_app_compose; auto.
      rewrite <- bij_ren_app_compose; auto.
      apply H; auto using wf_bij_app, bij_ren_app.
  - inversion HT'.
    existT_eq. subst.
    assert ((br' (br r)) = ((ren_compose br br') r)) by reflexivity.
    rewrite H0.
    econstructor; auto.
  - inversion HT'.
    existT_eq. subst.
    assert ((bf' (bf f)) = ((ren_compose bf bf') f)) by reflexivity.
    rewrite H.
    assert ((br' (br r)) = ((ren_compose br br') r)) by reflexivity.
    rewrite H0.
    econstructor; auto.
  - inversion HT'.
    existT_eq. subst.
    econstructor; auto.
  - inversion HT'; existT_eq; subst.
    auto.
  - inversion HT'; existT_eq; subst.
    assert ((br' (br r1)) = ((ren_compose br br') r1)) by reflexivity.
    rewrite H.
    assert ((br' (br r2)) = ((ren_compose br br') r2)) by reflexivity.
    rewrite H0.
    econstructor; auto.
  - inversion HT'.
    existT_eq. subst.
    assert ((bf' (bf f)) = ((ren_compose bf bf') f)) by reflexivity.
    rewrite H.
    econstructor; auto.
  - inversion HT'.
    existT_eq. subst.
    econstructor.
    
    assert ((ren_id 1) = (ren_compose (ren_id 1) (ren_id 1))).
    { rewrite ren_compose_id_r; auto.
      apply wf_ren_id. } 
    rewrite H0.
    apply H; auto using wf_ren_id, bij_ren_id.
Qed.


Lemma peq_inv_tpo :
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (t t' : term)
     (HT: peq_term m n bf br t t'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br),
      peq_term m n (bij_inv bf BF) (bij_inv br BR) t' t)
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (P P' : proc)
     (HT: peq_proc m n bf br P P'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br),
      peq_proc m n (bij_inv bf BF) (bij_inv br BR) P' P)
  /\
  (forall (m n:nat) (bf : ren m m) (br : ren n n) (o o' : oper)
     (HT: peq_oper m n bf br o o'),
    forall (WFF : wf_ren bf) (WFR : wf_ren br)
      (BF : bij_ren bf) (BR : bij_ren br),
      peq_oper m n (bij_inv bf BF) (bij_inv br BR) o' o).
Proof.
  apply peq_tpo_ind; intros.
  - apply peq_bag with (bf' := bij_inv bf' HBF') (br' := bij_inv br' HBR').
    apply wf_bij_ren_inv.
    apply bij_inv_bij; auto.
    apply wf_bij_ren_inv.
    apply bij_inv_bij; auto.
    rewrite <- bij_inv_app 
      with (HWF1 := WFF')(HWF2 := WFF).    
    rewrite <- bij_inv_app with (HWF1 := WFR')(HWF2 := WFR).
    apply H.
    apply wf_bij_app; auto.
    apply wf_bij_app; auto.
  - assert (r = ((bij_inv br BR) (br r))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    constructor; auto.
    apply WFR; auto.
  - assert (r = ((bij_inv br BR) (br r))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H at 2.
    assert (f = ((bij_inv bf BF) (bf f))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    constructor; auto.
    apply WFF; auto.
    apply WFR; auto.
  - constructor; auto.
  - constructor; auto.
  - assert (r1 = ((bij_inv br BR) (br r1))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H at 2.
    assert (r2 = ((bij_inv br BR) (br r2))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H0 at 2.
    econstructor.
    apply WFR; auto.
    apply WFR; auto.
  - assert (f = ((bij_inv bf BF) (bf f))).
    { apply bij_ren_inv_elt; auto. }
    rewrite H at 2.
    constructor; auto.
    apply WFF; auto.
  - constructor; auto.
    rewrite <- bij_inv_id.
    apply H; auto.
    apply wf_ren_id.
Qed.    


(* As defined, renaming by the identity isn't reflexive because it requires that
   the variables mentioned are in scope.  Therefore peq defines a PER. It is
   reflexive on "well scoped" terms.  *)
Lemma peq_id_refl_tpo :
  (forall m n (t : term),
      ws_term m n t ->
      peq_term m n (ren_id m) (ren_id n) t t)
  /\ (forall m n (P : proc),
        ws_proc m n P ->
        peq_proc m n (ren_id m) (ren_id n) P P)
  /\ (forall m n (o : oper),
        ws_oper m n o ->
        peq_oper m n (ren_id m) (ren_id n) o o).
Proof.
  apply ws_tpo_ind; intros.
  - econstructor; eauto using wf_ren_id, bij_ren_id.
    rewrite bij_app_id.
    rewrite bij_app_id.
    apply H.
  - rewrite <- (ren_id_id n r) at 2; auto.
  - rewrite <- (ren_id_id m f) at 2; auto.
    rewrite <- (ren_id_id n r) at 2; auto.
  - econstructor; eauto.
  - auto.
  - rewrite <- (ren_id_id n r1) at 2; auto.
    rewrite <- (ren_id_id n r2) at 2; auto.
  - rewrite <- (ren_id_id m f) at 2; auto.
  - econstructor.
    auto.
Qed.

(* We can existentially quantify over the renamings to get a "permutation"
   equivalence on syntax directly.  These relations are what actually formed
   a partial equivalence relation (PER).
 *)

Inductive peq_t (m n : nat) (t t' : term) : Prop :=
| peq_t_intro :
  forall (bf : ren m m)
    (br : ren n n)
    (HWF : wf_ren bf)
    (HBF : bij_ren bf)
    (HWR : wf_ren br)
    (HBR : bij_ren br)
    (EQ : peq_term m n bf br t t'),
    peq_t m n t t'.

Inductive peq_p (m n : nat) (P P' : proc) : Prop :=
| peq_p_intro :
  forall (bf : ren m m)
    (br : ren n n)
    (HWF : wf_ren bf)
    (HBF : bij_ren bf)
    (HWR : wf_ren br)
    (HBR : bij_ren br)
    (EQ : peq_proc m n bf br P P'),
    peq_p m n P P'.

Inductive peq_o (m n : nat) (o o' : oper) : Prop :=
| peq_o_intro :
  forall (bf : ren m m)
    (br : ren n n)
    (HWF : wf_ren bf)
    (HBF : bij_ren bf)
    (HWR : wf_ren br)
    (HBR : bij_ren br)
    (EQ : peq_oper m n bf br o o'),
    peq_o m n o o'.


Infix "[t≡ m n ]" := (peq_t m n) (at level 55).
Infix "[p≡ m n ]" := (peq_p m n) (at level 55).
Infix "[o≡ m n ]" := (peq_o m n) (at level 55).

Lemma peq_t_refl : forall m n t,
    ws_term m n t ->
    peq_t m n t t.
Proof.
  intros.
  specialize (peq_id_refl_tpo).
  intros.
  destruct H0 as [HT _].
  specialize (HT m n t H).
  econstructor; eauto using wf_ren_id, bij_ren_id.
Qed.

Lemma peq_p_refl : forall m n P,
    ws_proc m n P ->
    peq_p m n P P.
Proof.
  intros.
  specialize (peq_id_refl_tpo).
  intros.
  destruct H0 as [_ [HP _]].
  specialize (HP m n P H).
  econstructor; eauto using wf_ren_id, bij_ren_id.
Qed.

Lemma peq_o_refl : forall m n o,
    ws_oper m n o ->
    peq_o m n o o.
Proof.
  intros.
  specialize (peq_id_refl_tpo).
  intros.
  destruct H0 as [_ [_ HO]].
  specialize (HO m n o H).
  econstructor; eauto using wf_ren_id, bij_ren_id.
Qed.


#[global] Instance Transitive_peq_term {m n} : Transitive (peq_t m n).
Proof.
  unfold Transitive.
  intros.
  inversion H.
  inversion H0.
  econstructor.
  5 : { eapply peq_compose_tpo; eauto. }
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
Qed.

#[global] Instance Transitive_peq_proc {m n} : Transitive (peq_p m n).
Proof.
  unfold Transitive.
  intros.
  inversion H.
  inversion H0.
  econstructor.
  5 : { eapply peq_compose_tpo; eauto. }
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
Qed.

#[global] Instance Transitive_peq_oper {m n} : Transitive (peq_o m n).
Proof.
  unfold Transitive.
  intros.
  inversion H.
  inversion H0.
  econstructor.
  5 : { eapply peq_compose_tpo; eauto. }
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
  apply wf_ren_compose; auto.
  apply bij_ren_compose; auto.
Qed.

#[global] Instance Symmetric_peq_term {m n} : Symmetric (peq_t m n).
Proof.
  unfold Symmetric.
  intros.
  inversion H.
  apply peq_t_intro with (bf := bij_inv bf HBF)(br := bij_inv br HBR).
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  eapply peq_inv_tpo; eauto. 
Qed.

#[global] Instance Symmetric_peq_proc {m n} : Symmetric (peq_p m n).
Proof.
  unfold Symmetric.
  intros.
  inversion H.
  apply peq_p_intro with (bf := bij_inv bf HBF)(br := bij_inv br HBR).
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  eapply peq_inv_tpo; eauto. 
Qed.

#[global] Instance Symmetric_peq_oper {m n} : Symmetric (peq_o m n).
Proof.
  unfold Symmetric.
  intros.
  inversion H.
  apply peq_o_intro with (bf := bij_inv bf HBF)(br := bij_inv br HBR).
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  apply wf_bij_ren_inv.
  apply bij_inv_bij; auto.
  eapply peq_inv_tpo; eauto. 
Qed.

Lemma map_ext_Forall_partial :
    forall A B (f g : A -> B) (l : list A) (P : A -> Prop),
    (forall x, P x -> f x = g x) ->
    Forall P l -> map f l = map g l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - inversion H0; subst.
    simpl.
    rewrite H; auto.
    rewrite IHl; auto.
Qed.    

Lemma Forall_ren_wf :
  forall n (r : ren n n) (HR: wf_ren r) (rs:list var),
    Forall (fun x => x < n) rs ->
    Forall (fun x => x < n) (map r rs).
Proof.
  intros.
  apply Forall_map.
  eapply Forall_impl.
  2 : { apply H. }
  apply HR.
Qed.  

(* Well-formedness also respects permutation equivalence, but we have to compose
   the context with the *inverse* renaming to explain how the book keeping works
   out.  *) 
Lemma peq_wf_tpo :
  (forall (m n:nat)
      (G : lctxt m)
      (D : lctxt n)
      (t1 : term), 
      wf_term m n G D t1 ->
      forall (t2 : term)
        (bf : ren m m) (br : ren n n) ,
        peq_term m n bf br t1 t2 ->
        forall (HWF : wf_ren bf)
          (HBF : bij_ren bf)
          (HWR : wf_ren br)
          (HBR : bij_ren br),
          wf_term m n
          (ren_compose (bij_inv bf HBF) G)
          (ren_compose (bij_inv br HBR) D)
          t2)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (P1 : proc), 
        wf_proc m n G D P1 ->
        forall (P2 : proc)
          (bf : ren m m) (br : ren n n) ,
          peq_proc m n bf br P1 P2 ->
          forall (HWF : wf_ren bf)
            (HBF : bij_ren bf)
            (HWR : wf_ren br)
            (HBR : bij_ren br),
            wf_proc m n
              (ren_compose (bij_inv bf HBF) G)
              (ren_compose (bij_inv br HBR) D)
              P2)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (o1 : oper), 
        wf_oper m n G D o1 ->
        forall (o2 : oper)
          (bf : ren m m) (br : ren n n) ,
          peq_oper m n bf br o1 o2 ->
          forall (HWF : wf_ren bf)
            (HBF : bij_ren bf)
            (HWR : wf_ren br)
            (HBR : bij_ren br),
            wf_oper m n
              (ren_compose (bij_inv bf HBF) G)
              (ren_compose (bij_inv br HBR) D)
              o2).
Proof.
  apply wf_tpo_ind; intros.
  - inversion H0; existT_eq; subst.
    assert (wf_ren (bij_inv bf HBF)) by apply wf_bij_ren_inv.
    assert (wf_ren (bij_inv br HBR)) by apply wf_bij_ren_inv.    
    assert (wf_ren (bij_inv bf' HBF')) by apply wf_bij_ren_inv.
    assert (wf_ren (bij_inv br' HBR')) by apply wf_bij_ren_inv.
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    assert (bij_ren (bij_inv bf' HBF')) by (apply bij_inv_bij; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (bij_ren (bij_inv br' HBR')) by (apply bij_inv_bij; auto).
    apply wf_bag with (G':=(ren_compose (bij_inv bf' HBF') G'))
                      (D':=(ren_compose (bij_inv br' HBR') D')).
    + intros.
      destruct HBF' as [bf'_inv [HBI HEQ]].
      simpl. unfold ren_compose, compose.
      assert ((bf'_inv x) < m'). { apply HBI. assumption. }
      apply UG'; auto.
    + intros.
      destruct HBR' as [br'_inv [HBR' HEQ]].
      simpl. unfold ren_compose, compose.
      assert ((br'_inv x) < n'). { apply HBR'. assumption. }
      apply UD'; auto.
    + rewrite ren_compose_app; auto.
      rewrite ren_compose_app; auto.
      rewrite bij_app_inv with (WF1 := WFF')(WF2 := HWF).
      rewrite bij_app_inv with (WF1 := WFR')(WF2 := HWR).
      apply H; auto.
      apply wf_bij_app; auto.
      apply wf_bij_app; auto.
  - inversion H0; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    eapply wf_def; eauto.
    + apply HWR; auto.
    + specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H1). intros HP.
      rewrite HD.
      rewrite ren_sum_compose.
      rewrite ren_one_compose with (H:=X); auto.
      rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
      reflexivity.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H0). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H1). intros HPF.
    rewrite HG.
    rewrite ren_one_compose with (H:=X); auto.
    rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
    rewrite ren_compose_zero.
    constructor; auto.
    apply HWF; auto.
    apply HWR; auto.
    reflexivity.
    reflexivity.
  - inversion H1; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H2). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H3). intros HPF.
    rewrite HG.
    rewrite ren_sum_compose.
    rewrite ren_sum_compose.
    econstructor; eauto.
    reflexivity.
    reflexivity.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H0). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H1). intros HPF.
    rewrite HG.
    rewrite ren_compose_zero.
    rewrite ren_compose_zero.
    constructor.
    reflexivity.
    reflexivity.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H0). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H1). intros HPF.
    rewrite HG.
    rewrite ren_sum_compose.
    rewrite ren_compose_zero.
    rewrite ren_one_compose with (H := X); auto.
    rewrite ren_one_compose with (H := X); auto.
    rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
    eapply wf_tup.
    apply HWR; auto.
    apply HWR; auto.
    reflexivity.
    reflexivity.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H0). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H1). intros HPF.
    rewrite HG.
    rewrite ren_one_compose with (H := X0); auto.
    rewrite (bij_inv_bij_inv_eq _ bf HWF HBF X0).
    rewrite ren_compose_zero.
    constructor.
    apply HWF; auto.
    reflexivity.
    reflexivity.
  - inversion H0; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    specialize (@Proper_ren_compose _ n nat (bij_inv br HBR) H1). intros HP.
    rewrite HD.
    specialize (@Proper_ren_compose _ m nat (bij_inv bf HBF) H2). intros HPF.
    rewrite HG.    
    rewrite ren_compose_zero.
    rewrite ren_compose_zero.
    constructor; auto.
    reflexivity.
    reflexivity.
    specialize (H t' bf _ H6 HWF HBF (wf_ren_id 1) (bij_ren_id 1)).
    rewrite ren_compose_zero in H.
    simpl in H.
    setoid_rewrite (ren_delta_compose _ (ren_id 1) 0 1 (wf_ren_id 1) (bij_ren_id 1)) in H; auto.
Qed.    

(* cuts *)

(* "removes" variable x from the scope, where n is the number of variables > x *)
Definition strengthen n (x:var) : ren (x + 1 + n) (x + n) :=
  fun y =>
  if lt_dec y x then y
  else (y - 1).

(* "retracts" a variable y into x:
   Makes sense when x < y
    - "merges" x and y to be just "x"

    - first rename y to x
        y + 1 + n  ~> y + 1 + n
    - then cut out y
        y + 1 + n ~>  y + n
   Here, n is the number of variables in the original scope that are > y.
 *)
Definition retract n x y : ren (y + 1 + n) (y + n) :=
  @ren_compose (y + 1 + n) (y + 1 + n) _ (rename_var y x) (strengthen n y).

Definition strengthen_rvar_oper n x o : oper :=
  rename_rvar_oper (strengthen n x) o.
  
Definition strengthen_rvar_proc n x P : proc :=
  rename_rvar_proc (strengthen n x) P.

Definition retract_rvar_proc n x y P :=
  rename_rvar_proc (retract n x y) P.


(*
Lemma wf_cut_oper :
  forall m n x c o (G : lctxt m) (Dx : lctxt x) (Dn : lctxt n),
    wf_oper m (x + 1 + n) G (Dx ⊗ 1[0 ↦ c] ⊗ Dn) o ->
    wf_oper m (x + n) G (Dx ⊗ Dn) (cut_rvar_oper n x o).
Proof.
  intros.
  inversion H; existT_eq; subst.
  - simpl.
*)




(* Fixpoint cuts n (l:list (nat * nat)) : ren (length l + n) n := *)
(*   match l with *)
(*   | [] => ren_id n *)
(*   | (x,y)::l => *)
(*       let f := cuts n l in *)
(*       let x' := f x in *)
(*       let y' := f y in *)
(*           match Nat.compare x' y' with *)
(*           | Lt => ren_compose f (retract n x' y') *)
(*           | Eq => ren_compose f (cut n x') *)
(*           | Gt => ren_compose f (retract n y' x') *)
(*       end *)
(*   end. *)

(* Operational Semantics --------------------------------------------------- *)

Import ListNotations.
Example ex_P0 : proc :=
  (par (def 3 (tup 2 2)))
     (def 1 (tup 4 4)).

Example ex_P : proc :=
  par (def 0 (tup 1 2))
    (par (def 0 (tup 3 4))
       ex_P0).

Eval compute in retract_rvar_proc 1 1 3 ex_P0.

Definition ren_f_extrude m m' : ren (m + m') (m' + m) :=
  fun x =>
    if lt_dec x m' then x + m else (x - m').

Definition scope_extrude m m' n n' Q :=
    let Q1 := @rename_rvar_proc n (n' + n) (fun x => n + x) Q in
    let Q2 := @rename_fvar_proc (m + m') (m' + m) (ren_f_extrude m m') Q1 in
    Q2.


Lemma wf_prim_step_emp :
  forall m m' n n' r P (G : lctxt m),
    wf_term m n G (zero n) (bag m' n' (par P (par (def r emp) (def r emp)))) ->
    wf_term m n G (zero n) (bag m' n' P).
Proof.
  intros.
  inversion H; existT_eq; subst; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP3; existT_eq; subst; clear WFP3.
  inversion WFO; existT_eq; subst; clear WFO.
  inversion WFO0; existT_eq; subst; clear WFO0.
  
  rewrite HG1 in HG0; clear HG1.
  rewrite HG2 in HG0; clear HG2.
  rewrite sum_zero_r in HG0.
  rewrite HG0 in HG; clear HG0.
  rewrite sum_zero_r in HG.
  rewrite <- HG in WFP1; clear HG.
  rewrite HD4 in HD2; clear HD4.
  rewrite sum_zero_r in HD2.
  rewrite HD2 in HD0; clear HD2.
  rewrite HD3 in HD1; clear HD3.
  rewrite sum_zero_r in HD1.
  rewrite HD1 in HD0; clear HD1.
  unfold one in HD0.
  rewrite delta_sum in HD0. simpl in HD0.
  rewrite HD0 in HD; clear HD0.
  apply sum_app_inv_ctxt in HD.
  destruct HD as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
  assert (DB1 ≡[n] zero n). { apply sum_zero_inv_l_eq in EQ4. assumption. } 
  assert (DB2 ≡[n] zero n). { apply sum_zero_inv_r_eq in EQ4. assumption. }
  clear EQ4.
  rewrite H in EQ1; clear H.
  rewrite H0 in EQ2; clear H0.
  rewrite EQ1 in WFP1.
  eapply wf_bag.
  3 : { apply WFP1.  }
  auto.
  apply app_delta_zero_inv_ctxt in EQ2; auto.
  rewrite <- EQ2 in EQ3; clear EQ2.
  intros x HX.
  specialize (UD' x HX).
  destruct (Nat.eq_dec x r).
  - subst.
    specialize (EQ3 _ HX).
    unfold sum in EQ3.
    rewrite delta_id in EQ3; auto.
    lia.
  - specialize (EQ3 _ HX).
    unfold sum in EQ3.
    rewrite delta_neq in EQ3; auto.
    lia.
Qed.    
                     
Lemma ctxt_eq_imp :
  forall n X (c : ctxt n X) (d : ctxt n X) (P : X -> Prop),
    c ≡[n] d ->
    forall x, x < n -> P (c x) -> P (d x).
Proof.
  unfold ctxt_eq.
  intros.
  rewrite <- H; auto.
Qed.  

Lemma ctxt_app_c_zero_inv : forall n' n (c : lctxt n') r r1 r1' r2 r2',
    r < n' + n ->
    r1 < n' + n ->
    r1' < n' + n ->
    r2 < n' + n ->
    r2' < n' + n ->
 c ⊗ zero n
   ≡[ n' + n] (n' + n) [r ↦ 2] ⨥ (one (n' + n) r1 ⨥ (one (n' + n) r1' ⨥ (one (n' + n) r2 ⨥ one (n' + n) r2')))
 ->
   (r < n') /\ (r1 < n') /\ (r1' < n') /\ (r2 < n') /\ (r2' < n').
Proof.
  unfold ctxt_app, zero, one, delta, sum, ctxt_eq.
  intros.
  repeat match goal with
         | [ H: context[lt_dec ?R1 ?R2] |- _ ] => destruct (lt_dec R1 R2); try lia
         end.
  apply H4 in H.
  apply H4 in H0.
  apply H4 in H1.
  apply H4 in H2.
  apply H4 in H3.
  clear H4.
  repeat split;
  repeat match goal with
         | [ H: context[Nat.eq_dec ?R1 ?R1] |- _ ] => destruct (Nat.eq_dec R1 R1); subst; try lia
    end.
  - destruct (lt_dec r n'); try lia.
  - destruct (lt_dec r1 n'); try lia.
  - destruct (lt_dec r1' n'); try lia.
  - destruct (lt_dec r2 n'); try lia.
  - destruct (lt_dec r2' n'); try lia.    
Qed.  

Lemma zero_delta_0 :
  forall n x, zero n ⨥ n[x ↦ 0] ≡[n] zero n.
  intros.
  unfold zero, delta, sum, ctxt_eq.
  intros.
  destruct (lt_dec x n); try lia.
  destruct (Nat.eq_dec x x0); try lia.
Qed.  

Ltac lia_destruct :=
  repeat match goal with
    | [ H: context[lt_dec ?R1 ?R2] |- _ ] => destruct (lt_dec R1 R2); try lia
    end;
  repeat match goal with
    | [ H: context[Nat.eq_dec ?R1 ?R2] |- _ ] => destruct (Nat.eq_dec R1 R2); subst; try lia
    end.

Ltac lia_goal :=
  repeat match goal with
    | [ |- context[lt_dec ?R1 ?R2] ] => destruct (lt_dec R1 R2); try lia
    | [ |- context[Nat.eq_dec ?R1 ?R2] ] => destruct (Nat.eq_dec R1 R2); try lia
    end.


Lemma wf_oper_rename_rvar :
  forall m n G D o,
    wf_oper m n G D o ->
    forall D1 D2  r r' cr cr'
      (HR: r < n)
      (HR' : r' < n)
      (HDR : D1 r = 0)
      (HDR' : D1 r' = 0)
      (HNEQ : r <> r')
      (HD1 : D ≡[n] D1 ⨥ (n[r ↦ cr]) ⨥ (n[r' ↦ cr']))
      (HD2 : D2 ≡[n] D1 ⨥ (n[r' ↦ cr + cr'])),
      wf_oper m n G D2 (@rename_rvar_oper n n(rename_var r r') o).
Proof.
  intros.
  inversion H; existT_eq; subst; simpl.
  - rewrite HD in HD1.
    rewrite <- sum_assoc in HD1.
    symmetry in HD1.
    specialize (sum_zero_inv_l_eq _ _ _ HD1).
    intros.
    specialize (sum_zero_inv_r_eq _ _ _ HD1).
    intros.
    assert (cr = 0 /\ cr' = 0). {
      pose proof (H1 _ HR) as HA.
      pose proof (H1 _ HR') as HB.
      unfold sum, delta, zero in HA, HB.
      lia_destruct.
    }
    destruct H2; subst.
    rewrite H0 in HD2.
    rewrite zero_delta_0 in HD2.
    apply wf_emp; auto.
  - unfold rename_var.
    rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    destruct (Nat.eq_dec r1 r); destruct (Nat.eq_dec r2 r); subst.
    + assert (D2 ≡[n] (one n r') ⨥ (one n r')). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2. clear HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r') ⨥ (one n r2)). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r1) ⨥ (one n r')). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
    + assert (D2 ≡[n] (one n r1) ⨥ (one n r2)). {
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        rewrite HD2.
        unfold ctxt_eq, one, delta, sum in *.
        lia_destruct.
      }
      apply wf_tup; auto.
  - rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    assert (D2 ≡[n] zero n). { 
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        unfold ctxt_eq, one, delta, sum, zero in *.
        lia_destruct.
    }
    apply wf_bng; auto.
  - rewrite HD in HD1. clear HD.
    pose proof (HD1 _ HR) as HA.
    pose proof (HD1 _ HR') as HB.
    assert (D2 ≡[n] zero n). { 
        unfold ctxt_eq.
        intros x HX.
        specialize (HD1 _ HX).
        specialize (HD2 _ HX).
        unfold ctxt_eq, one, delta, sum, zero in *.
        lia_destruct.
    }
    apply wf_lam; auto.
Qed.


Lemma lctxt_subtract : forall n c r,
    r < n ->
    c r > 0 ->
    exists d, c ≡[n] (one n r) ⨥ d.
Proof.
  intros.
  exists (fun x => if Nat.eq_dec r x then (c r - 1) else c x).
  unfold ctxt_eq.
  intros.
  unfold one, delta, sum.
  destruct (lt_dec r n); try lia.
  destruct (Nat.eq_dec r x); subst; try lia.
Qed.

Lemma sum_inv_l : forall n (c d1 d2 : lctxt n),
    c ⨥ d1 ≡[n] c ⨥ d2 ->
    d1 ≡[n] d2.
Proof.
  unfold ctxt_eq, sum.
  intros.
  specialize (H _ H0).
  lia.
Qed.  

Lemma lctxt_sum_inv_two :
  forall n
   (D1 : lctxt n)
   (r r' cr cr' : nat)
   (HR : r < n)
   (HR' : r' < n)
   (HDR : D1 r = 0)
   (HDR' : D1 r' = 0)
   (HNEQ : r <> r')
   (D0 D3 : lctxt n)
   (HD1 : D0 ⨥ D3 ≡[ n] (D1 ⨥ n [r ↦ cr]) ⨥ n [r' ↦ cr']),
    exists D0' D3',
    D1 ≡[n] D0' ⨥ D3' /\
      (D0 ≡[n] D0' ⨥ n[r ↦ D0 r] ⨥ n[r' ↦ D0 r']) /\
      (D3 ≡[n] D3' ⨥ n[r ↦ D3 r] ⨥ n[r' ↦ D3 r']) /\
      (D0 r + D3 r = cr) /\ (D0 r' + D3 r' = cr') /\
      (D0' r = 0) /\ (D0' r' = 0) /\ (D3' r = 0) /\ (D3' r' = 0).
Proof.
  intros.
  exists (fun x => if Nat.eq_dec x r then 0 else if Nat.eq_dec x r' then 0 else  D1 x - D3 x).
  exists (fun x => if Nat.eq_dec x r then 0 else if Nat.eq_dec x r' then 0 else  D1 x - D0 x).
  split.
  - unfold ctxt_eq.
    intros.
    pose proof (HD1 _ HR).
    pose proof (HD1 _ HR').
    pose proof (HD1 _ H).
    clear HD1.
    unfold sum, delta in *.
    destruct (Nat.eq_dec x r); try lia_destruct; try lia.
    destruct (Nat.eq_dec x r'); lia_destruct; try lia.
  - split.
    +  unfold ctxt_eq.
       intros.
       pose proof (HD1 _ HR).
       pose proof (HD1 _ HR').
       pose proof (HD1 _ H).
       clear HD1.
       unfold sum, delta in *.
       destruct (Nat.eq_dec x r); try lia_destruct; try lia.
       destruct (Nat.eq_dec x r'); try lia.
    + split.
      * unfold ctxt_eq.
        intros.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H).
        clear HD1.
        unfold sum, delta in *.
        destruct (Nat.eq_dec x r); try lia_destruct; try lia.
        destruct (Nat.eq_dec x r'); try lia.
      * pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        clear HD1.
        unfold sum, delta in *.
        destruct (Nat.eq_dec r r); try lia_destruct; try lia.
Qed.

Lemma wf_proc_rename_rvar :
  forall m n G D P,
    wf_proc m n G D P ->
    forall D1 D2  r r' cr cr'
      (HR: r < n)
      (HR' : r' < n)
      (HDR : D1 r = 0)
      (HDR' : D1 r' = 0)
      (HNEQ : r <> r')
      (HD1 : D ≡[n] D1 ⨥ (n[r ↦ cr]) ⨥ (n[r' ↦ cr']))
      (HD2 : D2 ≡[n] D1 ⨥ (n[r' ↦ cr + cr'])),
      wf_proc m n G D2 (@rename_rvar_proc n n(rename_var r r') P).
Proof.
  intros m n G D P. revert m n G D.
  induction P; intros; inversion H; existT_eq; subst; simpl.
  - unfold rename_var at 1.
    destruct (Nat.eq_dec r r0); subst.
    + rewrite HD in HD1.
      assert (D' ≡[n] (D1 ⨥ n[r0 ↦ (cr - 1)] ⨥ n[r' ↦ cr'])). {
        unfold ctxt_eq, sum, delta. intros.
        pose proof (HD1 _ H0).
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        unfold ctxt_eq, sum, one, delta in H1, H2, H3.
        lia_destruct.
      }
      assert (cr > 0). {
        specialize (HD1 _ HR).
        unfold ctxt_eq, sum, one, delta in HD1.
        lia_destruct.
      }
      assert (D2 ≡[n] (one n r') ⨥ (D1 ⨥ n[r' ↦ (cr - 1) + cr'])). {
        unfold ctxt_eq, sum, one, delta. intros.
        pose proof (HD2 _ H2).
        pose proof (HD2 _ HR).
        pose proof (HD2 _ HR').
        unfold ctxt_eq, sum, one, delta in H3, H4, H5.
        lia_destruct.
      } 
      eapply wf_def; eauto.
      eapply wf_oper_rename_rvar; eauto.
      reflexivity.
    + rewrite HD in HD1.
      destruct (Nat.eq_dec r r'); subst; auto.
      * assert (D' ≡[n] (D1 ⨥ n[r0 ↦ cr] ⨥ n[r' ↦ (cr' - 1)])). {
          unfold ctxt_eq, sum, delta. intros.
          pose proof (HD1 _ H0).
          pose proof (HD1 _ HR).
          pose proof (HD1 _ HR').
          unfold ctxt_eq, sum, one, delta in H1, H2, H3.
          lia_destruct.
        }
        assert (cr' > 0). {
          specialize (HD1 _ HR').
          unfold ctxt_eq, sum, one, delta in HD1.
          lia_destruct.
        }
        assert (D2 ≡[n] (one n r') ⨥ (D1 ⨥ n[r' ↦ cr + (cr' - 1)])). {
          unfold ctxt_eq, sum, one, delta. intros.
          pose proof (HD2 _ H2).
          pose proof (HD2 _ HR).
          pose proof (HD2 _ HR').
          unfold ctxt_eq, sum, one, delta in H3, H4, H5.
          lia_destruct.
        } 
        eapply wf_def; eauto.
        eapply wf_oper_rename_rvar; eauto.
        reflexivity.
      * assert (D1 r > 0). {
          pose proof (HD1 _ HR0).
          unfold ctxt_eq, sum, one, delta in H0.
          lia_destruct.
        }
        pose proof (lctxt_subtract _ _ _ HR0 H0).
        destruct H1 as (D1' & HD1').
        rewrite HD1' in HD2.
        repeat rewrite <- sum_assoc in HD2.
        rewrite HD1' in HD1.
        repeat rewrite <- sum_assoc in HD1.
        apply sum_inv_l in HD1.
        rewrite  sum_assoc in HD1.
        eapply wf_def; eauto.
        eapply wf_oper_rename_rvar with (D:=D')(D1:=D1'); eauto; try reflexivity.
        -- specialize (HD1' _ HR).
           unfold one, delta, sum in HD1'.
           lia_destruct.
        -- specialize (HD1' _ HR').
           unfold one, delta, sum in HD1'.
           lia_destruct.
  - unfold rename_var.
    rewrite HD in HD1; clear HD.
    destruct (Nat.eq_dec r r0); subst.
    + assert (D2 ≡[n] (one n r')). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
    + destruct (Nat.eq_dec r r'); subst.
      * assert (D2 ≡[n] (one n r')). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
      * assert (D2 ≡[n] (one n r)). {
        unfold ctxt_eq, one, delta. intros.
        pose proof (HD2 _ H0).
        rewrite H1; clear H1.
        pose proof (HD1 _ HR).
        pose proof (HD1 _ HR').
        pose proof (HD1 _ H0).
        unfold one, sum, delta.
        unfold one, sum, delta in H1, H2, H3.
        lia_destruct.
      }
      apply wf_app; eauto.
  - rewrite HD in HD1.
    apply lctxt_sum_inv_two in HD1; auto.
    destruct HD1 as (D0' & D3' & EQ1 & EQ2 & EQ3 & HS1 & HS2 & HS3 & HS4 & HS5 & HS6).
    rewrite EQ2 in WFP1.
    rewrite EQ3 in WFP2.
    rewrite EQ1 in HD2.

    assert (D2 ≡[n] (D0' ⨥ n[r' ↦ D0 r + D0 r']) ⨥ (D3' ⨥ n[r' ↦ D3 r + D3 r'])). {
      repeat rewrite <- sum_assoc.
      rewrite (@sum_assoc _ n [r' ↦ D0 r + D0 r']).
      rewrite (@sum_commutative _ _ D3').
      repeat rewrite <- sum_assoc.
      rewrite delta_sum.
      assert ((D0 r + D0 r' + (D3 r + D3 r')) = cr + cr') by lia.
      rewrite H0.
      rewrite HD2.
      repeat rewrite <- sum_assoc.
      reflexivity.
    }
    rewrite H0.
    eapply wf_par with (G1 := G1)(G2 :=G2); auto.
    3 : { reflexivity. }
    + eapply IHP1; auto.
      apply WFP1.
      4 : { reflexivity. }
      auto.
      auto.
      reflexivity.
    + eapply IHP2; auto.
      apply WFP2.
      4 : { reflexivity. }
      auto.
      auto.
      reflexivity.
Qed.

Lemma ctxt_app_assoc_zero :
  forall (j k l : nat) 
         (J : lctxt j)
         (K : lctxt k),
  (@ctxt_app _ (j + k) l (@ctxt_app _ j k J K) (zero l)) =
  (@ctxt_app _ j (k + l)  J (@ctxt_app _ k l K (zero l))).
Proof. 
  intros. 
  unfold ctxt_app. 
  apply functional_extensionality. 
  intros x.
  destruct (lt_dec x (j + k)); try lia.
  destruct (lt_dec x j); try lia.
  destruct (lt_dec (x - j) k); try lia.
  destruct (lt_dec x j); try lia.
  destruct (lt_dec (x - j) k); try lia.
  unfold zero; lia.
Qed.

Lemma ctxt_app_zero_zero :
  forall (n m : nat),
  (@ctxt_app _ n m (zero n) (zero m)) ≡[n + m]
  (zero (n + m)).
Proof.
  intros.
  unfold zero, ctxt_app.
  intros x Hx. 
  destruct (lt_dec x n); try lia.
Qed.

Lemma wf_app_zero :
  (forall (m n : nat)
      (G : lctxt m)
      (D : lctxt n)
      (t : term), 
      wf_term m n G D t ->
      forall (m' n' : nat),
        wf_term (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) t)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (P : proc), 
        wf_proc m n G D P ->
        forall (m' n' : nat),
          wf_proc (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) P)
  /\ (forall (m n:nat)
       (G : lctxt m)
       (D : lctxt n)
       (o : oper), 
        wf_oper m n G D o ->
        forall (m' n' : nat),
          wf_oper (m + m') (n + n') 
          (@ctxt_app _ m m' G (zero m'))
          (@ctxt_app _ n n' D (zero n')) o).
Proof.
apply wf_tpo_ind; intros.
- eapply wf_bag with (G':= G') (D' := D').
  assumption. assumption.
  assert ((@ctxt_app _ m' (m + m'0) G' (G ⊗ (zero m'0))) = 
          (@ctxt_app _ (m' + m) m'0 (G' ⊗ G) (zero m'0))).
  { symmetry; apply ctxt_app_assoc_zero. }
  rewrite H0; clear H0.
  assert ((@ctxt_app _ n' (n + n'0) D' (D ⊗ (zero n'0))) = 
          (@ctxt_app _ (n' + n) n'0 (D' ⊗ D) (zero n'0))).
  { symmetry; apply ctxt_app_assoc_zero. }
  rewrite H0; clear H0.
  specialize (H m'0 n'0).
  replace (m' + (m + m'0)) with (m' + m + m'0) by lia.
  replace (n' + (n + n'0)) with (n' + n + n'0) by lia.
  assumption.
- rewrite HD. 
  assert ((@ctxt_app _ n n' (one n r ⨥ D') (zero n')) = 
          ((@ctxt_app _ n n' (one n r) (zero n')) ⨥ (@ctxt_app _ n n' D' (zero n')))).
  { assert ((zero n') = (zero n') ⨥ (zero n')) by (symmetry; apply sum_zero_l). 
    rewrite H0 at 1.
    symmetry; apply lctxt_sum_app_dist. }
  rewrite H0; clear H0. 
  eapply wf_def; eauto; try lia.
  unfold ctxt_app, sum, one, zero, delta.
  intros x Hx. destruction.
- eapply wf_app; try lia. 
  rewrite HG. unfold zero, ctxt_app.
  intros x Hx. destruct (lt_dec x m); try lia.
  rewrite HD. unfold one, zero, ctxt_app, delta.
  intros x Hx. destruction.
- rewrite HG, HD. 
  assert ((@ctxt_app _ m m' (G1 ⨥ G2) (zero m')) = 
          (@ctxt_app _ m m' G1 (zero m')) ⨥ (@ctxt_app _ m m' G2 (zero m'))).
  symmetry; apply lctxt_sum_app_dist. rewrite H1; clear H1.
  assert ((@ctxt_app _ n n' (D1 ⨥ D2) (zero n')) = 
          (@ctxt_app _ n n' D1 (zero n')) ⨥ (@ctxt_app _ n n' D2 (zero n'))).
  symmetry; apply lctxt_sum_app_dist. rewrite H1; clear H1.
  eapply wf_par with (G1 := (@ctxt_app _ m m' G1 (zero m')))
                     (G2 := (@ctxt_app _ m m' G2 (zero m'))) 
                     (D1 := (@ctxt_app _ n n' D1 (zero n')))
                     (D2 := (@ctxt_app _ n n' D2 (zero n'))).
  specialize (H m' n'); try assumption.
  specialize (H0 m' n'); try assumption.
  apply refl_ctxt_eq. apply refl_ctxt_eq.
- rewrite HG, HD. apply wf_emp. 
  apply ctxt_app_zero_zero.
  unfold zero, ctxt_app. intros x Hx. destruct (lt_dec x n); try lia.
- rewrite HG, HD. apply wf_tup; try lia.
  apply ctxt_app_zero_zero.
  assert ((@ctxt_app _ n n' (one n r1 ⨥ one n r2) (zero n')) = 
          ((@ctxt_app _ n n' (one n r1) (zero n')) ⨥ (@ctxt_app _ n n' (one n r2) (zero n'))))
  by (symmetry; apply lctxt_sum_app_dist). rewrite H; clear H.
  unfold zero, ctxt_app, one, sum, delta. 
  intros x Hx. destruction.
- rewrite HG, HD. apply wf_bng; try lia.
  unfold one, ctxt_app, zero, delta.
  intros x Hx. destruction.  
  unfold zero, ctxt_app. 
  intros x Hx. destruction.
- rewrite HG, HD. apply wf_lam. 
  apply ctxt_app_zero_zero.
  apply ctxt_app_zero_zero.
  specialize (H m' 0).
  assert ((@ctxt_app _ 1 0 (1 [0 ↦ 1]) (zero 0) = 1 [0 ↦ 1])).
  unfold delta, ctxt_app, zero. apply functional_extensionality.
  intros x. destruction.
  rewrite H0 in H; clear H0. simpl in H.
  assert ((zero m ⊗ zero m') ≡[m + m'] (zero (m + m'))) by (apply ctxt_app_zero_zero).
  rewrite H0 in H; clear H0; try assumption.
Qed.

Lemma wf_scope_extrude :
  forall m m' n n' (G : lctxt m') (D : lctxt n') Q,
   wf_proc (m' + m) n' (G ⊗ zero m) D Q ->
   wf_proc (m + m') (n + n') (zero m ⊗ G) (zero n ⊗ D) (scope_extrude m m' n n' Q).
Proof.

Admitted.


Lemma wf_prim_step_app :
  forall m m' m'' n n' n'' r r' f P Q (G : lctxt m),
    wf_term m n G (zero n) (bag m' n'
                            (par P
                                (par (def r (lam (bag m'' n'' Q)))
                                     (par (def r (bng f))
                                          (app f r'))))) ->
    wf_term m n G (zero n) (bag (m' + m'') (n' + n'')
                            (par P
                                (par (def r (lam (bag m'' n'' Q)))
                                     (par (def r (bng f))
                                          (@rename_rvar_proc m'' (m' + m'') 
                                            (rename_var (n'+ n'') r') 
                                            (scope_extrude m' m'' n' n'' Q)))))).
Proof.
  intros.
  inversion H; existT_eq; subst; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP3; existT_eq; subst; clear WFP3.
  inversion WFO; existT_eq; subst; clear WFO.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFT; existT_eq; subst; clear WFT.

  rewrite HG2 in HG0; clear HG2.
  rewrite sum_zero_l in HG0.
  rewrite HD3 in HD1; clear HD3.
  rewrite sum_zero_r in HD1.
  rewrite HG3 in HG1; clear HG3.
  rewrite sum_zero_r in HG1.
  rewrite HG1 in HG0; clear HG1.
  rewrite HG0 in HG; clear HG0.
  rewrite HD4 in HD2; clear HD4.
  rewrite HD5 in HD2; clear HD5. 
  rewrite HD2 in HD0; clear HD2.
  rewrite HD1 in HD0; clear HD1.
  rewrite HD0 in HD; clear HD0.

  unfold one in HD.

  (* --------------------------------------------------------------------------------------------------- *)
  eapply wf_bag with (G := G) (D := (zero n))  (G' := G')(D' := D').
  
  3 : { 
    eapply wf_par with (G1 := G1) (G2 := G4) (D1 := D1) 
                       (D2 := ((n' + n) [r ↦ 1] ⨥ (((n' + n) [r ↦ 1] ⨥ D'1) ⨥ (n' + n) [r' ↦ 1]))).
   
  apply wf_lam. 

  }

Admitted. 


Lemma wf_prim_step_tup :
  forall m m' n n' r r1 r2 r1' r2' P (G : lctxt m),
    wf_term m n G (zero n) (bag m' n' (par P (par (def r (tup r1 r2)) (def r (tup r1' r2'))))) ->
    wf_term m n G (zero n) (bag m' n' (rename_rvar_proc (cut_renaming (n' + n) r1 r2 r1' r2') P)).
Proof.
  intros.
  inversion H; existT_eq; subst; clear H.
  inversion WFP; existT_eq; subst; clear WFP.
  inversion WFP2; existT_eq; subst; clear WFP2.
  inversion WFP0; existT_eq; subst; clear WFP0.
  inversion WFP3; existT_eq; subst; clear WFP3.
  inversion WFO; existT_eq; subst; clear WFO.
  inversion WFO0; existT_eq; subst; clear WFO0.
  rewrite HG1 in HG0; clear HG1.
  rewrite HG2 in HG0; clear HG2.
  rewrite sum_zero_r in HG0.
  rewrite HG0 in HG; clear HG0.
  rewrite sum_zero_r in HG.
  rewrite HD1 in HD0; clear HD1.
  rewrite HD2 in HD0; clear HD2.
  rewrite <- sum_assoc in HD0.
  rewrite (@sum_assoc _ D'0) in HD0.
  rewrite (@sum_commutative _ D'0) in HD0.
  do 2 rewrite sum_assoc in HD0.
  unfold one in HD0.
  rewrite delta_sum in HD0. simpl in HD0.
  apply sum_app_inv_ctxt in HD.
  destruct HD as (DA1 & DA2 & DB1 & DB2 & EQ1 & EQ2 & EQ3 & EQ4).
  rewrite EQ2 in HD0.
  assert (DB1 ≡[n] zero n). { apply sum_zero_inv_l_eq in EQ4. assumption. }
  assert (DB2 ≡[n] zero n). { apply sum_zero_inv_r_eq in EQ4. assumption. }
  clear EQ4.
  rewrite H in EQ1; clear H.
  rewrite H0 in EQ2, HD0; clear H0.

  rewrite HD3 in HD0; clear HD3.
  rewrite HD4 in HD0; clear HD4.

  repeat rewrite <- sum_assoc in HD0.
  rewrite (@sum_assoc _ (one (n' + n) r2)) in HD0.
  rewrite (@sum_commutative _ (one (n' + n) r2)) in HD0.
  rewrite <- sum_assoc in HD0.

   
  assert (   (r < n') /\ (r1 < n') /\ (r1' < n') /\ (r2 < n') /\ (r2' < n')).
  { eapply ctxt_app_c_zero_inv; eauto. }
  destruct H as (HR0' & HR1' & HR2' & HR3' & HR4').

  
  symmetry in EQ3.
  assert (forall x, x < n' -> (DA1 ⨥ DA2) x = 2 \/ (DA1 ⨥ DA2) x = 0).
  { intros. eapply (@ctxt_eq_imp _ nat _ _ (fun z => z = 2 \/ z = 0) EQ3); eauto. }

  
  rewrite <- HG in WFP1. clear HG.
  rewrite EQ1 in WFP1.  clear EQ1. 

  assert (
      DA2 ≡[n']
        n' [r ↦ 2] ⨥ (one n' r1 ⨥ (one n' r1' ⨥ (one n' r2 ⨥ one n' r2')))).
  { unfold ctxt_eq.  intros x HX.
    assert (x < n' + n) by lia.
    specialize (HD0 x H0).
    unfold ctxt_app, sum, one, delta, zero in HD0.
    unfold sum, one, delta.
    destruct (lt_dec x n'); try lia.
    rewrite HD0.
    clear HD0.
    lia_goal.
  } 

  assert ( r <> r1 /\ r <> r1' /\ r <> r2 /\ r <> r2' ) as HNEQ.
  { pose proof (H _ HR0').
    pose proof (H _ HR1').
    pose proof (H _ HR2').
    pose proof (H _ HR3').
    pose proof (H _ HR4').
    pose proof (H0 _ HR0').
    pose proof (H0 _ HR1').
    pose proof (H0 _ HR2').
    pose proof (H0 _ HR3').
    pose proof (H0 _ HR4').
    clear EQ2 EQ3 HD0 HD0 H H0.
    unfold one, delta, sum in *.
    lctxt_solve.
  } 

  unfold cut_renaming.

  destruct (Nat.eq_dec r1 r1'); subst.
  - destruct (Nat.eq_dec r2 r2'); subst.
    * apply wf_bag with (G' := G')(D' := DA1); auto.
      -- intros.
         specialize (H _ H1).
         specialize (H0 _ H1).
         unfold sum, one, delta in H, H0.
         lia_destruct.
      -- rewrite rename_rvar_id_proc with (m := (m'+m)).
         assumption.
         eapply tpo_wf_ws; eauto.
    * assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r1' then 0 else
                         if Nat.eq_dec z r2 then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r2 ↦ 1])
                ⨥ ((n' + n)[r2' ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        unfold ctxt_app, zero, sum, one, delta.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR3').
        pose proof (H _ HR4').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR3').
        pose proof (H0 _ HR4').
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lia_goal.
      }
      apply wf_bag with (G':=G')(D':=
                                   ((fun z : var =>
                                       if lt_dec z n' then
                                         if Nat.eq_dec z r then 0 else
                                           if Nat.eq_dec z r1' then 0 else
                                             if Nat.eq_dec z r2 then 0 else
                                               if Nat.eq_dec z r2' then 0 else DA1 z
                                       else 0)
                                      ⨥ (n' + n) [r2' ↦ 1+1])
                        ).
      -- auto.
      -- unfold sum, delta.
         intros.
         lia_goal.
         specialize (H _ H2).
         specialize (H0 _ H2).
         assert (x < (n' + n)) by lia.
         specialize (H1 _ H3).
         unfold sum, one, delta in H, H0, H1.
         lctxt_solve.
      -- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
         unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
         lctxt_solve.
  - destruct (Nat.eq_dec r2 r2'); subst.
    + assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r1 then 0 else
                         if Nat.eq_dec z r1' then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1 ↦ 1])
                ⨥ ((n' + n)[r1' ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR2').        
        pose proof (H _ HR3').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR2').        
        pose proof (H0 _ HR3').
        unfold ctxt_app, zero, sum, one, delta.
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
      }
      apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r1' then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r1' ↦ 2]).
      -- auto.
      -- unfold sum, delta.
         intros.
         lia_goal.
         specialize (H _ H2).
         specialize (H0 _ H2).
         assert (x < (n' + n)) by lia.
         specialize (H1 _ H3).
         unfold sum, one, delta in H, H0, H1.
         lctxt_solve.
      -- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
         unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
         lctxt_solve.
    + destruct (Nat.eq_dec r1 r2); subst.
      * destruct (Nat.eq_dec r1' r2'); subst.
        -- apply wf_bag with (G' := G')(D' := DA1); auto.
           ++ intros.
              specialize (H _ H1).
              specialize (H0 _ H1).
              unfold sum, one, delta in H, H0.
              lia_destruct.
           ++ rewrite rename_rvar_id_proc with (m := (m'+m)).
              assumption.
              eapply tpo_wf_ws; eauto.
        -- assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r2 then 0 else
                         if Nat.eq_dec z r1' then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1' ↦ 1])
                ⨥ ((n' + n)[r2' ↦ 1])
             ).
           
           { unfold ctxt_eq.
             intros.
             pose proof (H _ HR0').
             pose proof (H _ HR1').
             pose proof (H _ HR2').        
             pose proof (H _ HR4').
             pose proof (HD0 _ H1).
             pose proof (H0 _ HR0').
             pose proof (H0 _ HR1').
             pose proof (H0 _ HR2').        
             pose proof (H0 _ HR4').
             unfold ctxt_app, zero, sum, one, delta.
             destruct (lt_dec x n').
             - pose proof (H0 _ l).
               pose proof (H _ l).
               clear H H0 HD0.
               clear WFP1 EQ2 EQ3.
               unfold ctxt_app, zero, sum, one, delta in *.
               lctxt_solve.
             - clear H H0 HD0.
               clear WFP1 EQ2 EQ3.
               unfold ctxt_app, zero, sum, one, delta in *.
               lctxt_solve.
           }
           apply wf_bag with (G':=G')(D':=
                                        (fun z =>
                                           if lt_dec z n' then
                                             if Nat.eq_dec z r then 0 else
                                               if Nat.eq_dec z r2 then 0 else
                                                 if Nat.eq_dec z r1' then 0 else
                                                   if Nat.eq_dec z r2' then 0 else
                                                     DA1 z
                                           else 0)
                                          ⨥ (n' + n)[r2' ↦ 2]).
           ++ auto.
           ++ unfold sum, delta.
              intros.
              lia_goal.
              specialize (H _ H2).
              specialize (H0 _ H2).
              assert (x < (n' + n)) by lia.
              specialize (H1 _ H3).
              unfold sum, one, delta in H, H0, H1.
              lctxt_solve.
           ++ eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
              unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
              lctxt_solve.
      * destruct (Nat.eq_dec r1' r2'); subst.
        -- assert (DA1 ⊗ zero n ≡[n' + n]
                (fun z =>
                   if lt_dec z n' then
                     if Nat.eq_dec z r then 0 else
                       if Nat.eq_dec z r2 then 0 else
                         if Nat.eq_dec z r1 then 0 else
                           if Nat.eq_dec z r2' then 0 else
                             DA1 z
                   else 0)
                ⨥ ((n' + n)[r1 ↦ 1])
                ⨥ ((n' + n)[r2 ↦ 1])
             ).
                
      { unfold ctxt_eq.
        intros.
        pose proof (H _ HR0').
        pose proof (H _ HR1').
        pose proof (H _ HR2').        
        pose proof (H _ HR4').
        pose proof (HD0 _ H1).
        pose proof (H0 _ HR0').
        pose proof (H0 _ HR1').
        pose proof (H0 _ HR2').        
        pose proof (H0 _ HR4').
        unfold ctxt_app, zero, sum, one, delta.
        destruct (lt_dec x n').
        - pose proof (H0 _ l).
          pose proof (H _ l).
          clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
        - clear H H0 HD0.
          clear WFP1 EQ2 EQ3.
          unfold ctxt_app, zero, sum, one, delta in *.
          lctxt_solve.
      }
      apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r2 then 0 else
                                            if Nat.eq_dec z r1 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2 ↦ 2]).
           ++ auto.
           ++ unfold sum, delta.
              intros.
              lia_goal.
              specialize (H _ H2).
              specialize (H0 _ H2).
              assert (x < (n' + n)) by lia.
              specialize (H1 _ H3).
              unfold sum, one, delta in H, H0, H1.
              lctxt_solve.
           ++ eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
              unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
              lctxt_solve.
        -- destruct (Nat.eq_dec r1 r2'); subst.
           ++ destruct (Nat.eq_dec r1' r2); subst.
              ** apply wf_bag with (G' := G')(D' := DA1); auto.
                 --- intros.
                     specialize (H _ H1).
                     specialize (H0 _ H1).
                     unfold sum, one, delta in H, H0.
                     lia_destruct.
                 --- rewrite rename_rvar_id_proc with (m := (m'+m)).
                     assumption.
                     eapply tpo_wf_ws; eauto.
              ** assert (DA1 ⊗ zero n ≡[n' + n]
                           (fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r2 then 0 else
                                    if Nat.eq_dec z r1' then 0 else
                                      if Nat.eq_dec z r2' then 0 else
                                        DA1 z
                              else 0)
                           ⨥ ((n' + n)[r1' ↦ 1])
                           ⨥ ((n' + n)[r2 ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').        
                   pose proof (H _ HR3').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').        
                   pose proof (H0 _ HR3').
                   unfold ctxt_app, zero, sum, one, delta.
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 }
                 apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r2 then 0 else
                                            if Nat.eq_dec z r1' then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2 ↦ 2]).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     lia_goal.
                     specialize (H _ H2).
                     specialize (H0 _ H2).
                     assert (x < (n' + n)) by lia.
                     specialize (H1 _ H3).
                     unfold sum, one, delta in H, H0, H1.
                     lctxt_solve.
                 --- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
                     unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
                     lctxt_solve.
           ++ destruct (Nat.eq_dec r1' r2); subst.
              ** assert (DA1 ⊗ zero n ≡[n' + n]
                           (fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r1 then 0 else
                                    if Nat.eq_dec z r2 then 0 else
                                      if Nat.eq_dec z r2' then 0 else
                                        DA1 z
                              else 0)
                           ⨥ ((n' + n)[r1 ↦ 1])
                           ⨥ ((n' + n)[r2' ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').        
                   pose proof (H _ HR4').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').        
                   pose proof (H0 _ HR4').
                   unfold ctxt_app, zero, sum, one, delta.
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 }
                 apply wf_bag with (G':=G')(D':=
                                   (fun z =>
                                      if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r2 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                      else 0)
                                     ⨥ (n' + n)[r2' ↦ 2]).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     lia_goal.
                     specialize (H _ H2).
                     specialize (H0 _ H2).
                     assert (x < (n' + n)) by lia.
                     specialize (H1 _ H3).
                     unfold sum, one, delta in H, H0, H1.
                     lctxt_solve.
                 --- eapply wf_proc_rename_rvar; eauto; simpl; try lia_goal.
                     unfold ctxt_eq, zero, ctxt_app, sum, delta. intros. simpl.
                     lctxt_solve.
              ** rewrite <- rename_rvar_proc_compose.

                 assert (DA1 ⊗ zero n ≡[n' + n]
                           ((fun z =>
                              if lt_dec z n' then
                                if Nat.eq_dec z r then 0 else
                                  if Nat.eq_dec z r1 then 0 else
                                    if Nat.eq_dec z r1' then 0 else 
                                      if Nat.eq_dec z r2 then 0 else
                                        if Nat.eq_dec z r2' then 0 else
                                          DA1 z
                              else 0)
                              ⨥ ((n' + n)[r2 ↦ 1])
                              ⨥ ((n' + n)[r2' ↦ 1])
                           )
                           ⨥ ((n' + n)[r1 ↦ 1])
                           ⨥ ((n' + n)[r1' ↦ 1])
                        ).
                 { unfold ctxt_eq.
                   intros.
                   
                   unfold ctxt_app, zero, sum, one, delta.
                   pose proof (H _ HR0').
                   pose proof (H _ HR1').
                   pose proof (H _ HR2').
                   pose proof (H _ HR3').
                   pose proof (H _ HR4').
                   pose proof (HD0 _ H1).
                   pose proof (H0 _ HR0').
                   pose proof (H0 _ HR1').
                   pose proof (H0 _ HR2').
                   pose proof (H0 _ HR3').                   
                   pose proof (H0 _ HR4').
                   destruct (lt_dec x n').
                   - pose proof (H0 _ l).
                     pose proof (H _ l).
                     clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                   - clear H H0 HD0.
                     clear WFP1 EQ2 EQ3.
                     unfold ctxt_app, zero, sum, one, delta in *.
                     lctxt_solve.
                 } 

                 
                 assert (wf_proc (m' + m) (n' + n) (G' ⊗ G)
                           ((((fun z =>
                                if lt_dec z n' then
                                  if Nat.eq_dec z r then 0 else
                                    if Nat.eq_dec z r1 then 0 else
                                      if Nat.eq_dec z r1' then 0 else 
                                        if Nat.eq_dec z r2 then 0 else
                                          if Nat.eq_dec z r2' then 0 else
                                            DA1 z
                                else 0)
                               ⨥ ((n' + n)[r2 ↦ 1])
                               ⨥ ((n' + n)[r2' ↦ 1])
                             )
                               ⨥ ((n' + n)[r1' ↦ 2])
                            ) ⊗ zero n)
                           (@rename_rvar_proc (n' + n) (n' + n) (rename_var r1 r1') P)).
                 { eapply wf_proc_rename_rvar with
                     (D1 := ((fun z => if lt_dec z n' then
                                      if Nat.eq_dec z r then 0 else
                                        if Nat.eq_dec z r1 then 0 else
                                          if Nat.eq_dec z r1' then 0 else 
                                            if Nat.eq_dec z r2 then 0 else
                                              if Nat.eq_dec z r2' then 0 else
                                                DA1 z
                                    else 0)
                               ⨥ ((n' + n)[r2 ↦ 1])
                               ⨥ ((n' + n)[r2' ↦ 1])
                     )); eauto.
                   - unfold sum, delta. lia_goal.
                   - unfold sum, delta. lia_goal.
                   - unfold ctxt_eq, ctxt_app, zero, delta, sum. intros. lctxt_solve.
                 } 
                     
                 eapply wf_bag with (G':=G')
                                    (D' := ((fun z =>
                                               if lt_dec z n' then
                                                 if Nat.eq_dec z r then 0 else
                                                   if Nat.eq_dec z r1 then 0 else
                                                     if Nat.eq_dec z r1' then 0 else 
                                                       if Nat.eq_dec z r2 then 0 else
                                                         if Nat.eq_dec z r2' then 0 else
                                                           DA1 z
                                               else 0)
                                              ⨥ ((n' + n)[r2' ↦ 2])
                                           )
                                             ⨥ ((n' + n)[r1' ↦ 2])).
                 --- auto.
                 --- unfold sum, delta.
                     intros.
                     pose proof (H _ H3).
                     pose proof (H _ HR2').
                     pose proof (H _ HR4').
                     assert (x < (n' + n)) by lia.
                     pose proof (HD0 _ H7).
                     unfold ctxt_app, sum, zero, one, delta in H, H4, H5, H6, H8.
                     lia_goal.
                     clear H1 H2.
                     lia_destruct.
                 --- rewrite <- sum_assoc.
                     rewrite (@sum_commutative _ ((n' + n)[r2' ↦ 2])).
                     rewrite sum_assoc.
                     repeat rewrite <- sum_assoc in H2.
                     rewrite (@sum_commutative _ ((n' + n)[r2' ↦ 1])) in H2.
                     repeat rewrite <- sum_assoc in H2.
                     rewrite (@sum_assoc _ (n' + n) [r2 ↦ 1]) in H2.
                     rewrite (@sum_commutative _ ((n' + n)[r2 ↦ 1])) in H2.
                     repeat rewrite sum_assoc in H2.
                     
                     eapply wf_proc_rename_rvar with (cr:=1)(cr':=1)
                       (D1 := (((fun z => if lt_dec z n' then
                                        if Nat.eq_dec z r then 0 else
                                          if Nat.eq_dec z r1 then 0 else
                                            if Nat.eq_dec z r1' then 0 else 
                                              if Nat.eq_dec z r2 then 0 else
                                                if Nat.eq_dec z r2' then 0 else
                                                  DA1 z
                                      else 0)
                                  ⨥ (n' + n)[r1' ↦ 2]))); eauto.
                     +++ unfold sum, delta.
                         intros.
                         lia_goal.
                     +++ unfold sum, delta.
                         lia_goal.
                     +++ unfold ctxt_eq, ctxt_app, sum, zero, one, delta.
                         intros.
                         clear H1 H2.
                         destruct (lt_dec x n').
                         *** pose proof (H0 _ l).
                             pose proof (H _ l).
                             unfold sum, one, delta in H1, H2.
                             lia_goal.
                         *** lia_goal.
                     +++ unfold ctxt_eq, ctxt_app, sum, zero, one, delta.
                         intros.
                         clear H1 H2.
                         destruct (lt_dec x n').
                         *** pose proof (H0 _ l).
                             pose proof (H _ l).
                             unfold sum, one, delta in H1, H2.
                             lia_goal.
                         *** lia_goal.
Qed.
                     
                   

Inductive prim_step : nat -> nat -> term -> term -> Prop :=
| step_emp_cut :
  forall m m' n n' r P,
    prim_step m n
      (bag m' n' (par P (par (def r emp) (def r emp))))
      (bag m' n' P)

| step_tup_cut :
  forall m m' n n' r r1 r2 r1' r2' P,
    prim_step m n
      (bag m' n' (par P (par (def r (tup r1 r2)) (def r (tup r1' r2')))))
      (bag m' n' (rename_rvar_proc (cut_renaming (n' + n) r1 r2 r1' r2') P))
      
| step_app :
  forall m m' m'' n n' n'' r r' f P Q,
    let Q' := retract_rvar_proc (m' + m'') r' m' (scope_extrude m' m'' n' n'' Q) in
    prim_step m n
      (bag m' n'
         (par P
         (par (def r (lam (bag m'' n'' Q)))
         (par (def r (bng f))
              (app f r')))))
      (bag (m' + m'') (n' + n'')
         (par P
         (par (def r (lam (bag m'' n'' Q)))
         (par (def r (bng f))
              Q')))).

Inductive  step : nat -> nat -> term -> term -> Prop :=
| step_equiv : forall m n t1 t1' t2,
    t1 ≈t t1' ->
    prim_step m n t1' t2 ->
    step m n t1 t2.





(* Canonical forms -- is it needed?  ----------------------------------- *)


Inductive lt_list : list nat -> list nat -> Prop :=
| lt_nil : forall x xs, lt_list nil (x::xs)
| lt_cons : forall x y xs ys,
    x < y -> lt_list (x::xs) (y::ys)
| lt_tl : forall x xs ys,
    lt_list xs ys ->
    lt_list (x::xs) (x::ys).

Lemma lt_list_transitive : forall l1 l2 l3,
    lt_list l1 l2 -> lt_list l2 l3 -> lt_list l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0; intros.
  - inversion H.
  - inversion H0; subst.
    apply lt_nil.
    apply lt_cons. lia.
    apply lt_cons. assumption.
  - inversion H; subst.
    apply lt_nil.
    apply lt_cons. assumption.
    apply lt_tl.
    apply IHlt_list.
    assumption.
Qed.    

Lemma lt_list_lt_eq_lt_dec : forall l1 l2,
    {lt_list l1 l2} + {l1 = l2} + {lt_list l2 l1}.
Proof.
  induction l1; intros.
  - destruct l2.
    + left. right. reflexivity.
    + left. left. apply lt_nil.
  - destruct l2.
    + right. apply lt_nil.
    + specialize (lt_eq_lt_dec a n) as H.
      destruct H as [[HL | HE] | HG].
      * left. left. apply lt_cons. assumption.
      * subst.
        destruct (IHl1 l2) as [[HL | HE] | HG].
        -- left. left. apply lt_tl. assumption.
        -- subst. left. right. reflexivity.
        -- right. apply lt_tl. assumption.
      * right. apply lt_cons. assumption.
Qed.        

Unset Elimination Schemes.
Inductive lt_term : term -> term -> Prop :=
| lt_bag_m:
  forall m1 m2 n1 n2 P1 P2,
    m1 < m2 ->
    lt_term (bag m1 n1 P1) (bag m2 n2 P2)    

| lt_bag_n:
  forall m n1 n2 P1 P2,
    n1 < n2 ->
    lt_term (bag m n1 P1) (bag m n2 P2)    

| lt_bag_P:
  forall m n P1 P2,
    lt_proc P1 P2 ->
    lt_term (bag m n P1) (bag m n P2)    

with lt_proc : proc -> proc -> Prop :=
| lt_def_def_r:
  forall r1 r2 o1 o2,
    r1 < r2 ->
    lt_proc (def r1 o1) (def r2 o2)

| lt_def_def_o:
  forall r o1 o2,
    lt_oper o1 o2 ->
    lt_proc (def r o1) (def r o2)

| lt_def_app :
  forall r o f r',
    lt_proc (def r o) (app f r')

| lt_def_par :
  forall r o P1 P2,
    lt_proc (def r o) (par P1 P2)

| lt_app_app_f:
  forall f1 f2 r1 r2,
    f1 < f2 ->
    lt_proc (app f1 r1) (app f2 r2)

| lt_app_app_r:
  forall f r1 r2,
    r1 < r2 ->
    lt_proc (app f r1) (app f r2)

| lt_app_par :
  forall f r P1 P2,
    lt_proc (app f r) (par P1 P2)

| lt_par_par1 :
  forall P1 P1' P2 P2',
    lt_proc P1 P1' ->
    lt_proc (par P1 P2) (par P1' P2')

| lt_par_par2 :
  forall P P2 P2',
    lt_proc P2 P2' ->
    lt_proc (par P P2) (par P P2')

with lt_oper : oper -> oper -> Prop :=

| lt_emp_tup :
  forall r1 r2,
    lt_oper emp (tup r1 r2)

| lt_emp_bng :
  forall f,
    lt_oper emp (bng f)

| lt_emp_lam :
  forall t,
    lt_oper emp (lam t)
            
| lt_tup_tup1 :
  forall r1 r2 r1' r2',
    r1 < r1' ->
    lt_oper (tup r1 r2) (tup r1' r2')

| lt_tup_tup2 :
  forall r r2 r2',
    r2 < r2' ->
    lt_oper (tup r r2) (tup r r2')
            
| lt_tup_bng :
  forall r1 r2 f,
    lt_oper (tup r1 r2) (bng f)

| lt_tup_lam :
  forall r1 r2 t,
    lt_oper (tup r1 r2) (lam t)

| lt_bng_bng :
  forall f1 f2,
    f1 < f2 ->
    lt_oper (bng f1) (bng f2)

| lt_bng_lam :
  forall f t,
    lt_oper (bng f) (lam t)

| lt_lam_lam :
  forall t1 t2,
    lt_term t1 t2 ->
    lt_oper (lam t1) (lam t2).

Hint Constructors lt_term lt_proc lt_oper : core.



Scheme lt_term_ind := Induction for lt_term Sort Prop
    with lt_proc_ind := Induction for lt_proc Sort Prop
                        with lt_oper_ind := Induction for lt_oper Sort Prop.

Combined Scheme lt_tpo_ind from lt_term_ind, lt_proc_ind, lt_oper_ind.

Lemma lt_tpo_transitive :
  (forall t1 t2,
    lt_term t1 t2 ->
    forall t3,
      lt_term t2 t3 ->
      lt_term t1 t3)
  /\ (forall P1 P2,
        lt_proc P1 P2 ->
        forall P3,
          lt_proc P2 P3 ->
          lt_proc P1 P3)
  /\ (forall o1 o2,
        lt_oper o1 o2 ->
        forall o3,
          lt_oper o2 o3 ->
          lt_oper o1 o3).
Proof.
  apply lt_tpo_ind; intros; try inversion H; subst; eauto.
  - apply lt_bag_m. lia.
  - inversion H; subst; auto.
    apply lt_bag_n. lia.
  - inversion H0; subst; auto.
  - inversion H; subst; auto.
    apply lt_def_def_r. lia.
  - inversion H0; subst; auto.
  - apply lt_app_app_f. lia.
  - apply lt_app_app_r. lia.
  - inversion H0; subst; auto.
  - inversion H0; subst; auto.
  - apply lt_tup_tup1. lia.
  - apply lt_tup_tup2. lia.
  - apply lt_bng_bng. lia.
  - inversion H0; subst; auto.
Qed.

Lemma lt_top_lt_eq_lt_dec :
  (forall t1,
    forall t2, {lt_term t1 t2} + {t1 = t2} + {lt_term t2 t1})
  *
    ((forall P1,
       forall P2, {lt_proc P1 P2} + {P1 = P2} + {lt_proc P2 P1})
     * (forall o1,
         forall o2,  {lt_oper o1 o2} + {o1 = o2} + {lt_oper o2 o1}))%type.
Proof.
  apply tpo_rect; intros.
  - destruct t2.
    specialize (lt_eq_lt_dec m m0) as [[HL | HE] | HG].
    + left. left. auto.
    + subst.
      specialize (lt_eq_lt_dec n n0) as [[HL | HE] | HG].
      * left. left.  auto.
      * subst.
        destruct (H P0) as [[HL | HE] | HG].
        -- left. left.  auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + right.  auto.
  - destruct P2.
    specialize (lt_eq_lt_dec r r0) as [[HL | HE] | HG].
    + left. left. auto.
    + subst.
      destruct (H o0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + right. auto.
    + left. left.  auto.
    + left. left.  auto.
  - destruct P2.
    + right. auto.
    + specialize (lt_eq_lt_dec f f0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. specialize (lt_eq_lt_dec r r0) as [[HL | HE] | HG].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + left. left. auto.
  - destruct P0.
    + right. auto.
    + right. auto.
    + destruct (H P0_1) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. 
        destruct (H0 P0_2) as [[HL | HE] | HG].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
  - destruct o2.
    + left. right. reflexivity.
    + left. left. auto.
    + left. left. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + destruct (lt_eq_lt_dec r1 r0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst.
        destruct (lt_eq_lt_dec r2 r3) as [[HL' | HE'] | HG'].
        -- left. left. auto.
        -- subst. left. right. auto.
        -- right. auto.
      * right. auto.
    + left. left. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + right. auto.
    + specialize (lt_eq_lt_dec f f0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + right. auto.
    + right. auto.
    + destruct (H t0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
Qed.        

Unset Elimination Schemes.
Inductive ForallTerm (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : term -> Prop :=
| Forall_bag:
  forall m n P,
    ForallProc PT PP PO P ->
    PT (bag m n P) ->
    ForallTerm PT PP PO (bag m n P)
with 
  ForallProc (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : proc -> Prop :=
| Forall_def : forall r o,
    PP (def r o) ->
    ForallOper PT PP PO o ->
    ForallProc PT PP PO (def r o)

| Forall_app : forall f r,
    PP (app f r) ->
    ForallProc PT PP PO (app f r)

| Forall_par : forall P1 P2,
    ForallProc PT PP PO P1 ->
    ForallProc PT PP PO P2 ->
    ForallProc PT PP PO (par P1 P2)
with
  ForallOper (PT : term -> Prop) (PP : proc -> Prop) (PO : oper -> Prop) : oper -> Prop :=
| Forall_emp :
  PO emp ->
  ForallOper PT PP PO emp

| Forall_tup :
  forall r1 r2,
    PO (tup r1 r2) ->
    ForallOper PT PP PO (tup r1 r2)

| Forall_bng :
  forall f,
    PO (bng f) ->
    ForallOper PT PP PO (bng f)

| Forall_lam :
  forall t,
    PO (lam t) ->
    ForallTerm PT PP PO t ->
    ForallOper PT PP PO (lam t).

Scheme Forallterm_ind := Induction for ForallTerm Sort Prop
    with Forallproc_ind := Induction for ForallProc Sort Prop
                        with Foralloper_ind := Induction for ForallOper Sort Prop.

Combined Scheme Foralltpo_ind from Forallterm_ind, Forallproc_ind, Foralloper_ind.

Definition locally_ordered_wrt (P:proc) :=
  ForallProc (fun t => True) (fun P' => P = P' \/ lt_proc P P') (fun o => True).



Unset Elimination Schemes.
Inductive canonical_term : term -> Prop :=
| can_term :
  forall m n P,
    canonical_proc P ->
    canonical_term (bag m n P)

with canonical_proc : proc -> Prop :=
| can_def_tl :
  forall r o,
    canonical_oper o ->
    canonical_proc (def r o)

| can_app_tl :
  forall f r,
    canonical_proc (app f r)

| can_def_cons :
  forall r o P,
    canonical_oper o ->
    canonical_proc P ->
    locally_ordered_wrt (def r o) P ->
    canonical_proc (par (def r o) P)

| can_app_cons :
  forall f r P,
    canonical_proc P ->
    locally_ordered_wrt (app f r) P ->
    canonical_proc (par (app f r) P)
                   
with canonical_oper : oper -> Prop :=
| can_emp :
  canonical_oper emp
                 
| can_tup :
  forall r1 r2,
    canonical_oper (tup r1 r2)

| can_bng :
  forall f,
    canonical_oper (bng f)

| can_lam :
  forall t,
    canonical_term t ->
    canonical_oper (lam t).


