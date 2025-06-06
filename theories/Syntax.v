From Stdlib Require Import
  Arith            
  Classes.RelationClasses
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

     - [tup rs]  a "tuple" of resources
     - [bng f]   the name of a function
     - [lam t]   an lambda, which is a term parameterized by one resource


  (* SAZ: We could contemplate defining Rocq notations for terms. *) 

 *)

Inductive term :=
| bag (m n:nat) (P:proc)   (* nu. {f1...fm} {r1..rn} P *)

with proc :=
| def (r:rvar) (o:oper)  (* r <- o *)
| app (f:fvar) (r:rvar)  (* f r *)
| par (P1 P2 : proc)     (* P1 | P2 *)

with oper :=             
| tup (rs : list rvar)   (* (r1,...,rk) *)
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
| ws_tup :
  forall m n
    (rs : list rvar)
    (HRS : List.Forall (fun x => x < n) rs),
    ws_oper m n (tup rs)

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
    (UD' : forall x, x < n' -> (D' x) = 2)
    (P : proc)
    (WFP : wf_proc (m' + m) (n' + n) (G' ⊗ G) (D' ⊗ D) P),
    wf_term m n G D (bag m' n' P)

with wf_proc : forall (m n:nat), lctxt m -> lctxt n -> proc -> Prop :=
| wf_def :
  forall m n
    (G : lctxt m)
    (D : lctxt n)
    (r : rvar) (HR : r < n)
    (o : oper)
    (WFO : wf_oper m n G D o),
    wf_proc m n G ((one n r) ⨥ D) (def r o)

| wf_app :
  forall m n
    (f : fvar) (HF : f < m)
    (r : rvar) (HR : r < n),
    wf_proc m n (one m f) (one n r) (app f r)

| wf_par :
  forall m n
    (G1 G2 : lctxt m)
    (D1 D2 : lctxt n)
    (P1 P2 : proc)
    (WFP1 : wf_proc m n G1 D1 P1)
    (WFP2 : wf_proc m n G2 D2 P2),
    wf_proc m n (G1 ⨥ G2) (D1 ⨥ D2) (par P1 P2)
            
with wf_oper : forall (m n:nat), lctxt m -> lctxt n -> oper -> Prop :=
| wf_tup :
  forall m n
    (rs : list rvar)
    (HRS : List.Forall (fun x => x < n) rs),
    wf_oper m n (zero m) (SUM (List.map (one n) rs)) (tup rs)

| wf_bng :
  forall m n
    (f : fvar)
    (HF : f < m),
    wf_oper m n (one m f) (zero n) (bng f)
            
| wf_lam :
  forall m n
    (t : term)
    (WFT : wf_term m 1 (zero m) (1[0 ↦ 1]) t),
    wf_oper m n (zero m) (zero n) (lam t).
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
      rewrite sum_commutative. rewrite (@sum_commutative _ D1 D2).
      apply wf_par; assumption.
    + inversion H; existT_eq; subst.
      rewrite sum_commutative. rewrite (@sum_commutative _ D1 D2).
      apply wf_par; assumption.
  - split; intros.
    + inversion H; existT_eq; subst. inversion WFP2; existT_eq; subst.
      rewrite sum_assoc. rewrite (@sum_assoc _ D1 D0 D3).
      apply wf_par. apply wf_par; assumption. assumption.
    + inversion H; existT_eq; subst. inversion WFP1; existT_eq; subst.
      rewrite <- sum_assoc. rewrite <- (@sum_assoc _ D0 D3 D2).
      apply wf_par. assumption. apply wf_par; assumption.
  - split; intros.
    + inversion H; existT_eq; subst. inversion WFP1; existT_eq; subst.
      rewrite <- sum_assoc. rewrite <- (@sum_assoc _ D0 D3 D2).
      apply wf_par. assumption. apply wf_par; assumption.
    + inversion H; existT_eq; subst. inversion WFP2; existT_eq; subst.
      rewrite sum_assoc. rewrite (@sum_assoc _ D1 D0 D3).
      apply wf_par. apply wf_par; assumption. assumption.
  - destruct H as [HL1 HR1].
    destruct H0 as [HL2 HR2].
    split; intros.
    + inversion H; existT_eq; subst.
      apply wf_par. apply HL1. apply WFP1.
      apply HL2. apply WFP2.
    + inversion H; existT_eq; subst.
      apply wf_par.
      apply HR1. apply WFP1.
      apply HR2. apply WFP2.
  - destruct H as [HL HR].
    split; intros.
    + inversion H; existT_eq; subst.
      apply wf_def; auto.
    + inversion H; existT_eq; subst.
      apply wf_def; auto.
  - split; intros; auto.
  - destruct H as [HL HR].
    split; intros.
    + inversion H; existT_eq; subst.
      apply wf_lam; auto.
    + inversion H; existT_eq; subst.
      apply wf_lam; auto.
Qed.
    
Instance wf_term_seq : Proper (eq ==> eq ==> eq ==> eq ==> seq_term ==> iff) (wf_term).
Proof.
  repeat red; intros; subst.
  split.
  apply tpo_wf_seq. symmetry. assumption.
  apply tpo_wf_seq. assumption.
Qed.

Instance wf_proc_seq : Proper (eq ==> eq ==> eq ==> eq ==> seq_proc ==> iff) (wf_proc).
Proof.
  repeat red; intros; subst.
  split.
  apply tpo_wf_seq. symmetry. assumption.
  apply tpo_wf_seq. assumption.
Qed.

Instance wf_oper_seq : Proper (eq ==> eq ==> eq ==> eq ==> seq_oper ==> iff) (wf_oper).
Proof.
  repeat red; intros; subst.
  split.
  apply tpo_wf_seq. symmetry. assumption.
  apply tpo_wf_seq. assumption.
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
  | tup rs => tup (map v rs)
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
       | tup rs => tup rs
       | bng f => bng (v f)
       | lam t => lam (rename_fvar_term v t)
       end.

Lemma rename_rvar_oper_compose : forall n n' n'' (v1 : ren n n') (v2 : ren n' n'') (o : oper),
    rename_rvar_oper v2 (rename_rvar_oper v1 o) = @rename_rvar_oper n n'' (ren_compose v1 v2) o.
Proof.
  intros.
  destruct o; simpl; try reflexivity.
  rewrite map_map. reflexivity.
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
  simpl. rewrite map_ren_id; auto.
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
| peq_tup :
  forall m n rs
    (HRS : List.Forall (fun r => r < n) rs)
    (bf : ren m m)
    (br : ren n n),
    peq_oper m n bf br (tup rs) (tup (List.map br rs))

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
  - inversion HT'.
    existT_eq. subst.
    rewrite map_map.
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
  - assert (rs = map (bij_inv br BR) (map br rs)).
    { rewrite map_map.
      rewrite <- (map_id rs) at 1.
      eapply map_ext_Forall.
      eapply Forall_impl.
      2 : apply HRS.
      intros.     
      apply bij_ren_inv_elt; auto.
    }
    rewrite H at 2.
    econstructor.
    rewrite Forall_map.
    eapply Forall_impl.
    2 : apply HRS.
    intros. auto.
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
  - rewrite <- (map_ren_id rs n) at 2; auto. 
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
    rewrite ren_sum_compose.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    rewrite ren_one_compose with (H:=X); auto.
    rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
    constructor.
    + apply HWR; auto.
    + apply H; auto.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    rewrite ren_one_compose with (H:=X); auto.
    rewrite ren_one_compose with (H:=X0); auto.
    rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
    rewrite (bij_inv_bij_inv_eq _ bf HWF HBF X0).
    constructor.
    apply HWF; auto.
    apply HWR; auto.
  - inversion H1; existT_eq; subst.
    rewrite ren_sum_compose.
    rewrite ren_sum_compose.
    constructor; auto.
  - inversion H; existT_eq; subst.
    rewrite ren_SUM_compose.
    rewrite map_map.
    rewrite ren_compose_zero.
    assert (wf_ren (bij_inv br HBR)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv br HBR)) by (apply bij_inv_bij; auto).
    pose proof (map_ext_Forall_partial _ _ _ _ _ _ (ren_one_compose n (bij_inv br HBR) H0 X) HRS0).
    setoid_rewrite H1.
    rewrite (bij_inv_bij_inv_eq _ br HWR HBR X).
    rewrite <- map_map.
    constructor.
    apply Forall_ren_wf; auto.
  - inversion H; existT_eq; subst.
    assert (wf_ren (bij_inv bf HBF)) by (apply wf_bij_ren_inv; auto).
    assert (bij_ren (bij_inv bf HBF)) by (apply bij_inv_bij; auto).
    rewrite ren_one_compose with (H := X); auto.
    rewrite (bij_inv_bij_inv_eq _ bf HWF HBF X).
    rewrite ren_compose_zero.
    constructor.
    apply HWF; auto.
  - inversion H0; existT_eq; subst.
    rewrite ren_compose_zero.
    rewrite ren_compose_zero.
    constructor; auto.
    specialize (H t' bf _ H6 HWF HBF (wf_ren_id 1) (bij_ren_id 1)).
    rewrite ren_compose_zero in H.
    simpl in H.
    setoid_rewrite (ren_delta_compose _ (ren_id 1) 0 1 (wf_ren_id 1) (bij_ren_id 1)) in H; auto.
Qed.    

(* cuts *)

(* "removes" variable x from the scope, where n is the number of variables > x *)
Definition cut n (x:var) : ren (x + 1 + n) (x + n) :=
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
  @ren_compose (y + 1 + n) (y + 1 + n) _ (rename_var y x) (cut n y).

Definition cut_rvar_oper n x o : oper :=
  rename_rvar_oper (cut n x) o.
  
Definition cut_rvar_proc n x P : proc :=
  rename_rvar_proc (cut n x) P.

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
  (par (def 3 (tup ([2])))
     (def 1 (tup ([4])))).

Example ex_P : proc :=
  par (def 0 (tup ([1;2])))
    (par (def 0 (tup ([3;4])))
       ex_P0).

Eval compute in retract_rvar_proc 1 1 3 ex_P0.

(* (bag m n (par P (par (def r (tup rs1)) (def r (tup rs2))))) *)
Inductive step_cuts : term -> term -> Prop :=
| step_tup_nil :
  forall m n P r,
    step_cuts
      (bag m (r + 1 + n) (par P (par (def r (tup nil)) (def r (tup nil)))))
      (bag m (r + n) (cut_rvar_proc n r P))

| step_tup_cons_l :
  forall m n P r r1 r2 rs1 rs2 t'
    (HLT: r1 < r2)
    (HS: step_cuts (bag m (r2 + n)
                  (retract_rvar_proc n r1 r2
                     (par P (par (def r (tup rs1))
                               (def r (tup rs2))))))
               t'),
    
    (step_cuts (bag m (r2 + 1 + n) (par P (par (def r (tup (r1::rs1)))
                                             (def r (tup (r2::rs2))))))
       t')

| step_tup_cons_r :
  forall m n P r r1 r2 rs1 rs2 t'
    (HLT: r2 < r1)
    (HS: step_cuts (bag m (r1 + n)
                  (retract_rvar_proc n r2 r1
                     (par P (par (def r (tup rs1))
                               (def r (tup rs2))))))
               t'),
    
    (step_cuts (bag m (r1 + 1 + n) (par P (par (def r (tup (r1::rs1)))
                                             (def r (tup (r2::rs2))))))
       t').



      
  




Definition ren_f_extrude m m' : ren (m + m') (m' + m) :=
  fun x =>
    if lt_dec x m' then x + m else (x - m').

Definition scope_extrude m m' n n' Q :=
    let Q1 := @rename_rvar_proc n (n' + n) (fun x => n + x) Q in
    let Q2 := @rename_fvar_proc (m + m') (m' + m) (ren_f_extrude m m') Q1 in
    Q2.



(*



Inductive prim_step : term -> term -> Prop :=
| step_tup_cut :
  forall m n r rs1 rs2 P t,
    step_cuts (r::rs1) (r::rs2) (bag m n P) = Some t ->
    prim_step (bag m n (par P (par (def r (tup rs1)) (def r (tup rs2)))))
      t

| step_app :
  forall m m' n n' r r' f P Q,
    let Q' := retract_rvar_proc (m + m') r' m (scope_extrude m m' n n' Q) in
    prim_step
      (bag m n
         (par P
         (par (def r (lam (bag m' n' Q)))
         (par (def r (bng f))
              (app f r')))))
      (bag (m' + m) (n' + n)
         (par P
         (par (def r (lam (bag m' n' Q)))
         (par (def r (bng f))
              Q')))).

Inductive  step : term -> term -> Prop :=
| step_equiv : forall t1 t1' t2,
    t1 ≈t t1' ->
    prim_step t1' t2 ->
    step t1 t2.

Lemma wf_cuts :
  forall m (G : lctxt m) rrs n (ls1 : list var) (ls2 : list var) (D : lctxt n) (D1 : lctxt n) P
    (HLS: split rrs = (ls1, ls2))
    (HLS1 : Forall (fun x => x < n) ls1)
    (HLS2 : Forall (fun x => x < n) ls2)
    (UD' : forall x, x < n -> D x = 2)
    (HD : D1 ⨥ (SUM (map (one n) ls1) ⨥ SUM (map (one n) ls2)) = D)
    (WFP : wf_proc m n G D1 P),
  exists (D'' : lctxt (n - length rrs)),
    (forall x, x < (n - length rrs) -> D'' x = 2) /\
      wf_proc m (n - length rrs) G D'' (rename_rvar_proc (cuts (n - length rrs) rrs) P).
Proof.
  induction rrs; intros; simpl in *.
  - inversion HLS; clear HLS.
    subst. simpl in *.
    exists D1.
    split.
    + rewrite sum_zero_r in UD'.
      intros. apply UD'. lia.
    + replace (n-0) with n by lia.
      rewrite rename_rvar_id_proc with (m := m); auto.
      apply tpo_wf_ws in WFP.
      assumption.
  - destruct a as [r1 r2].
    destruct (split rrs).
    inversion HLS; clear HLS.
    rewrite <- H0 in HLS1.
    inversion HLS1. subst. clear HLS1.
    inversion HLS2; subst. clear HLS2.
    assert (forall x : nat, x < n -> (D1 ⨥ (SUM (map (one n) l) ⨥ SUM (map (one n) l0))) x = 2).
    { intros.
      specialize (UD' x H).
      simpl in UD'.
      
      
    
    
*)    
  
  
  

(*

(* Do we care only about stepping a top-level term? *)
Lemma prim_step_wf :
  forall m (G : lctxt m) (D : lctxt 0) (t t' : term)
    (WF : wf_term m 0 G D t)
    (STEP : prim_step t t'),
    wf_term m 0 G D t'.
Proof.
  intros.
  inversion STEP; subst; clear STEP.
  - inversion WF; existT_eq; subst; clear WF.
    inversion WFP; existT_eq; subst; clear WFP.
    inversion WFP2; existT_eq; subst; clear WFP2.
    inversion WFP0; existT_eq; subst; clear WFP0.
    inversion WFP3; existT_eq; subst; clear WFP3.
    inversion WFO; existT_eq; subst; clear WFO.
    inversion WFO0; existT_eq; subst; clear WFO0.
    rewrite sum_zero_r in H2.
    subst.
    replace (n + 0) with n in * by lia.
    unfold step_cuts in H.
    destruct (Nat.eq_dec (length (r::rs1)) (length (r::rs2))).
    2 : { inversion H. }
    assert ((one n r ⨥ SUM (map (one n) rs1)) = SUM (map (one n) (r::rs1))).
    { reflexivity. }
    rewrite H0 in H3; clear H0.
    assert ((one n r ⨥ SUM (map (one n) rs2)) = SUM (map (one n) (r::rs2))).
    { reflexivity. }
    rewrite H0 in H3; clear H0.
    remember (r :: rs1) as ls1.
    remember (r :: rs2) as ls2.
    remember (combine ls1 ls2) as rrs.
    assert (split rrs = (ls1, ls2)).
    { rewrite Heqrrs. apply combine_split; auto. }



    
    
    
    subst.
    
*)    





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
  
| lt_tup_tup :
  forall rs1 rs2,
    lt_list rs1 rs2 ->
    lt_oper (tup rs1) (tup rs2)

| lt_tup_bng :
  forall rs f,
    lt_oper (tup rs) (bng f)

| lt_tup_lam :
  forall rs t,
    lt_oper (tup rs) (lam t)

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
  apply lt_tpo_ind; intros; auto.
  - inversion H; subst; auto.
    apply lt_bag_m. lia.
  - inversion H; subst; auto.
    apply lt_bag_n. lia.
  - inversion H0; subst; auto.
  - inversion H; subst; auto.
    apply lt_def_def_r. lia.
  - inversion H0; subst; auto.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
    apply lt_app_app_f. lia.
  - inversion H; subst; auto.
    apply lt_app_app_r. lia.
  - inversion H; subst; auto.
  - inversion H0; subst; auto.
  - inversion H0; subst; auto.
  - inversion H; subst; auto.
    apply lt_tup_tup. eapply lt_list_transitive; eauto.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
    apply lt_bng_bng. lia.
  - inversion H; subst; auto.
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
    + destruct (lt_list_lt_eq_lt_dec rs rs0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + left. left. auto.
    + left. left. auto.
  - destruct o2.
    + right. auto.
    + specialize (lt_eq_lt_dec f f0) as [[HL | HE] | HG].
      * left. left. auto.
      * subst. left. right. auto.
      * right. auto.
    + left. left. auto.
  - destruct o2.
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
| Forall_tup :
  forall rs,
    PO (tup rs) ->
    ForallOper PT PP PO (tup rs)

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
| can_tup :
  forall rs,
    canonical_oper (tup rs)

| can_bng :
  forall f,
    canonical_oper (bng f)

| can_lam :
  forall t,
    canonical_term t ->
    canonical_oper (lam t).


