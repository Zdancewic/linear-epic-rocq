From Stdlib Require Import
  Arith
  Logic.FunctionalExtensionality
  Lia
  Classes.RelationClasses
  Morphisms
  Program.Basics
  List
  Vectors.FinFun.

Import Relation_Definitions.

From LEpic Require Import Permutations.

(* deBruijn indices *)
Definition var := nat.

(* Contexts ----------------------------------------------------------------- *)

Definition ctxt (n:nat) (X:Type) := var -> X.

Definition cons {X:Type} {n:nat} (x:X) (c : ctxt n X) :=
  fun y =>
    match y with
    | 0 => x
    | S y => c y
    end.

Definition tail {X} {n} (c : ctxt (S n) X) : ctxt n X :=
  fun x => c (S x).

Lemma tail_cons : forall  {X} {n} (l : ctxt (S n) X) (x:X),
    tail (cons x l) = l.
Proof.
  intros. reflexivity. 
Qed.

Definition ctxt_app {X} {n m : nat} (c : ctxt n X) (d : ctxt m X) :  ctxt (n + m) X :=
  fun x =>
    if Compare_dec.lt_dec x n then c x else d (x-n).

Infix "⊗" := (@ctxt_app _ _ _) (at level 50).

Lemma ctxt_app_null_l : forall {X} {n} (c : ctxt 0 X) (d : ctxt n X),
    c ⊗ d = d.
Proof.
  unfold ctxt_app.
  intros.
  apply functional_extensionality.
  intros x.
  destruct (lt_dec x 0).
  - inversion l.
  - replace x with (x - 0) at 2 by apply Nat.sub_0_r.
    reflexivity.
Qed.  

Lemma ctxt_app_null_r : forall {X} {n} (c : ctxt n X) (d : ctxt 0 X),
    forall (x:nat), (x < n) -> 
    (c ⊗ d) x = c x.
Proof.
  unfold ctxt_app.
  intros.
  destruct (lt_dec x n).
  - reflexivity.
  - contradiction.
Qed.  


(* Linear contexts ---------------------------------------------------------- *)

(* Theory of "linear" contexts that map variables (represented as autosubst's [fin n])
   to their usage information.
*)

(* The following definitions are about contexts of "usage" information as found in linear type systems. *)
Definition lctxt (n:nat) := ctxt n nat.

Definition sum {n} (c : lctxt n) (d : lctxt n) : lctxt n :=
  fun x => (c x) + (d x).

Infix "⨥" := (@sum _) (at level 50).

Definition zero n : lctxt n := fun (x:nat) => 0.

Lemma zero_scons : forall n, (zero (S n)) = (@cons _ n 0 (zero n)).
Proof.
  intros n.
  apply functional_extensionality.
  intros x.
  unfold cons.
  destruct x; auto.
Qed.  

Lemma zero_tail : forall n, (@tail _ n (zero (S n))) = zero n.
Proof.
  intros n.
  apply functional_extensionality.
  intros x.
  unfold tail. reflexivity.
Qed.  

Lemma sum_zero_r : forall {n} (c : lctxt n),
    c ⨥ (zero n) = c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold zero. lia.
Qed.

Lemma sum_zero_l : forall {n} (c : lctxt n),
    (zero n) ⨥ c = c.
Proof.
  intros. apply functional_extensionality.
  intros. reflexivity.
Qed.

Lemma sum_assoc : forall {n} (c : lctxt n) (d : lctxt n) (e : lctxt n),
    c ⨥ (d ⨥ e) = (c ⨥ d) ⨥ e.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. lia.
Qed.

Lemma sum_commutative : forall {n} (c : lctxt n) (d : lctxt n),
    c ⨥ d = d ⨥ c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. lia.
Qed.

(* 
  [delta x c] is the context that maps x to c and everything else to 0

  (* SAZ: we may be able to change this now that renamings are bounded *)
*)

Definition delta (n:nat) (x:var) (c : nat) : lctxt n :=
  fun y => if (Nat.eq_dec x y) then c else 0.
      
Notation "n [ x ↦ c ]" := (delta n x c).

Lemma delta_id : forall (n:nat) (x : var) (c:nat),
    n[x ↦ c] x = c.
Proof.
  intros.
  unfold delta.
  destruct (Nat.eq_dec x x); auto.
  contradiction.
Qed.

Lemma delta_neq : forall n (x y : var) c,
    x <> y ->
    n[x ↦ c] y = 0.
Proof.
  intros.
  unfold delta.
  destruct (Nat.eq_dec x y); auto.
  contradiction.
Qed.  
  
Lemma delta_c_inv : forall n (x y : var) c ,
    c <> 0 ->
    n[x ↦ c] y = c -> x = y.
Proof.
  intros.
  destruct (Nat.eq_dec x y); auto.
  rewrite delta_neq in H0; auto. subst. contradiction.
Qed.

Lemma delta_0_inv : forall n (x y : var) c ,
    n[x ↦ c] y = 0  -> (c = 0 \/ x <> y).
Proof.
  intros.
  destruct c eqn:HC. left; auto.
  right. intros Heq. subst. rewrite delta_id in H.
  discriminate. 
Qed.

Lemma delta_sum : forall n (x : var) c1 c2 ,
    n[x ↦ c1] ⨥ n[x ↦ c2] = n[x ↦ (c1 + c2)].
Proof.
  unfold delta. unfold sum.
  intros.
  apply functional_extensionality.
  intros.
  destruct (Nat.eq_dec x x0); auto.
Qed.

Definition one n (x : var) : lctxt n := n[x ↦ 1].

Definition SUM {n} (l : list (lctxt n)) : lctxt n :=
  List.fold_right sum (zero n) l.

(* Renaming Relations ------------------------------------------------------- *)

Module Renamings.

  Definition ren (n m : nat) := ctxt n var.

  (* Note: to make renamings more "canonical" we force them to map all variables
     "out of scope" to m (an illegal) variable in the range.  This will
     allow us to prove more equalities (of, e.g. delta) later one.

     This will force us to do "dynamic scope checks" inside the renaming functions.
  *)
  Definition wf_ren {n m:nat} (r : ren n m) : Prop :=
    forall x, (x < n -> (r x) < m) /\ (~(x < n) -> (r x) = m).

  Definition ren_id (n : nat) : ren n n :=
    fun (x:var) =>
      if (lt_dec x n) then x else n.

  Lemma wf_ren_id : forall n, wf_ren (ren_id n).
  Proof.
    unfold wf_ren, ren_id.
    intros.
    destruct (lt_dec x n); split; tauto.
  Qed.  

  Lemma ren_id_id :
    forall (n : nat) x,
      x < n ->
      (ren_id n) x = x.
  Proof.
    intros.
    unfold ren_id.
    destruct (lt_dec x n); auto.
    contradiction.
  Qed.

  Definition ren_shift {n m:nat} (k:nat) (r : ren n m) : ren (k + n) (k + m) :=
    ctxt_app (ren_id k) (fun x => k + (r x)).

  Lemma wf_ren_shift : forall n m k (r : ren n m),
      wf_ren r ->
      wf_ren (ren_shift k r).
  Proof.
    unfold wf_ren, ren_shift, ctxt_app, ren_id.
    intros.
    destruct (lt_dec x k).
    - split; lia.
    - split; intros.
      + assert (x - k < n) by lia.
        apply H in H1.
        lia.
      + assert (~ (x - k) < n) by lia.
        apply H in H1.
        lia.
  Qed.

  Lemma ren_shift_id : forall n k,
      ren_shift k (ren_id n) = ren_id (k + n).
  Proof.
    unfold ren_shift, ren_id, ctxt_app.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x k).
    - destruct (lt_dec x (k + n)).
      + reflexivity.
      + lia.
    - destruct (lt_dec (x - k) n);
      destruct (lt_dec x (k + n)); lia.
  Qed.

  Definition ren_compose {n m X} (r : ren n m) (c : ctxt m X) : ctxt n X :=
    compose c r.

  (* Our insistance that renamings map to m outside their scope means this
     equality holds only for in-scope variables. *)
  Lemma ren_compose_id_l : forall n m X (c : ctxt m X) x,
      x < n ->
      ren_compose (ren_id n) c x = c x.
  Proof.
    unfold ren_compose, compose, ren_id.
    intros.
    destruct (lt_dec x n); auto.
    contradiction.
  Qed.

  Lemma ren_compose_id_r : forall n m (r : ren n m),
      wf_ren r ->
      ren_compose r (ren_id m) = r.
  Proof.
    unfold wf_ren, ren_compose, compose, ren_id.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec (r x) m); auto.
    destruct (lt_dec x n).
    + assert (r x < m). { apply H. assumption. } contradiction.
    + symmetry. apply H. assumption.
  Qed.
  
  Lemma wf_ren_compose :
    forall n m l (r1 : ren n m) (r2 : ren m l),
      wf_ren r1 ->
      wf_ren r2 ->
      @wf_ren n l (ren_compose r1 r2).
  Proof.
    unfold wf_ren, ren_compose, compose.
    intros.
    split; intros.
    - eapply H0. eapply H. assumption.
    - apply H in H1.
      rewrite H1.
      apply H0. lia.
  Qed.

  Lemma ren_compose_shift : forall n m l k (r1 : ren n m) (r2 : ren m l),
      (ren_compose (ren_shift k r1) (ren_shift k r2)) =
        (@ren_shift n l k (ren_compose r1 r2)).
  Proof.
    intros.
    unfold ren_compose, compose, ren_shift, ren_id, ctxt_app.
    apply functional_extensionality.
    intros.
    destruct (lt_dec x k).
    - destruct (lt_dec x k); lia.
    - destruct (lt_dec (k + r1 (x - k)) k).
      lia.
      remember (r1 (x - k)) as X.
      assert (k + X - k = X) by lia.
      rewrite H.
      reflexivity.
  Qed.
  
  (* bijections *)

  Lemma wf_ren_bFun : forall n (r : ren n n),
      wf_ren r -> bFun n r.
  Proof.
    intros. unfold bFun.  unfold wf_ren in H.
    apply H.
  Qed.    
  
  Definition injective_ren {n} (r : ren n n) :=
    bInjective n r.

  Definition surjective_ren {n} (r : ren n n) :=
    bSurjective n r.

  Definition ren_inverses {n} (r r_inv : ren n n) :=
    forall x, x < n -> r_inv (r x) = x /\ r (r_inv x) = x.

  Lemma ren_inverses_comm : forall n (r r_inv : ren n n),
      ren_inverses r r_inv ->
      ren_inverses r_inv r.
  Proof.
    unfold ren_inverses.
    intros.
    split; apply H; auto.
  Qed.
  
  Lemma ren_inverses_exist : forall n (r : ren n n),
      wf_ren r ->
      surjective_ren r ->
      exists r_inv, wf_ren r_inv /\ ren_inverses r r_inv.
  Proof.
    unfold surjective_ren.
    intros.
    assert (bFun n r). apply wf_ren_bFun; auto.
    destruct (bSurjective_bBijective H1 H0) as [r_inv [HR HI]].
    exists (fun x => if lt_dec x n then r_inv x else n).
    split.
    - unfold wf_ren. intros.
      destruct (lt_dec x n); intros.
      + split; intros. apply HR. assumption.
        contradiction.
      + split; intros. contradiction. reflexivity.
    - unfold ren_inverses.
      intros.
      destruct (lt_dec (r x) n).
      + destruct (lt_dec x n).
        * apply HI. assumption.
        * contradiction.
      + destruct (lt_dec x n).
        * assert (r x < n). apply H1. assumption.
          contradiction.
        * contradiction.
  Qed.
  
  Definition bij_ren {n} (r : ren n n) :=
    { r_inv : ren n n &  wf_ren r_inv /\ ren_inverses r r_inv }.

  Lemma bij_ren_id : forall n, bij_ren (ren_id n).
  Proof.
    unfold bij_ren, ren_id, wf_ren, ren_inverses.
    intros.
    exists (ren_id n).
    unfold ren_id.
    split; intros; split; intros.
    - destruct (lt_dec x n); auto.
      contradiction.
    - destruct (lt_dec x n); auto.
      contradiction.
    - destruct (lt_dec x n); auto.
      destruct (lt_dec x n); auto. contradiction.
      contradiction.
    - destruct (lt_dec x n); auto.
      destruct (lt_dec x n); auto. contradiction.
      contradiction.
  Defined.

  
  Definition bij_app {n m} (r1 : ren n n) (r2 : ren m m) : ren (n + m) (n + m) :=
    ctxt_app r1 (fun x => n + (r2 x)).

  Lemma wf_bij_app : forall n m (r1 : ren n n) (r2 : ren m m),
      wf_ren r1 ->
      wf_ren r2 -> 
      wf_ren (bij_app r1 r2).
  Proof.
    unfold wf_ren, bij_app, ctxt_app.
    intros.
    destruct (lt_dec x n).
    - split.
      + apply H in l. lia.
      + intros.
        lia.
    - split.
      + intros. 
        assert (x - n < m) by lia.
        apply H0 in H2.
        lia.
      + intros.
        assert (~ (x - n < m)). lia.
        assert (r2 (x - n) = m). apply H0.  assumption.
        rewrite H3.
        reflexivity.
  Qed.

  Lemma bij_ren_app :
    forall {n m} (r1 : ren n n) (r2 : ren m m)
      (HWF1 : wf_ren r1)
      (HWF2 : wf_ren r2)
      (HBR1 : bij_ren r1)
      (HBR2 : bij_ren r2),
      @bij_ren (n + m) (bij_app r1 r2).
  Proof.
    unfold bij_app, ctxt_app.
    intros.
    unfold bij_ren.
    destruct HBR1 as [r1_inv [HR1 HI1]].
    destruct HBR2 as [r2_inv [HR2 HI2]].
    exists (bij_app r1_inv r2_inv).
    split.
    - apply wf_bij_app; auto.
    - unfold ren_inverses.
      intros.
      unfold bij_app, ctxt_app.
      split.
      + destruct (lt_dec x n).
        * destruct (lt_dec (r1 x) n).
          apply HI1. assumption.
          assert (r1 x < n).
          apply HWF1. assumption.
          contradiction.
        * destruct (lt_dec (n + r2 (x - n)) n).
          lia.
          assert (n + (r2 (x - n)) - n = r2 (x - n)) by lia.
          rewrite H0.
          assert (x - n < m) by lia.
          assert (r2_inv (r2 (x - n)) = x - n).
          { apply HI2. assumption. }
          rewrite H2.
          lia.
      + destruct (lt_dec x n).
        * destruct (lt_dec (r1_inv x) n).
          apply HI1. assumption.
          assert (r1_inv x < n).
          { apply HR1. assumption. }
          lia.
        * destruct (lt_dec (n + r2_inv (x -n)) n).
          lia.
          assert (n + r2_inv (x - n) - n = r2_inv (x - n)) by lia.
          rewrite H0.
          assert (x - n < m) by lia.
          assert (r2(r2_inv (x - n)) = (x -n )).
          { apply HI2. assumption. }
          rewrite H2. lia.
  Defined.

  Lemma bij_app_id : forall n m,
      bij_app (ren_id n) (ren_id m) = ren_id (n + m).
  Proof.
    unfold bij_app, ctxt_app,  ren_id.
    intros.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n); try lia.
    - destruct (lt_dec x (n + m)); try lia.
    - destruct (lt_dec x (n + m)); destruct (lt_dec (x - n) m); try lia.
  Qed.
  
  Definition bij_inv {n} (r : ren n n) (H : bij_ren r) : ren n n :=
    let (r_inv, _) := H in r_inv.

  Lemma bij_inv_id : forall n,
      bij_inv (ren_id n) (bij_ren_id n) = ren_id n.
  Proof.
    intros n.
    reflexivity.
  Qed.

  Lemma wf_bij_ren_inv : forall n (r : ren n n)
      (BR : bij_ren r),
      wf_ren (bij_inv r BR).
  Proof.
    intros.
    destruct BR as [r_inv [HBR HI]].
    simpl. auto.
  Qed.

  Lemma bij_inv_bij :
    forall n (r : ren n n)
      (WFR : wf_ren r)
      (BR : bij_ren r),
      bij_ren (bij_inv r BR).
  Proof.
    intros.
    destruct BR as [r_inv [HBR HI]].
    simpl.
    exists r. split; auto. apply ren_inverses_comm. auto.
  Qed.

  Lemma bij_inv_bij_inv_eq :
    forall n (r : ren n n)
      (WFR : wf_ren r)
      (BR : bij_ren r)
      (HX : bij_ren (bij_inv r BR)),
      (bij_inv (bij_inv r BR) HX) = r.
  Proof.
    intros.
    destruct BR as [r_inv [WRI BRI]].
    simpl in *.
    destruct HX as [r' [WR' BR']].
    simpl in *.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    - unfold ren_inverses in *.
      assert (r x < n). { apply WFR; auto. }
      assert (r' (r_inv (r x)) = r x). { apply BR'. assumption. }
      rewrite <- H0.
      assert (r_inv (r x ) = x). {  apply BRI.  assumption. }
      rewrite H1.
      reflexivity.
    - assert (r' x = n). { apply WR'; auto. }
      assert (r x = n). { apply WFR; auto. }
      rewrite H. rewrite H0. reflexivity.
  Qed.                               
  
  Lemma bij_inv_app :
    forall n m
      (r1 : ren n n) (r2 : ren m m)
      (HWF1 : wf_ren r1)
      (HWF2 : wf_ren r2)
      (HBR1 : bij_ren r1)
      (HBR2 : bij_ren r2),
      bij_inv (bij_app r1 r2) (bij_ren_app r1 r2 HWF1 HWF2 HBR1 HBR2) =
        bij_app (bij_inv r1 HBR1) (bij_inv r2 HBR2).
  Proof.
    intros.
    destruct HBR1 as [r1_inv [HR1 HI1]].
    destruct HBR2 as [r2_inv [HR2 HI2]].
    reflexivity.
  Qed.                  

  Lemma bij_ren_inv :
    forall n (r : ren n n) (BR: bij_ren r),
      wf_ren r ->
      (ren_compose (bij_inv r BR) r) = (ren_id n).
  Proof.
    intros.
    destruct BR as [r_inv [HR HI]].
    simpl.
    apply functional_extensionality.
    intros.
    unfold ren_compose, compose, ren_id.
    destruct (lt_dec x n).
    - apply HI. assumption.
    - assert (r_inv x = n). { apply HR. assumption. }
      rewrite H0.
      apply H.
      lia.
  Qed.

  Lemma bij_ren_inv_elt :
    forall n (r : ren n n) (BR : bij_ren r) x,
      wf_ren r ->
      x < n ->
      x = ((bij_inv r BR) (r x)).
  Proof.
    intros.
    destruct BR as [r_inv [HR HI]].
    simpl.
    apply HI in H0.
    destruct H0.
    symmetry. auto.
  Qed.
  
  Lemma bij_ren_elt : forall n (r : ren n n),
      bij_ren r -> forall x, x < n -> exists y, y < n /\ x = r y.
  Proof.
    unfold bij_ren, wf_ren, ren_inverses.
    intros.
    destruct X as [r_inv [HWF HE]].
    exists (r_inv x).
    split.
    - apply HWF. assumption.
    - symmetry. apply HE. assumption.
  Qed.

  Lemma bij_ren_compose :
    forall n (r1 : ren n n) (r2 : ren n n)
      (WF1 : wf_ren r1),
      bij_ren r1 ->
      bij_ren r2 ->
      bij_ren (ren_compose r1 r2).
  Proof.
    unfold bij_ren, ren_inverses, ren_compose. intros.
    destruct X as [r1_inv [HWF1 HEQ1]].
    destruct X0 as [r2_inv [HWF2 HEQ2]].
    exists (ren_compose r2_inv r1_inv).
    split.
    - apply wf_ren_compose; auto.
    - split.
      + unfold ren_compose, compose.
        assert ((r1 x) < n). { apply WF1. auto. }
        destruct (HEQ2 (r1 x) H0).
        rewrite H1.
        destruct (HEQ1 x H).
        rewrite H3. reflexivity.
      + unfold ren_compose, compose.
        assert ((r2_inv x) < n). { apply HWF2.  auto. } 
        destruct (HEQ1 (r2_inv x) H0).
        rewrite H2.
        destruct (HEQ2 x H).
        rewrite H4.
        reflexivity.
  Defined.

  Lemma bij_ren_app_compose :
    forall n m (r11 r12 : ren n n) (r21 r22 : ren m m)
      (WFR11 : wf_ren r11)
      (WFR12 : wf_ren r12)
      (WFR21 : wf_ren r21)
      (WFR22 : wf_ren r22)
      (HB11 : bij_ren r11)
      (HB12 : bij_ren r12)
      (HB21 : bij_ren r21)
      (HB22 : bij_ren r22),
      ren_compose (bij_app r11 r21) (bij_app r12 r22) =
        bij_app (ren_compose r11 r12) (ren_compose r21 r22).
  Proof.
    intros.
    destruct HB11 as [r11_inv [HR11 HI11]].
    destruct HB12 as [r12_inv [HR12 HI12]].
    destruct HB21 as [r21_inv [HR21 HI21]].
    destruct HB22 as [r22_inv [HR22 HI22]].
    unfold ren_compose.
    unfold bij_app.
    unfold ctxt_app, compose.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    - destruct (lt_dec (r11 x) n).
      + reflexivity.
      + assert (r11 x < n). { apply WFR11. auto. }
        contradiction.
    - destruct (lt_dec (n + r21 (x - n)) n).
      + lia.
      + assert ((n + r21 (x - n) - n) = (r21 (x - n))).
        lia.
        rewrite H.
        reflexivity.
  Qed.

  Lemma ren_compose_app :
    forall m n  X
      (r1 : ren m m)  (r2 : ren n n)
      (HR1 : wf_ren r1) (HR2 : wf_ren r2)
      (HBR1 : bij_ren r1) (HBR2 : bij_ren r2)
      (c : ctxt m X) (d : ctxt n X),
      (ren_compose r1 c) ⊗ (ren_compose r2 d) = 
        ren_compose (bij_app r1 r2) (c ⊗ d).
  Proof.
    intros.
    apply functional_extensionality.
    intros.
    unfold ren_compose, compose, bij_app, ctxt_app.
    destruct (lt_dec x m).
    - destruct (lt_dec (r1 x) m).
      + reflexivity.
      + assert (r1 x < m). { apply HR1. assumption. }
        contradiction.
    - destruct (lt_dec (m + r2 (x - m)) m).
      + lia.
      + assert ((m + (r2 (x - m)) - m) = (r2 (x - m))) by lia.
        rewrite H. reflexivity.
  Qed.        

  Lemma bij_app_inv :
    forall m m' (r1 : ren m m) (r2 : ren m' m')
      (WF1 : wf_ren r1) (WF2 : wf_ren r2)
      (BR1 : bij_ren r1) (BR2 : bij_ren r2),
      bij_app (bij_inv r1 BR1) (bij_inv r2 BR2) =
        bij_inv (bij_app r1 r2) (bij_ren_app r1 r2 WF1 WF2 BR1 BR2).
  Proof.
    intros.
    destruct BR1 as [r1_inv [WFI1 BRI1]].
    destruct BR2 as [r2_inv [FWI2 BRI2]].
    reflexivity.
  Qed.
  
  (* SAZ: the stronger notion of renaming well-formedness, which requires
     out-of-scope variables to be canonical, lets us prove this
     equivalence.
   *) 
  Lemma bij_ren_app_inv_compose_id :
    forall n (r : ren n n)
      (WFR : wf_ren r)
      (HB: bij_ren r),
      ren_compose r (bij_inv r HB) = ren_id n.
  Proof.
    intros.
    destruct HB as [r_inv [HR HI]].
    simpl.
    unfold ren_inverses in HI.
    unfold ren_compose, compose, ren_id.
    apply functional_extensionality.
    intros x.
    destruct (lt_dec x n).
    + apply HI. assumption.
    + assert (r x = n).
      apply WFR. assumption.
      rewrite H.
      apply HR.
      lia.
  Qed.
  
  Lemma ren_sum_compose : forall n (r : ren n n) (c : lctxt n) (d : lctxt n),
      ren_compose r (c ⨥ d) = (ren_compose r c) ⨥ (ren_compose r d).
  Proof.
    intros.
    apply functional_extensionality.
    intros x.
    reflexivity.
  Qed.

  Lemma bij_ren_var :
    forall n (r : ren n n) x y
      (WFR : wf_ren r)
      (H : bij_ren r),
      x < n ->
      y < n ->
      r x = y <-> x = (bij_inv r H) y.
  Proof.
    intros.
    destruct H as [r_inv [HWRI HE]].
    simpl.
    unfold ren_inverses in HE.
    split; intros; subst.
    - specialize (HE _ H0).
      destruct HE.
      rewrite H. reflexivity.
    - specialize (HE _ H1).
      destruct HE.
      assumption.
  Qed.
      
  Lemma ren_delta_compose :
    forall n (r : ren n n) x c
      (WFR : wf_ren r)
      (H : bij_ren r),
      x < n ->
      ren_compose r (n[x ↦ c]) = n[((bij_inv r H)  x) ↦ c].
  Proof.
    intros.
    unfold ren_compose, compose, delta.
    destruct H as [r_inv [HWF HEQ]].
    simpl.
    apply functional_extensionality.
    intros y.
    destruct (Nat.eq_dec x (r y)); subst.
    + unfold ren_inverses in HEQ.
      destruct (Nat.eq_dec (r_inv (r y)) y); subst; auto.
      destruct(lt_dec y n).
      specialize (HEQ y l).
      destruct HEQ. contradiction.
      unfold wf_ren in *.
      assert (r y = n). { apply WFR; auto. }
      lia.
    + destruct (Nat.eq_dec (r_inv x) y).
    - unfold ren_inverses in *.
      specialize (HEQ x H0).
      destruct HEQ.
      subst.
      lia.
    - reflexivity.
  Qed.

  Lemma ren_compose_zero :
    forall n (r : ren n n),
      ren_compose r (zero n) = zero n.
  Proof.
    intros.
    reflexivity.
  Qed.    
    
  
  Lemma ren_one_compose :
    forall n (r : ren n n)
      (WFR : wf_ren r)
      (H : bij_ren r)
      x,
      x < n ->
      ren_compose r (one n x) = one n ((bij_inv r H) x).
  Proof.
    intros.
    unfold one.
    apply ren_delta_compose; auto.
  Qed.

  Lemma ren_SUM_compose :
    forall n (r : ren n n)
      (l : list (lctxt n)),
      ren_compose r (SUM l) = SUM (List.map (ren_compose r) l).
  Proof.
    intros.
    induction l.
    - simpl. reflexivity.
    - simpl. rewrite ren_sum_compose.
      rewrite IHl. reflexivity.
  Qed.
  
End Renamings.  

Module RelationalRenamings.

Definition ren (n m:nat) := ctxt n (var -> Prop).

Definition wf_ren {n m:nat} (r : ren n m) :=
  forall x y, x < n -> r x y -> y < m.

Definition ren_eq (n m:nat) (r1 r2 : ren n m) :=
  forall x y, x < n -> (r1 x y <-> r2 x y).

Infix "≡[ n , m ]" := (ren_eq n m).

#[global] Instance refl_ren_eq : forall n m, Reflexive (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros; auto.
Qed.

#[global] Instance sym_ren_eq : forall n m, Symmetric (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros.
  - rewrite H; tauto.
  - rewrite <- H; tauto.
Qed.

#[global] Instance trans_ren_eq : forall n m, Transitive (ren_eq n m).
Proof.
  intros. repeat red.
  intros. unfold ren_eq in *.
  split; intros.
  - rewrite <- H0; auto. rewrite <- H; tauto.
  - rewrite H; auto. rewrite H0; tauto.
Qed.

(* Some renamings are functional *)
Definition fun_ren {n m} (r : ren n m) : Prop :=
  forall x y z, x < n -> r x y -> r x z -> y = z.

Definition ren_id (n : nat) : ren n n := fun (x y:var) => x = y.

Lemma wf_ren_id : forall n, wf_ren (ren_id n).
Proof.
  unfold wf_ren, ren_id.
  intros. subst. assumption.
Qed.  

Lemma fun_ren_id : forall n, fun_ren (ren_id n).
Proof.
  unfold fun_ren, ren_id.
  intros.
  subst. reflexivity.
Qed.  

Definition ren_zero : ren 0 0 := fun x y => False.

Lemma wf_ren_zero : wf_ren (ren_zero).
Proof.
  unfold wf_ren, ren_zero.
  intros. inversion H0.
Qed.  

Lemma fun_ren_zero : fun_ren (ren_zero).
Proof.
  unfold fun_ren, ren_zero.
  intros. contradiction.
Qed.  

Definition ren_app {n1 m1 n2 m2} (r1 : ren n1 m1) (r2 : ren n2 m2) : ren (n1+n2) (m1+m2) :=
  fun x y =>
    if Compare_dec.lt_dec x n1 then
      if Compare_dec.lt_dec y m1 then
        r1 x y else False
    else
      if Compare_dec.lt_dec y m1 then
        False else
      r2 (x - n1) (y - m1).

Infix "⨣" := (@ren_app _ _ _ _) (at level 50).

Lemma wf_ren_app : forall n1 m1 n2 m2
                     (r1 : ren n1 m1)
                     (r2 : ren n2 m2)
                     (HR1: wf_ren r1)
                     (HR2 : wf_ren r2),
    wf_ren (r1 ⨣ r2).
Proof.
  unfold wf_ren, ren_app.
  intros.
  destruct (lt_dec x n1); destruct (lt_dec y m1); try lia.
  assert ((x - n1)  < n2). { lia. }
  destruct (lt_dec y m2); try lia.
  specialize (HR2 (x-n1) (y-m1) H1 H0).
  lia.
Qed.  

Lemma fun_ren_app : forall n1 m1 n2 m2
                      (r1 : ren n1 m1)
                      (r2 : ren n2 m2)
                      (HR1: fun_ren r1)
                      (HR2 : fun_ren r2),
    fun_ren (r1 ⨣ r2).
Proof.
  unfold fun_ren, ren_app.
  intros.
  destruct (lt_dec x n1); destruct (lt_dec y m1); destruct (lt_dec z m1); try lia.
  - eapply HR1; eauto.
  - assert ((y - m1)  = (z - m1)). { eapply HR2; eauto. lia. }
    lia.
Qed.    

Lemma ren_app_zero_l : forall n m (r : ren n m),
    (ren_zero ⨣ r) ≡[n, m] r.
Proof.
  unfold ren_zero, ren_app, ren_eq.
  intros.
  destruct (lt_dec x 0); destruct (lt_dec y 0); auto.
  - inversion l.
  - inversion l.
  - inversion l.
  - repeat rewrite Nat.sub_0_r. tauto.
Qed.

Lemma ren_app_zero_r : forall n m (r : ren n m)
    (HR:wf_ren r),
    (r ⨣ ren_zero) ≡[n, m] r.
Proof.
  unfold wf_ren, ren_zero, ren_app, ren_eq.
  intros.
  destruct (lt_dec x n); destruct (lt_dec y m); auto.
  - tauto.
  - split; try tauto. intros HY. specialize (HR _ _ l HY). contradiction.
  - split; try tauto. 
  - split; try tauto. 
Qed.  

Lemma ren_app_assoc : forall n1 n2 m1 m2 o1 o2 (r1 : ren n1 n2) (r2 : ren m1 m2) (r3 : ren o1 o2),
    wf_ren r2 ->
    (r1 ⨣ r2) ⨣ r3 ≡[n1 + m1 + o1, n2 + m2 + o2] r1 ⨣ (r2 ⨣ r3).
Proof.
  unfold wf_ren, ren_eq, ren_app. intros.
  destruct (lt_dec x n1).
  - destruct (lt_dec x (n1 + m1)).
    + destruct (lt_dec y n2); destruct (lt_dec y (n2 + m2)); try lia.
      tauto.
    + destruct (lt_dec y n2); try lia.
  - destruct (lt_dec x (n1 + m1)).
    + destruct (lt_dec y (n2 + m2)); try lia.
      * destruct (lt_dec (x - n1) m1); try lia.
        destruct (lt_dec (y - n2) m2); try lia.
        -- tauto.
        -- destruct (lt_dec y n2); try lia.
      * destruct (lt_dec y n2); try lia.
        destruct (lt_dec (x - n1) m1); try lia.
        destruct (lt_dec (y - n2) m2); try lia.
    + destruct (lt_dec (x - n1) m1); try lia.
      destruct (lt_dec y n2); try lia.
      -- destruct (lt_dec y (n2 + m2)); try lia.
      -- destruct (lt_dec (y - n2) m2); destruct (lt_dec y (n2 + m2)); try lia.
         replace (y - (n2 + m2)) with (y - n2 - m2) by lia.
         replace (x - (n1 + m1)) with (x - n1 - m1) by lia.
         reflexivity.
Qed.      
      

Definition function_ren (n m : nat) (f:nat -> nat) : ren n m := fun x y => (f x) = y.

Lemma wf_function_ren : forall n m (f:nat -> nat) (HF: forall x, x < n -> (f x) < m), wf_ren (function_ren n m f).
Proof.
  unfold wf_ren, function_ren.
  intros. subst. auto.
Qed.

Lemma fun_function_ren : forall n m (f:nat -> nat), fun_ren (function_ren n m f).
Proof.
  unfold fun_ren, function_ren.
  intros.
  subst. reflexivity.
Qed.  

Definition shift_ren n' n m (r : ren n m) : ren (n' + n) (n' + m) :=
  (ren_id n') ⨣ r.

Lemma id_ren_app : forall n m, (ren_id n) ⨣ (ren_id m) ≡[n,m] (ren_id (n+m)).
Proof.
  unfold ren_id, ren_eq, ren_app.
  intros.
  split; intros.
  - destruct (lt_dec x n); destruct (lt_dec y n); tauto.
  - destruct (lt_dec x n); destruct (lt_dec y n); lia.
Qed.

Definition ren_compose {n m o} (r1 : ren n m) (r2 : ren m o) : ren n o :=
  fun x y => exists z, r1 x z /\ r2 z y.

Notation "f ;; g" := (@ren_compose _ _ _ f g) (at level 55, right associativity).

Lemma wf_ren_compose : forall n m o (r1 : ren n m) (r2 : ren m o),
    wf_ren r1 -> wf_ren r2 -> wf_ren (r1 ;; r2).
Proof.
  unfold wf_ren, ren_compose.
  intros.
  destruct H2 as [z [HR1 HR2]].
  eauto.
Qed.

Lemma ren_compose_id_l : forall n m (r : ren n m),
    (ren_id n) ;; r ≡[n,m] r.
Proof.
  unfold ren_id, ren_compose, ren_eq.
  intros. split; intros.
  - destruct H0 as [z [HX HR]].
    subst. assumption.
  - exists x. auto.
Qed.

Lemma ren_compose_id_r : forall n m (r : ren n m),
    r ;; (ren_id m) ≡[n,m] r.
Proof.
  unfold ren_id, ren_compose, ren_eq.
  intros. split; intros.
  - destruct H0 as [z [HX HR]].
    subst. assumption.
  - exists y. auto.
Qed.

Lemma ren_compose_assoc : forall n m o p (r1 : ren n m) (r2 : ren m o) (r3 : ren o p),
    (r1 ;; r2) ;; r3 ≡[n,p] r1 ;; (r2 ;; r3).
Proof.
  unfold ren_compose, ren_eq. intros.
  split; intros.
  - destruct H0 as [z [[w [HR1 HR2]] HR3]].
    exists w. split; auto. exists z; auto.
  - destruct H0 as [z [HR1 [w [HR2 HR3]]]].
    exists w. split; auto. exists z; auto.
Qed.

Lemma fun_ren_compose : forall n m o (r1 : ren n m) (r2 : ren m o),
    wf_ren r1 ->
    fun_ren r1 -> fun_ren r2 -> fun_ren (r1 ;; r2).
Proof.
  unfold wf_ren, fun_ren, ren_compose.
  intros.
  destruct H3 as [w1 [HW11 HW12]].
  destruct H4 as [w2 [HW21 HW22]].
  assert (w1 = w2). { eapply H0; eauto. }
  subst.
  eapply H1; eauto.
Qed.  

End RelationalRenamings.


(* Linear Contexts and Renamings -------------------------------------------- *)

(*
  0 -> 1
  1 -> 1
  2 -> _
  3 -> 2
  4 -> 0

  ren 5 3

  l(0) = k0
  l(1) = k1
  l(2) = k2
  l(3) = k3
  l(4) = k4

  cl(0) = k4
  cl(1) = k0 + k1
  cl(2) = k3
  
*)

Import ListNotations.

Fixpoint down_from (n:nat) : list nat :=
  match n with
  | 0 => []
  | S n => n::(down_from n)
  end.

(* Could map between general lists and context, but this may be all we need? *)
Definition lctxt_to_list (n:nat) (c : lctxt n) : list (var * nat) :=
  List.map (fun x => (x, c x)) (down_from n).

Definition list_to_lctxt (n:nat) (l : list (var * nat)) : lctxt n :=
  SUM (List.map (fun '(x,i) => delta n x i) l).

Lemma lctxt_to_list_S : forall (n:nat) (c : lctxt (S n)),
    lctxt_to_list (S n) c = (n,c n)::lctxt_to_list n c.
Proof.
  intros.
  reflexivity.
Qed.  

Lemma list_to_lctxt_hd : forall n x d l,
    list_to_lctxt (S n) ((x,d)::l) = (S n)[x ↦ d] ⨥ (list_to_lctxt n l).
Proof.
  intros.
  unfold list_to_lctxt.
  simpl. reflexivity.
Qed.  

Lemma list_to_lctxt_0 : forall n (c : lctxt n) x,
    n <= x ->
    list_to_lctxt n (lctxt_to_list n c) x = 0.
Proof.
  induction n; intros; simpl in *; auto.
  rewrite lctxt_to_list_S.
  rewrite list_to_lctxt_hd.
  unfold sum.
  unfold delta.
  destruct (Nat.eq_dec n x); try lia.
  simpl.
  rewrite IHn.
  auto.
  lia.
Qed.

Lemma lctxt_to_list_inc : forall n (c : lctxt n),
    forall x, x < n ->
    list_to_lctxt n (lctxt_to_list n c) x = c x.
Proof.
  induction n; simpl.
  - intros. inversion H.
  - intros.
    rewrite lctxt_to_list_S.
    rewrite list_to_lctxt_hd.
    unfold delta, sum.
    destruct (Nat.eq_dec n x).
    subst.
    rewrite list_to_lctxt_0; auto.
    rewrite IHn. reflexivity. lia. 
Qed.

(*           R
  k0 <- 0        0 -> j0
  k1 <- 1        1 -> j1
  k2 <- 2        2 -> j2
    ..           3 -> j3
  kn <- n       ..
                 m -> jm

    D1              D2

    

*)


(* 
Fixpoint sum_pred (p : nat -> Prop) (c : nat -> nat) (n:nat) : nat -> Prop :=
  match n with
  | 0 => fun d => d = 0
  | S n =>
      fun d =>
        (exists d', sum_pred p c n d' /\
                 ((p n -> d = (c n) + d') \/ d = d'))
  end.

Definition preimage_sum {n m:nat} (c : lctxt n) (r : ren n m) (x:nat) (d:nat):=
  sum_pred (fun y => r y x) c n d.

Definition lin_ctxt_ren {n m:nat} (c : lctxt n) (r : ren n m) (l : lctxt m) : Prop :=
  forall x d, x < m -> l x = d -> preimage_sum c r x d.

Definition strengthen (n:nat) (k:nat) : ren n (n-1) :=
  fun x y =>
    if lt_dec x k then y = x else
      if lt_dec k x then y = x - 1
      else False.

*)
      


