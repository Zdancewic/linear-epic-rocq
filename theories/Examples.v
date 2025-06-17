From Stdlib Require Import
  Arith   
  Logic.FunctionalExtensionality         
  Classes.RelationClasses
  Morphisms
  Program.Basics
  List
  Lia.

From LEpic Require Import Syntax.
From LEpic Require Import Contexts.


(* Playing around with ws and seq definitions... *)
Example ws_term_example : term :=
  (bag 2 3 
    (par (def 2 (lam (bag 1 2 (par (app 0 1) 
                                   (def 1 (tup 0 0))))))
         (par (app 0 1)
              (par (def 1 (bng 1))
                   (def 2 emp))))).
(* nu {f, f'} {r_a, r_b, r_c} :
    r_c <- lam r_0 {f''} {r_0, r_1}
           f'' r_1
           r_1 <- (r_0, r_0)
    f r_b
    r_b <- !f'
    r_c <- emp
*)

Theorem ws_term_example_is_ws :
  ws_term 2 3 ws_term_example.
Proof. apply ws_bag. simpl. apply ws_par.
  - apply ws_def. lia. 
    apply ws_lam. 
    apply ws_bag; simpl. 
    apply ws_par. apply ws_app. lia. lia.
    apply ws_def. lia.
    apply ws_tup. lia. lia.
  - apply ws_par. 
    + apply ws_app. lia. lia.
    + apply ws_par. 
      * apply ws_def. lia.
        apply ws_bng. lia.
      * apply ws_def. lia.
        apply ws_emp.
Qed.

(* Sanity check *)
Theorem ws_example_self_seq :
  seq_term ws_term_example ws_term_example.
Proof. apply seq_bag. apply seq_proc_refl. Qed.

(* Commuting par's to make a structually equivalent term... *)
Example seq_to_ws_example : term :=
  (bag 2 3 
    (par (par (par (def 1 (bng 1))
                   (def 2 emp))
              (app 0 1))
         (def 2 (lam (bag 1 2 (par (app 0 1) 
                                   (def 1 (tup 0 0)))))))).

Theorem is_seq_to_ws_example :
  seq_term seq_to_ws_example ws_term_example.
Proof. apply seq_bag. 
  assert (H0 : seq_proc
          (par (par (def 1 (bng 1)) (def 2 emp)) (app 0 1))
          (par (app 0 1) (par (def 1 (bng 1)) (def 2 emp)))).
  { apply seq_par_comm. }
  assert (H1 : seq_proc
          (par (par (par (def 1 (bng 1)) (def 2 emp)) (app 0 1)) 
               (def 2 (lam (bag 1 2 (par (app 0 1) (def 1 (tup 0 0)))))))
          (par (def 2 (lam (bag 1 2 (par (app 0 1) (def 1 (tup 0 0))))))
               (par (par (def 1 (bng 1)) (def 2 emp)) (app 0 1)))).
  { apply seq_par_comm. }
  assert (H2 : seq_proc
          (par (def 2 (lam (bag 1 2 (par (app 0 1) (def 1 (tup 0 0)))))) 
               (par (par (def 1 (bng 1)) (def 2 emp)) (app 0 1)))
          (par (def 2 (lam (bag 1 2 (par (app 0 1) (def 1 (tup 0 0)))))) 
               (par (app 0 1) (par (def 1 (bng 1)) (def 2 emp))))).
  { apply seq_par_cong.
    - reflexivity.
    - assumption. } 
  apply seq_proc_trans with (P2 := par (def 2 (lam (bag 1 2 (par (app 0 1) 
                                                                 (def 1 (tup 0 0)))))) 
                                       (par (par (def 1 (bng 1)) (def 2 emp)) (app 0 1))).
  - assumption.
  - assumption.
Qed. 
  
(* General wf'dness proof sketch:  
  To show wf_term m n (zero m) (zero n) ws_term_example,
   forall 0 < m, 3 < n:
  - eapply wf_bag with G' := (2[0 ↦ 1] ⨥ 2[1 ↦ 1]) and 
    D' := (2[0 ↦ 0] ⨥ 2[1 ↦ 2] ⨥ 2[2 ↦ 2]) 
  - Distribute '⊗ zero m' and '⊗ zero' over ⨥ in G'⊗ G 
    and D'⊗ D (see delta_app_zero).
  - Reshape results as: 
    (zero (2 + m)) ⨥ ((2 + m)[0 ↦ 1] ⨥ (2 + m)[1 ↦ 1])) 
    and 
    ((3 + n)[0 ↦ 0] ⨥ 3[2 ↦ 1]) ⨥ (3[1 ↦ 1] ⨥ 3[1 ↦ 1] ⨥ 3[2 ↦ 1]).
      + That is, use sum_assoc, sum_commutativity, delta_sum, etc.
        to reshape lctxts so that they can be split up in 
        applications of wf_par, used in wf_def/tup/app, etc. 
  - Apply wf's. *)


(* Identity Example *)   
Example id_ex : term := 
  bag 1 3 
    (par  (def 0 (lam (bag 0 1 (def 1 (tup 0 0)))))
          (par (def 0 (bng 0)) 
               (par (app 0 1) (def 1 (tup 2 2))))).
(* 
nu {f} {r_a, r_b, r_c}
  r_a <- lam r_1 . {} {r_1}
             r_1 <- (r_0, r_0)
  r_a <- !f
  f r_b
  r_b <- (r_c, r_c)
*)

(* Proof of well-structuredness *)
Theorem id_ex_is_ws : forall m n, 
    ws_term m n id_ex.
Proof. intros m n. apply ws_bag. 
apply ws_par.
- apply ws_def. lia. 
  apply ws_lam; apply ws_bag; apply ws_def. lia.
  apply ws_tup; simpl. 
  lia. lia.
- apply ws_par. 
    + apply ws_def. lia. 
      apply ws_bng. lia.
    + apply ws_par.
        * apply ws_app. lia. lia.
        * apply ws_def. lia. 
          apply ws_tup. 
          lia. lia.
Qed.

(* Appending zero 'extends context' / pads with zeros *)
Lemma delta_app_zero_r : forall m n x y, 
                      x < m -> 
                      (@ctxt_app _ m n (m[x ↦ y]) (zero n)) = (m + n)[x ↦ y].
Proof.
intros.
apply functional_extensionality.
unfold ctxt_app, delta, zero.
intros x0. 
destruct (lt_dec x0 m).
destruct (lt_dec x m); try lia.
destruct (Nat.eq_dec x x0).
destruct (lt_dec x (m+n)); try lia.
destruct (lt_dec x (m+n)); try lia. 
destruct (lt_dec x (m+n)); try lia. 
destruct (Nat.eq_dec x x0); try lia.
Qed.

(* Summing with zero context yields original context *)
Lemma delta_add_zero_r : forall m n x y, 
                      x < (m + n) -> 
                      (m + n)[x ↦ y] = (m + n)[x ↦ y] ⨥ (zero (m + n)).
Proof. intros. 
assert ((m + n)[x ↦ y] ⨥ (zero (m + n)) = (m + n)[x ↦ y]).
{ apply sum_zero_r. }
symmetry. assumption.
Qed.

Lemma delta_add_zero_l : forall m n x y, 
                      x < (m + n) -> 
                      (m + n)[x ↦ y] = (zero (m + n)) ⨥ (m + n)[x ↦ y].
Proof. intros. 
assert ((zero (m + n)) ⨥ (m + n)[x ↦ y] = (m + n)[x ↦ y]).
{ apply sum_zero_l. }
symmetry. assumption.
Qed.

(* Reverse of associativity lemma *)
Lemma sum_assoc_rev : forall {n} (c : lctxt n) (d : lctxt n) (e : lctxt n),
    (d ⨥ e) ⨥ c = d ⨥ (e ⨥ c).
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. lia.
Qed.

Ltac dsum_tac :=
  match goal with 
    |- _ => symmetry; apply delta_sum
  end.

(* Reshaping lctxt for id_ex_is_wf *)
Lemma refactor_lctxt : forall n,
  ((3 + n)[0 ↦ 2] ⨥ (3 + n)[1 ↦ 2] ⨥ (3 + n)[2 ↦ 2]) =
  (((3 + n)[0 ↦ 1]) ⨥ ((3 + n)[0 ↦ 1] ⨥ ((3 + n)[1 ↦ 1]  ⨥ (3 + n)[1 ↦ 1] ⨥ (3 + n)[2 ↦ 2]))).
Proof. intros n.
assert (H : (3 + n) [0 ↦ 2] = (3 + n) [0 ↦ 1] ⨥ (3 + n) [0 ↦ 1]). 
dsum_tac.
rewrite H; clear H.
assert (((3 + n) [0 ↦ 1] ⨥ (3 + n) [0 ↦ 1]) ⨥ (3 + n) [1 ↦ 2] =
        (3 + n) [0 ↦ 1] ⨥ ((3 + n) [0 ↦ 1] ⨥ (3 + n) [1 ↦ 2])).
{ apply sum_assoc_rev. }
rewrite H; clear H.
assert (H : ((3 + n) [0 ↦ 1] ⨥ ((3 + n) [0 ↦ 1] ⨥ (3 + n) [1 ↦ 2])) ⨥ (3 + n) [2 ↦ 2] = 
        (3 + n) [0 ↦ 1] ⨥ (((3 + n) [0 ↦ 1] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
{ apply sum_assoc_rev. }
rewrite H; clear H.
assert (H : (3 + n) [1 ↦ 2] = (3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1]). 
dsum_tac.
rewrite H; clear H.
assert (H : (((3 + n) [0 ↦ 1] ⨥ ((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1])) ⨥ (3 + n) [2 ↦ 2]) =
            (3 + n) [0 ↦ 1] ⨥ ((((3 + n) [1 ↦ 1]) ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [2 ↦ 2])).
{ apply sum_assoc_rev. }
rewrite H; clear H.
reflexivity.
Qed.


Theorem id_ex_is_wf : forall m n, 
    0 < m /\ 2 < n -> wf_term m n (zero m) (zero n) id_ex.
Proof. intros m n H. destruct H as [Hm Hn].  
eapply wf_bag with  (G' := 1[0 ↦ 1]) (D' :=  (3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2])). 
- intros x H. 
  assert (Hx: x = 0) by lia; subst. 
  apply delta_id; lia.

- intros x H. simpl. 
  assert (Hx: x = 0 \/ x = 1 \/ x = 2) by lia. 
  destruct Hx as [Hx | [Hx | Hx]]. 
  all : (subst; unfold sum, delta, zero; simpl; lia).

- apply wf_par with (G1:=(zero(1+m))) (G2:=(1+m)[0↦1]) (D1:=(3+n)[0↦1])
                    (D2:=((3 + n) [0 ↦ 1] ⨥ (((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [2↦2]))).
  + apply wf_def with (D':=zero(3+n)); try lia.
    assert ((3 + n) [0 ↦ 1] = one (3 + n) 0 ⨥ zero (3 + n)).
    { symmetry; apply sum_zero_r. }
    rewrite H; clear H. reflexivity.
    apply wf_lam; try reflexivity.
    eapply wf_bag with (G' := (zero (1 + m))) (D' := 1[0 ↦ 2]). 
      * intros x H'. inversion H'.
      * intros x H'. inversion H'. 
        subst. assert (1[0 ↦ 2]0 = 2). unfold zero. reflexivity.
        rewrite H. lia. 
        inversion H0.
      * apply wf_def with (D':=(1+1)[0↦2]); try lia.
        assert ((@ctxt_app _ 1 1 (1 [0 ↦ 2]) (1 [0 ↦ 1])) = (1 + 1)[1 ↦ 1] ⨥ (1 + 1)[0 ↦ 2]).
        { unfold ctxt_app, sum. apply functional_extensionality. 
          intros x. destruct x. simpl. 
          apply delta_id. lia.
          simpl. destruct x. simpl.
          replace (S (2 [0 ↦ 2] 1)) with (2 [0 ↦ 2] 1 + 1) by lia. 
          simpl. apply delta_id. lia.
          apply delta_neq. lia. }
        rewrite H. reflexivity.
        apply wf_tup; try lia. 
        simpl. unfold ctxt_app. intros x H. simpl. reflexivity.
        simpl. unfold sum, one. intros x H. 
        destruct x. simpl. apply delta_id. lia.
        apply delta_neq. lia.
  + apply wf_par with (G1:=(1+m)[0↦1]) (G2:=(zero(1+m))) (D1:=(3 + n) [0 ↦ 1])
                      (D2:=(3 + n) [1 ↦ 1] ⨥ ((3 + n) [1 ↦ 1] ⨥ (3 + n) [2 ↦ 2])).
      * apply wf_def with (D':=(zero(3+n))); try lia.
        assert ((3 + n) [0 ↦ 1] = (3 + n) [0 ↦ 1] ⨥ (zero (3 + n))). 
        { symmetry; apply sum_zero_r. }
        rewrite H; clear H. reflexivity.
        apply wf_bng; try lia; try reflexivity.
      * apply wf_par with (G1:=(zero(1+m))) (G2:=(zero(1+m))) (D1:=(3 + n) [1 ↦ 1])
                        (D2:=(3 + n) [1 ↦ 1] ⨥ (3 + n) [2 ↦ 2]).
        apply wf_app; try lia; try reflexivity. 
        apply wf_def with (D':=(3 + n) [2 ↦ 2]); try lia; try reflexivity.
        apply wf_tup; try lia; try reflexivity.
        unfold one. symmetry. 
        assert ((3 + n) [2 ↦ 1] ⨥ (3 + n) [2 ↦ 1] = (3+n) [2 ↦ 2]).
        { apply delta_sum. } 
        rewrite H; clear H. reflexivity.
        assert (zero (1 + m) ⨥ zero (1 + m) = zero(1 + m)).
        { apply sum_zero_r. }
        rewrite H; clear H; try reflexivity.
        reflexivity.
      * assert ((S m) [0 ↦ 1] ⨥ (zero (S m)) = (S m) [0 ↦ 1]).
        { apply sum_zero_r. }
        simpl. rewrite H; clear H. reflexivity.
      * assert ((((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [2 ↦ 2]) = 
                ((3 + n) [1 ↦ 1] ⨥ ((3 + n) [1 ↦ 1] ⨥ (3 + n) [2 ↦ 2]))).
        { apply sum_assoc_rev. }
        rewrite H; reflexivity.
  + simpl. assert ((@ctxt_app _ 1 m (1[0 ↦ 1])(zero m)) = (S m)[0 ↦ 1]). 
    { apply delta_app_zero_r; try lia. }
    rewrite H; clear H. 
    assert (zero (S m) ⨥ (S m) [0 ↦ 1] = (S m) [0 ↦ 1]) by (apply sum_zero_l).
    rewrite H; clear H. reflexivity.
  + assert ((zero n) = (zero n) ⨥ (zero n)). 
    { unfold zero, sum. simpl. reflexivity. }
    assert (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2]) (zero n)
            = ((3 + n)[0 ↦ 2] ⨥ (3 + n)[1 ↦ 2] ⨥ (3 + n)[2 ↦ 2])).
    { replace (zero n) with ((zero n) ⨥ (zero n)).
    assert (((@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) (zero n)) ⨥ (3[2 ↦ 2] ⊗ zero n))
            = @ctxt_app _ 3 n ((3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ⨥ 3[2 ↦ 2]) (zero n ⨥ zero n)).
    { apply lctxt_sum_app_dist with (D11 := ((3[0 ↦ 2] ⨥ 3[1 ↦ 2]))) (D21 := (3[2 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). }
    assert (((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n))) 
            = (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ((zero n) ⨥ (zero n)))).
    { apply lctxt_sum_app_dist with (D11 := (3[0 ↦ 2])) (D21 := (3[1 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). }
    replace (zero n) with ((zero n) ⨥ (zero n)) in H0. 
    replace (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) (zero n ⨥ zero n)) with 
            ((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n))) in H0.
    clear H1.
    replace ((zero n) ⨥ (zero n)) with (zero n) in H0.
    assert ((@ctxt_app _ 3 n (3 [0 ↦ 2]) (zero n)) = (3 + n)[0 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) with ((3 + n) [0 ↦ 2]) in H0. clear H1.
    assert ((@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) = (3 + n)[1 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) with ((3 + n) [1 ↦ 2]) in H0. clear H1.
    assert ((@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) = (3 + n)[2 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) with ((3 + n) [2 ↦ 2]) in H0. clear H1.
    assert (((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2]) ⨥ (zero (3 + n)))
            = (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
    { apply sum_zero_r with (c := (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])). }
    symmetry; assumption. }
    replace (((3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ⨥ 3[2 ↦ 2]) ⊗ zero n) with 
          ((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
    replace (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2]) with 
           (((3 + n)[0 ↦ 1]) ⨥ ((3 + n)[0 ↦ 1] ⨥ ((3 + n)[1 ↦ 1]  ⨥ (3 + n)[1 ↦ 1] ⨥ (3 + n)[2 ↦ 2]))).
    reflexivity.
    symmetry; apply refactor_lctxt.   
Qed.
  

(* Nested tuples *)
Example tup_simple : term :=
bag 1 4
  (par (def 1 (tup 0 0))
       (par (def 2 emp)
            (par (def 3 (tup 1 2))
                 (def 3 (bng 0))))).
(* nu {} {r_0, r_1, r_2}
r_1 <- (r_0, r_0)
r_2 <- emp
r_3 <- (r_1, r_2)
r_3 <- !f
*)


(* Proof of well-structuredness *)
Theorem tup_simple_is_ws : forall m n,
  ws_term m n tup_simple.
Proof. intros m n. apply ws_bag; apply ws_par.
  - apply ws_def. lia.
    apply ws_tup. lia. lia.
  - apply ws_par. 
    apply ws_def. lia.
    apply ws_emp. 
    apply ws_par.
      + apply ws_def. lia. 
        apply ws_tup. lia. lia.
      + apply ws_def. lia.
        apply ws_bng. lia. 
Qed.


Lemma refactor_D' : forall n,
((((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 2]) ⨥ (4 + n) [2 ↦ 2]) ⨥ (4 + n) [3 ↦ 2]) =
(((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) ⨥ 
 ((4 + n) [2 ↦ 1] ⨥ 
  (((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1] ⨥ (4 + n) [3 ↦ 1]) ⨥ 
   (4 + n) [3 ↦ 1]))).
Proof. intros n.
assert ((((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1] ⨥ (4 + n) [3 ↦ 1]) ⨥ 
         (4 + n) [3 ↦ 1]) =
        ((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1]) ⨥ 
        ((4 + n) [3 ↦ 1] ⨥ (4 + n) [3 ↦ 1])).
{ apply sum_assoc_rev. }
rewrite H; clear H.
assert ((4 + n) [3 ↦ 1] ⨥ (4 + n) [3 ↦ 1] = (4 + n) [3 ↦ 2]).
{ apply delta_sum. }
rewrite H; clear H.
assert (((4 + n) [2 ↦ 1] ⨥ (((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [3 ↦ 2])) = 
        (((4 + n) [2 ↦ 1] ⨥ ((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1])) ⨥ (4 + n) [3 ↦ 2])).
{ apply sum_assoc. }
rewrite H; clear H.
assert (((4 + n) [2 ↦ 1] ⨥ ((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1])) =
        (((4 + n) [2 ↦ 1] ⨥ (4 + n) [2 ↦ 1]) ⨥ (4 + n) [1 ↦ 1])).
{ apply sum_assoc. }
rewrite H; clear H.
assert ((4 + n) [2 ↦ 1] ⨥ (4 + n) [2 ↦ 1] = (4 + n) [2 ↦ 2]).
{ apply delta_sum. }
rewrite H; clear H.
assert (((4 + n) [2 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) = ((4 + n) [1 ↦ 1] ⨥ (4 + n) [2 ↦ 2])).
{ apply sum_commutative. }
rewrite H; clear H.
assert ((((4 + n) [1 ↦ 1] ⨥ (4 + n) [2 ↦ 2]) ⨥ (4 + n) [3 ↦ 2]) = 
        (4 + n) [1 ↦ 1] ⨥ ((4 + n) [2 ↦ 2] ⨥ (4 + n) [3 ↦ 2])).
{ apply sum_assoc_rev. }
rewrite H; clear H.   
assert (((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) ⨥ 
        ((4 + n) [1 ↦ 1] ⨥ ((4 + n) [2 ↦ 2] ⨥ (4 + n) [3 ↦ 2])) =
        (((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [1 ↦ 1]) ⨥ 
        ((4 + n) [2 ↦ 2] ⨥ (4 + n) [3 ↦ 2])).
{ apply sum_assoc. }
rewrite H; clear H.    
assert ((((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [1 ↦ 1]) = 
        ((4 + n) [0 ↦ 2] ⨥ ((4 + n) [1 ↦ 1] ⨥ (4 + n) [1 ↦ 1]))).
{ apply sum_assoc_rev. }
rewrite H; clear H.    
assert ((4 + n) [1 ↦ 1] ⨥ (4 + n) [1 ↦ 1] = (4 + n) [1 ↦ 2]).
{ apply delta_sum. }
rewrite H; clear H.
apply sum_assoc_rev.
Qed.


Theorem tup_simple_is_wf : forall m n,
  0 < m /\ 0 < n -> wf_term m n (zero m) (zero n) tup_simple.
Proof. intros m n H. destruct H as [Hm Hn]. 
eapply wf_bag with (G' := 1[0 ↦ 1]) (D' := 4[0 ↦ 2] ⨥ 4[1 ↦ 2] ⨥ 4[2 ↦ 2] ⨥ 4[3 ↦ 2]).
- (* forall x, x < m' -> (G' x) = 1 *)
  intros x H. destruct x.
  + apply delta_id. lia.
  + inversion H. inversion H1.  

- (* forall x, x < n' -> (D' x) = 2 \/ (D' x) = 0 *)
  intros x H. simpl. 
  assert (Hx: x = 0 \/ x = 1 \/ x = 2 \/ x = 3) by lia. 
  destruct Hx as [Hx | [Hx | [Hx | Hx]]]. 
  all : (subst; unfold sum, delta, zero; simpl; lia).
  
- (* wf_proc (1 + m) (4 + n) (G' ⊗ G) (D' ⊗ D) P) *)

  (* Refactor (G' ⊗ G) as a sum to be 'split up' by applying wf_par *)
  assert ((@ctxt_app _ 1 m (1 [0 ↦ 1]) (zero m)) = (1 + m) [0 ↦ 1]).
  { apply delta_app_zero_r. lia. }
  rewrite H; clear H.
  assert ((zero (1 + m)) ⨥ (1 + m) [0 ↦ 1] = (1 + m) [0 ↦ 1]).
  { apply sum_zero_l. }
  symmetry in H; rewrite H.

  (* Refactor (D' ⊗ D) as a sum to be 'split up' by applying wf_par;
     first, distribute ⊗ (zero n) across sum. *)
  assert (@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2] ⨥ 4[2 ↦ 2] ⨥ 4[3 ↦ 2]) (zero n)
               = ((4 + n)[0 ↦ 2] ⨥ (4 + n)[1 ↦ 2] ⨥ (4 + n)[2 ↦ 2]⨥ (4 + n)[3 ↦ 2])).
  { assert (zero n = (zero n) ⨥ (zero n)). 
    { symmetry; apply sum_zero_r. }
    rewrite H0.
    assert (((@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2] ⨥ 4[2 ↦ 2]) (zero n)) ⨥ (4[3 ↦ 2] ⊗ zero n))
                = @ctxt_app _ 4 n ((4[0 ↦ 2] ⨥ 4[1 ↦ 2] ⨥ 4[2 ↦ 2]) ⨥ 4[3 ↦ 2]) (zero n ⨥ zero n)).
    { apply lctxt_sum_app_dist with (D11 := ((4[0 ↦ 2] ⨥ 4[1 ↦ 2] ⨥ 4[2 ↦ 2]))) (D21 := (4[3 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). } 
    replace (@ctxt_app _ 4 n (((4 [0 ↦ 2] ⨥ 4[1 ↦ 2]) ⨥ 4[2 ↦ 2]) ⨥ 4[3 ↦ 2]) (zero n ⨥ zero n)) with 
            ((@ctxt_app _ 4 n ((4 [0 ↦ 2] ⨥ 4[1 ↦ 2]) ⨥ 4[2 ↦ 2]) (zero n)) ⨥ (4[3 ↦ 2] ⊗ zero n)).
    clear H1. 
    rewrite H0.
    assert ((@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2])(zero n ⨥ zero n)) ⨥ (@ctxt_app _ 4 n (4[2 ↦ 2]) (zero n ⨥ zero n)) 
                = (@ctxt_app _ 4 n ((4[0 ↦ 2] ⨥ 4[1 ↦ 2]) ⨥ 4[2 ↦ 2]) (zero n ⨥ zero n))).
    { apply lctxt_sum_app_dist with (D11 := (4[0 ↦ 2] ⨥ 4[1 ↦ 2])) (D21 := (4[2 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). }
    replace (@ctxt_app _ 4 n ((4[0 ↦ 2] ⨥ 4[1 ↦ 2]) ⨥ 4[2 ↦ 2]) (zero n ⨥ zero n)) with 
            ((@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2])(zero n ⨥ zero n)) ⨥ 
             (@ctxt_app _ 4 n (4[2 ↦ 2]) (zero n ⨥ zero n))).
    clear H1.
    assert (((@ctxt_app _ 4 n (4[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 4 n (4[1 ↦ 2]) (zero n))) 
                = (@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2]) ((zero n) ⨥ (zero n)))).
    { apply lctxt_sum_app_dist with (D11 := (4[0 ↦ 2])) (D21 := (4[1 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). }
    replace (@ctxt_app _ 4 n (4[0 ↦ 2] ⨥ 4[1 ↦ 2]) ((zero n) ⨥ (zero n))) with 
            ((@ctxt_app _ 4 n (4[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 4 n (4[1 ↦ 2]) (zero n))).
    clear H1.
    symmetry in H0; rewrite H0.
    assert ((@ctxt_app _ 4 n (4[0 ↦ 2]) (zero n)) = (4 + n)[0 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 4 n (4[0 ↦ 2]) (zero n)) with ((4 + n) [0 ↦ 2]). clear H1.
    assert ((@ctxt_app _ 4 n (4[1 ↦ 2]) (zero n)) = (4 + n)[1 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 4 n (4[1 ↦ 2]) (zero n)) with ((4 + n) [1 ↦ 2]). clear H1.
    assert ((@ctxt_app _ 4 n (4[2 ↦ 2]) (zero n)) = (4 + n)[2 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 4 n (4[2 ↦ 2]) (zero n)) with ((4 + n) [2 ↦ 2]). clear H1.
    assert ((@ctxt_app _ 4 n (4[3 ↦ 2]) (zero n)) = (4 + n)[3 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 4 n (4[3 ↦ 2]) (zero n)) with ((4 + n) [3 ↦ 2]). clear H1.
    reflexivity. }
  rewrite H0. clear H0. 

  (* Rewrite using refactor_D' lemma proved above *)
  replace ((((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 2]) ⨥ (4 + n) [2 ↦ 2]) ⨥ (4 + n) [3 ↦ 2]) 
  with (((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1]) ⨥ 
        ((4 + n) [2 ↦ 1] ⨥ 
         (((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1] ⨥ (4 + n) [3 ↦ 1]) ⨥ 
          (4 + n) [3 ↦ 1]))).

  apply wf_par with (G1 := zero (1 + m)) (G2 := (1 + m) [0 ↦ 1])
                    (D1 := ((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1])) 
                    (D2 := ((4 + n) [2 ↦ 1] ⨥ 
                            (((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1] ⨥ (4 + n) [3 ↦ 1]) ⨥ 
                             (4 + n) [3 ↦ 1]))).
    + (* Reshape to apply wf_def. *)
      assert ((4 + n) [0 ↦ 2] ⨥ (4 + n) [1 ↦ 1] = (4 + n) [1 ↦ 1] ⨥ (4 + n) [0 ↦ 2]).
      { apply sum_commutative. }
      rewrite H0; clear H0.
      apply wf_def with (D':=(4+n)[0↦2]). lia. 
      reflexivity.
      apply wf_tup; try lia. reflexivity.
       (* Reshape to apply wf_tup. *)
      assert ((4 + n) [0 ↦ 2] = (4 + n) [0 ↦ 1] ⨥ (4 + n) [0 ↦ 1]).
      { symmetry; apply delta_sum. }
      rewrite H0; clear H0. 
      reflexivity.
    + rewrite H. apply wf_par with (G1:=(zero(1+m))) (G2:=(1+m)[0↦1]) (D1:=(4 + n) [2 ↦ 1])
                                   (D2:=((((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [3 ↦ 1]) ⨥ (4 + n) [3↦ 1])).
        * (* Reshape to apply wf_def. *)
          assert ((4 + n) [2 ↦ 1] = (4 + n) [2 ↦ 1] ⨥ (zero (4 + n))).
          { symmetry; apply sum_zero_r. }
          rewrite H0; clear H0.
          apply wf_def with (D':=zero(4+n)); try lia; try reflexivity.
          apply wf_emp; try reflexivity.
        * rewrite H. apply wf_par with (G1:=(zero(1+m))) (G2:=(1+m)[0↦1]) 
                                       (D1:=(((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [3 ↦ 1]))
                                       (D2:=(4+n)[3↦ 1]).
          (* Reshape to apply wf_def. *)
          assert (((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1]) ⨥ (4 + n) [3 ↦ 1] =
                  (4 + n) [3 ↦ 1] ⨥ ((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1])).
          { apply sum_commutative. }
          rewrite H0; clear H0. 
          apply wf_def with (D':=((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1])); try lia; try reflexivity.
          (* Reshape to apply wf_tup. *)
          assert ((4 + n) [2 ↦ 1] ⨥ (4 + n) [1 ↦ 1] = (4 + n) [1 ↦ 1] ⨥ (4 + n) [2 ↦ 1]).
          { apply sum_commutative. }
          rewrite H0; clear H0.
          apply wf_tup; try lia; try reflexivity.
          (* Reshape to apply wf_def *)
          assert ((4 + n) [3 ↦ 1] = (4 + n) [3 ↦ 1] ⨥ (zero (4 + n))).
          { symmetry; apply sum_zero_r. }
          rewrite H0; clear H0.
          apply wf_def with (D':=(zero(4+n))); try lia; try reflexivity.
          apply wf_bng; try lia; try reflexivity. reflexivity. reflexivity.
        * reflexivity.
        * reflexivity. 
    + reflexivity.
    + reflexivity.
    + symmetry; apply refactor_D'.
Qed. 

