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
    (par (def 2 (lam (bag 1 2 (par (app 0 0) 
                                   (def 1 (tup 0 0))))))
         (par (app 0 1)
              (def 1 (bng 1))))).
(* nu {f, f'} {r_a, r_b, r_c} :
    r_c <- lam r_0 {f''} {r_0, r_1}
           f'' r_0
           r_1 <- (r_0, r_0)
    f r_a
    r_b <- !f'
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
    + apply ws_def. lia. 
      apply ws_bng. lia.
Qed.

(* Sanity check *)
Theorem ws_example_self_seq :
  seq_term ws_term_example ws_term_example.
Proof. apply seq_bag. apply seq_proc_refl. Qed.

(* Commuting par's to make a structually equivalent term... *)
Example seq_to_ws_example : term :=
  (bag 2 3 
    (par (par (def 1 (bng 1))
              (app 0 1))
         (def 2 (lam (bag 1 2 (par (app 0 0) 
                                   (def 1 (tup 0 0)))))))).

Theorem is_seq_to_ws_example :
  seq_term seq_to_ws_example ws_term_example.
Proof. apply seq_bag. 
  assert (H0 : seq_proc
          (par (def 1 (bng 1)) (app 0 1))
          (par (app 0 1) (def 1 (bng 1)))).
  { apply seq_par_comm. }
  assert (H1 : seq_proc
          (par (par (def 1 (bng 1)) (app 0 1)) 
               (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))))
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0))))))
               (par (def 1 (bng 1)) (app 0 1)))).
  { apply seq_par_comm. }
  assert (H2 : seq_proc
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) 
               (par (def 1 (bng 1)) (app 0 1)))
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) 
               (par (app 0 1) (def 1 (bng 1)) ))).
  { apply seq_par_cong.
    - reflexivity.
    - assumption. } 
  apply seq_proc_trans with (P2 := par (def 2 (lam (bag 1 2 (par (app 0 0) 
                                                                 (def 1 (tup 0 0)))))) 
                                       (par (def 1 (bng 1)) (app 0 1))).
  - assumption.
  - assumption.
Qed. 
  

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
Proof. intros. apply functional_extensionality. 
unfold ctxt_app, delta, zero. 
intros x0. destruct (lt_dec x0 m).
  - reflexivity.
  - destruct (Nat.eq_dec x x0).
    subst.
    contradiction.
    reflexivity.
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

(* Reshaping lctxt for id_ex_is_wf *)
Lemma refactor_lctxt : forall n,
  ((3 + n)[0 ↦ 2] ⨥ (3 + n)[1 ↦ 2] ⨥ (3 + n)[2 ↦ 2]) =
  (((3 + n)[0 ↦ 1]) ⨥ ((3 + n)[0 ↦ 1] ⨥ ((3 + n)[1 ↦ 1]  ⨥ (3 + n)[1 ↦ 1] ⨥ (3 + n)[2 ↦ 2]))).
Proof. intros n.
assert (H : (3 + n) [0 ↦ 2] = (3 + n) [0 ↦ 1] ⨥ (3 + n) [0 ↦ 1]). 
{ symmetry; apply delta_sum. } 
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
{ symmetry; apply delta_sum. } 
rewrite H; clear H.
assert (H : (((3 + n) [0 ↦ 1] ⨥ ((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1])) ⨥ (3 + n) [2 ↦ 2]) =
            (3 + n) [0 ↦ 1] ⨥ ((((3 + n) [1 ↦ 1]) ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [2 ↦ 2])).
{ apply sum_assoc_rev. }
rewrite H; clear H.
reflexivity.
Qed.


(* Work-in-progress...

Current thoughts/issues: 
! splitting up unrestricted lctxt context to apply wf_par on (par P1 P2)
  for function used in both P1 and P2

- should work out redunacies in reshaping lctxts
*)
Theorem id_ex_is_wf : forall m n, 
    0 < m /\ 2 < n -> wf_term m n (zero m) (zero n) id_ex.
Proof. intros m n H. destruct H as [Hm Hn].  
eapply wf_bag with  (G' := 1[0 ↦ 1]) (D' :=  (3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2])). 
- intros x H. 
  assert (Hx: x = 0) by lia; subst. 
  apply delta_id. 

- intros x H. simpl. 
  assert (Hx: x = 0 \/ x = 1 \/ x = 2) by lia. 
  destruct Hx as [Hx | [Hx | Hx]]. 
  all : (subst; unfold sum, delta, zero; simpl; lia).

- (* reshaping G *)
  assert (H : @ctxt_app _ 1 m (1[0 ↦ 1]) (zero m) = ((1 + m) [0 ↦ 1])). 
  { apply delta_app_zero_r. lia. } 
  assert (H' : ((1 + m) [0 ↦ 1]) = (zero (1 + m)) ⨥ ((1 + m) [0 ↦ 1])). 
  { apply delta_add_zero_l. lia. }
  replace ((1 + m) [0 ↦ 1]) with ((zero (1 + m)) ⨥ (1 + m) [0 ↦ 1]) in H. clear H'. 
  replace (1[0 ↦ 1] ⊗ zero m) with ((zero (1 + m)) ⨥ (1 + m) [0 ↦ 1]). 

  assert ((zero n) = (zero n) ⨥ (zero n)). 
  { unfold zero, sum. simpl. reflexivity. }

  (* reshaping D *)
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
    replace (zero n) with ((zero n) ⨥ (zero n)) in H1. 
    replace (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) (zero n ⨥ zero n)) with 
            ((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n))) in H1.
    clear H2.
    replace ((zero n) ⨥ (zero n)) with (zero n) in H1.
    assert ((@ctxt_app _ 3 n (3 [0 ↦ 2]) (zero n)) = (3 + n)[0 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) with ((3 + n) [0 ↦ 2]) in H1. clear H2.
    assert ((@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) = (3 + n)[1 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) with ((3 + n) [1 ↦ 2]) in H1. clear H2.
    assert ((@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) = (3 + n)[2 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) with ((3 + n) [2 ↦ 2]) in H1. clear H2.
    assert (((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2]) ⨥ (zero (3 + n)))
            = (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
    { apply sum_zero_r with (c := (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])). }
    symmetry; assumption. }

  (* replace D using reshaping from above and from lemma *)
  replace (((3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ⨥ 3[2 ↦ 2]) ⊗ zero n) with 
          ((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
  replace (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2]) with 
           (((3 + n)[0 ↦ 1]) ⨥ ((3 + n)[0 ↦ 1] ⨥ ((3 + n)[1 ↦ 1]  ⨥ (3 + n)[1 ↦ 1] ⨥ (3 + n)[2 ↦ 2]))).
  
  apply wf_par.
    + assert ((3 + n) [0 ↦ 1] = (3 + n) [0 ↦ 1] ⨥ (zero (3 + n))).
      { symmetry; apply sum_zero_r. }
      rewrite H2; clear H2.
      apply wf_def. lia.
      apply wf_lam. 
      eapply wf_bag with (G' := (zero (1 + m))) (D' := 1[0 ↦ 2]). 
        * intros x H'. inversion H'.
        * intros x H'. inversion H'. 
          subst. assert (1[0 ↦ 2]0 = 2). unfold zero. reflexivity.
          rewrite H2. lia. 
          inversion H3.
        * assert ((@ctxt_app _ 1 1 (1 [0 ↦ 2]) (1 [0 ↦ 1])) = (1 + 1)[1 ↦ 1] ⨥ (1 + 1)[0 ↦ 2]).
          { unfold ctxt_app, sum. apply functional_extensionality. 
            intros x. destruct x. simpl. 
            apply delta_id.
            simpl. destruct x. 
            apply delta_id.
            apply delta_neq. lia.  }
          rewrite H2.
          apply wf_def. lia.
          assert ((1 + 1) [0 ↦ 2] = (1 + 1)[0 ↦ 1] ⨥ (1 + 1)[0 ↦ 1]).
          { symmetry; apply delta_sum. }
          rewrite H3. clear H3.
          apply wf_tup. lia. lia.
    + assert ((1 + m) [0 ↦ 1] = (1 + m) [0 ↦ 1] ⨥ (zero (1 + m))).
      { symmetry; apply sum_zero_r. }
      rewrite H2; clear H2.
      apply wf_par. 
      assert ((3 + n) [0 ↦ 1] = (3 + n) [0 ↦ 1] ⨥ (zero (3 + n))). 
      { symmetry; apply sum_zero_r. }
      rewrite H2; clear H2.
      apply wf_def. lia.
      apply wf_bng. lia.
      replace (zero (1 + m)) with (zero (1 + m) ⨥ zero (1 + m)).
      apply wf_par.
      
      (* -> apply wf_app.
        
      How to preserve the usage of unrestricted context across manipulations ?
      ... seems like I need a one ctxt in both P1 and P2, but don't know how to 
      manipulate (1 + m)[0 -> 1] to get that.  *)

Admitted.
  

(* Tuples in tuples *)

Lemma delta_dist : forall {n} x y z w,
  x < n -> (n[x ↦ y] ⨥ n[x ↦ z])w = n[x ↦ y]w + n[x ↦ z]w.
Proof. intros. destruct w.
  - destruct x. 
    + assert ((n [0 ↦ y] ⨥ n [0 ↦ z]) = n [0 ↦ y + z]). 
      { apply delta_sum. }
      rewrite H0; apply delta_id. 
    + assert ((n [S x ↦ y] ⨥ n [S x ↦ z]) = n [S x ↦ y + z]). 
      { apply delta_sum. }
      rewrite H0; apply delta_neq; lia.
  - destruct x. 
    + assert ((n [0 ↦ y] ⨥ n [0 ↦ z]) = n [0 ↦ y + z]). 
      { apply delta_sum. }
      rewrite H0; apply delta_neq; lia.
    + assert ((n [S x ↦ y] ⨥ n [S x ↦ z]) = n [S x ↦ y + z]). 
      { apply delta_sum. }
      rewrite H0; clear H0. 
      assert ((S w) = (S x) \/ ~((S w) = (S x))) by lia. 
      destruct H0. 
        * rewrite H0. 
          assert (n [S x ↦ y] (S x) = y). 
          { apply delta_id. } 
          rewrite H1; clear H1. 
          assert (n [S x ↦ z] (S x) = z). 
          { apply delta_id. } 
          rewrite H1; clear H1. 
          apply delta_id.
        * assert (n [S x ↦ y] (S w) = 0). 
        { apply delta_neq; lia. } 
          rewrite H1; clear H1. 
          assert (n [S x ↦ z] (S w) = 0). 
          { apply delta_neq; lia. } 
          rewrite H1; clear H1. 
          apply delta_neq; lia.
Qed.


(* Nested tuples *)
Example tup_simple : term :=
bag 1 4
  (par (def 1 (tup 0 0))
       (par (def 2 emp)
            (par (def 3 (tup 1 2))
                 (app 0 3)))).
(* nu {} {r_0, r_1, r_2}
r_1 <- (r_0, r_0)
r_2 <- emp
r_3 <- (r_1, r_2)
f r_3
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
      + apply ws_app. lia. lia. 
Qed.

(* Thoughts/issues :
- Can't eapply with lctxts naively; need to consider future rewrites up front.
  (need to rethink original choice of D')    

*)
Theorem tup_simple_is_wf : forall m n,
  0 < m /\ 0 < n -> wf_term m n (zero m) (zero n) tup_simple.
Proof. intros m n H. destruct H as [Hm Hn]. 
eapply wf_bag with (G' := 1[0 ↦ 1]) (D' := 3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2] ⨥ 3[3 ↦ 2]).
- intros x H. destruct x.
  + apply delta_id.
  + inversion H. inversion H1.  

- intros x H. inversion H. 
  (* Need to think about abbrv. this. *)
  + assert (((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2] ⨥ 3[3 ↦ 2]) 3 = 2). 
    { unfold sum. simpl. apply delta_id. }
    rewrite H0. lia.
  + inversion H1. assert (((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2] ⨥ 3[3 ↦ 2]) 2 = 2).
    { unfold sum. simpl. 
      replace (S (S (3 [3 ↦ 2] 2))) with ((3 [3 ↦ 2] 2) + 2) by lia.  
      assert (3 [3 ↦ 2] 2 = 0) by (apply delta_neq; lia). 
      rewrite H2; lia. }
    rewrite H2. lia.
    inversion H3. assert (((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2] ⨥ 3[3 ↦ 2]) 1 = 2).
    { unfold sum. simpl. 
      replace (S (S (3 [3 ↦ 2] 1))) with ((3 [3 ↦ 2] 1) + 2) by lia.  
      assert (3 [3 ↦ 2] 1 = 0) by (apply delta_neq; lia). 
      rewrite H4; lia. }
    rewrite H4; lia.
    inversion H5. assert (((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2] ⨥ 3[3 ↦ 2]) 0 = 2).
    { unfold sum. simpl. 
      replace (S (S (3 [3 ↦ 2] 0))) with ((3 [3 ↦ 2] 0) + 2) by lia.  
      assert (3 [3 ↦ 2] 0 = 0) by (apply delta_neq; lia). 
      rewrite H6; lia. }
    rewrite H6; lia. 
    inversion H7.

- assert ((@ctxt_app _ 1 m (1 [0 ↦ 1]) (zero m)) = (1 + m) [0 ↦ 1]).
  { apply delta_app_zero_r. lia. }
  rewrite H; clear H.
  assert (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2] ⨥ 3[3 ↦ 2]) (zero n)
               = ((3 + n)[0 ↦ 2] ⨥ (3 + n)[1 ↦ 2] ⨥ (3 + n)[2 ↦ 2]⨥ (3 + n)[3 ↦ 2])).
  { assert (zero n = (zero n) ⨥ (zero n)). 
    { symmetry; apply sum_zero_r. }
    rewrite H.
    assert (((@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2]) (zero n)) ⨥ (3[3 ↦ 2] ⊗ zero n))
                = @ctxt_app _ 3 n ((3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2]) ⨥ 3[3 ↦ 2]) (zero n ⨥ zero n)).
    { apply lctxt_sum_app_dist with (D11 := ((3[0 ↦ 2] ⨥ 3[1 ↦ 2] ⨥ 3[2 ↦ 2]))) (D21 := (3[3 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). } 
    replace (@ctxt_app _ 3 n (((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2]) ⨥ 3 [3 ↦ 2]) (zero n ⨥ zero n)) with 
            ((@ctxt_app _ 3 n ((3 [0 ↦ 2] ⨥ 3 [1 ↦ 2]) ⨥ 3 [2 ↦ 2]) (zero n)) ⨥ (3 [3 ↦ 2] ⊗ zero n)).
    clear H0. 
    rewrite H.
    assert (((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n))) 
                = (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ((zero n) ⨥ (zero n)))).
    { apply lctxt_sum_app_dist with (D11 := (3[0 ↦ 2])) (D21 := (3[1 ↦ 2]))
                                    (D12 := (zero n)) (D22 := (zero n)). }
    replace (@ctxt_app _ 3 n (3[0 ↦ 2] ⨥ 3[1 ↦ 2]) ((zero n) ⨥ (zero n))) with 
            ((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n))).
    clear H0.
    symmetry in H; rewrite H.
    assert ((@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) = (3 + n)[0 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[0 ↦ 2]) (zero n)) with ((3 + n) [0 ↦ 2]). clear H.
    assert ((@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) = (3 + n)[1 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[1 ↦ 2]) (zero n)) with ((3 + n) [1 ↦ 2]). clear H.
    assert ((@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) = (3 + n)[2 ↦ 2]). 
    { apply delta_app_zero_r. lia. }
    replace (@ctxt_app _ 3 n (3[2 ↦ 2]) (zero n)) with ((3 + n) [2 ↦ 2]). clear H.
    symmetry. 
    apply sum_zero_l with (c := (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])).
    symmetry. 
    apply sum_zero_l. apply sum_zero_l. apply sum_zero_l. }
  rewrite H. clear H. 

  (* Rewrite D here *)

  apply wf_par with (G1 := zero m) (G2 := zero m)
                    (D2 := (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2])) (D1 := zero (3 + n)).
    + assert ((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 2]) ⨥ (3 + n) [2 ↦ 2]) = 
              (one (3 + n) 1) ⨥ ((3 + n)[0 ↦ 2] ⨥ (3 + n)[1 ↦ 1] ⨥ (3 + n)[2 ↦ 2])).
      { assert ((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1] = (3 + n) [1 ↦ 2]). 
        apply delta_sum. 
        unfold one. 
        assert ((3 + n) [1 ↦ 1] ⨥ (((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [2 ↦ 2]) = 
                ((3 + n) [1 ↦ 1] ⨥ ((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 1])) ⨥ (3 + n) [2 ↦ 2]).
        apply sum_assoc. 
        rewrite H0. clear H0.
        assert (((3 + n) [1 ↦ 1] ⨥ ((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 1])) = 
                (((3 + n) [1 ↦ 1] ⨥ (3 + n) [0 ↦ 2]) ⨥ (3 + n) [1 ↦ 1])).
        apply sum_assoc. 
        rewrite H0; clear H0.
        assert (((3 + n) [1 ↦ 1] ⨥ (3 + n) [0 ↦ 2]) = 
                ((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 1])). 
        apply sum_commutative. 
        rewrite H0. clear H0.
        assert ((((3 + n) [0 ↦ 2] ⨥ (3 + n) [1 ↦ 1]) ⨥ (3 + n) [1 ↦ 1]) =
                ((3 + n) [0 ↦ 2] ⨥ ((3 + n) [1 ↦ 1] ⨥ (3 + n) [1 ↦ 1]))). 
        apply sum_assoc_rev. 
        rewrite H0; clear H0.
        rewrite H. reflexivity. }
    rewrite H. apply wf_def. lia.
    apply wf_tup. 
    (*-> apply wf_tup
      Need to refactor all of the lctxts. Original choice was poor.
    *)
Admitted.

