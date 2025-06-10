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
    r_b <- bng f'
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

Theorem ws_example_self_seq :
  seq_term ws_term_example ws_term_example.
Proof. apply seq_bag. apply seq_proc_refl. Qed.

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
          (par (par (def 1 (bng 1)) (app 0 1)) (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))))
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) (par (def 1 (bng 1)) (app 0 1)))).
  { apply seq_par_comm. }
  assert (H2 : seq_proc
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) (par (def 1 (bng 1)) (app 0 1)))
          (par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) (par (app 0 1) (def 1 (bng 1)) ))).
  { apply seq_par_cong.
    - reflexivity.
    - assumption. } 
  apply seq_proc_trans with (P2 := par (def 2 (lam (bag 1 2 (par (app 0 0) (def 1 (tup 0 0)))))) (par (def 1 (bng 1)) (app 0 1))).
  - assumption.
  - assumption.
Qed. 
  

(* Identity Example *)   
Example id_ex : term := 
  bag 1 3 
    (par  (def 0 (lam (bag 0 1 (def 1 (tup 0 0)))))
          (par (def 0 (bng 0)) 
               (par (app 0 1) (def 1 (tup 2 2))))).

Theorem id_ex_is_ws : forall m n, 
    ws_term m n id_ex.
Proof. intros m n. apply ws_bag. apply ws_par.
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

Lemma delta_app_zero_r : forall m n x y, 
                      x < m -> 
                      (@ctxt_app _ m n (m[x ↦ y]) (zero n)) = (m + n)[x ↦ y].
Proof. intros. apply functional_extensionality. unfold ctxt_app, delta, zero. intros x0. destruct (lt_dec x0 m).
  - reflexivity.
  - destruct (Nat.eq_dec x x0).
    subst.
    contradiction.
    reflexivity.
Qed.

Lemma sum_zero_gen_r : forall {n m} (c : lctxt n),
    c ⨥ (zero m) = c.
Proof.
  intros. apply functional_extensionality.
  intros. unfold sum. unfold zero. lia.
Qed.

Lemma delta_add_zero : forall m n x y, 
                      x < (m + n) -> 
                      (m + n)[x ↦ y] = (m + n)[x ↦ y] ⨥ (zero m).
Proof. intros. 
assert ((m + n)[x ↦ y] ⨥ (zero m) = (m + n)[x ↦ y]).
{ apply sum_zero_gen_r. }
symmetry. assumption.
Qed.

(* How do we treat/how do we want to treat '0[x \mapsto y]' and/or 'zero 0' ? *)
Lemma n_is_0_implies_zero_0 : forall x y,
  0[x ↦ y] = zero 0.
Proof. intros. subst. unfold delta, zero. 
Admitted.

(* Work-in-progress...

Current thoughts/issues: 
- Not sure about assumptions '0 < m' and '2 < n'. I think these are needed to ensure
  scoping makes sense.
- Showing distributivity of '⊗ (zero n)' over '⨥' was tedious. I might be missing something,
or mayber there is a useful lemma here.

! Still unable to apply wf_par after refactoring to get contexts with '⨥' not '⊗'. I thought
the issue was that wf_par expects G1, G2 and D1, D2 to (respectively) have the 'same size'. 
However, the error that actually appears is 'Unable to unify "n + n" with "3 + n".' 
*)
Theorem id_ex_is_wf : forall m n, 
    0 < m /\ 2 < n -> wf_term m n (zero m) (zero n) id_ex.
Proof. intros m n H. destruct H as [Hm Hn].  
eapply wf_bag with  (G' := m[0 ↦ 1]) (D' :=  (n[0 ↦ 2] ⨥ n[1 ↦ 2] ⨥ n[2 ↦ 2])). 
    - intros x H. assert (Hx: x = 0) by lia; subst. apply delta_id. 
    - intros x H. simpl. assert (Hx: x = 0 \/ x = 1 \/ x = 2) by lia. 
      destruct Hx as [Hx | [Hx | Hx]]. all : (subst; unfold sum, delta, zero; simpl; lia).
    - assert (H : @ctxt_app _ m m (m [0 ↦ 1]) (zero m) = ((m + m) [0 ↦ 1])). 
      { apply delta_app_zero_r. assumption. } 
      assert (H' : ((m + m) [0 ↦ 1]) = ((m + m) [0 ↦ 1]) ⨥ (zero m)). 
      { apply delta_add_zero. lia. }
      replace ((m + m) [0 ↦ 1]) with ((m + m) [0 ↦ 1] ⨥ zero m) in H. clear H'. 
      replace (m [0 ↦ 1] ⊗ zero m) with ((m + m) [0 ↦ 1] ⨥ zero m). 
      assert ((zero n) = (zero n) ⨥ (zero n)). 
      { unfold zero, sum. simpl. reflexivity. }
      assert (@ctxt_app _ n n (n[0 ↦ 2] ⨥ n[1 ↦ 2] ⨥ n[2 ↦ 2]) (zero n)
               = (((n + n)[0 ↦ 2] ⨥ (n + n)[1 ↦ 2] ⨥ (n + n)[2 ↦ 2]) ⨥ (zero n))).
      { replace (zero n) with ((zero n) ⨥ (zero n)).
        assert (((@ctxt_app _ n n (n [0 ↦ 2] ⨥ n [1 ↦ 2]) (zero n)) ⨥ (n [2 ↦ 2] ⊗ zero n))
                = @ctxt_app _ n n ((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) (zero n ⨥ zero n)).
        { apply lctxt_sum_app_dist with (D11 := ((n [0 ↦ 2] ⨥ n [1 ↦ 2]))) (D21 := (n [2 ↦ 2]))
                                        (D12 := (zero n)) (D22 := (zero n)). }
        assert (((@ctxt_app _ n n (n [0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ n n (n [1 ↦ 2]) (zero n))) 
                = (@ctxt_app _ n n (n [0 ↦ 2] ⨥ n [1 ↦ 2]) ((zero n) ⨥ (zero n)))).
        { apply lctxt_sum_app_dist with (D11 := (n [0 ↦ 2])) (D21 := (n [1 ↦ 2]))
                                        (D12 := (zero n)) (D22 := (zero n)). }
        replace (zero n) with ((zero n) ⨥ (zero n)) in H1. 
        replace (@ctxt_app _ n n (n [0 ↦ 2] ⨥ n [1 ↦ 2]) (zero n ⨥ zero n)) with 
                ((@ctxt_app _ n n (n [0 ↦ 2]) (zero n)) ⨥ (@ctxt_app _ n n (n [1 ↦ 2]) (zero n))) in H1.
        clear H2.
        replace ((zero n) ⨥ (zero n)) with (zero n) in H1.
        assert ((@ctxt_app _ n n (n [0 ↦ 2]) (zero n)) = (n + n)[0 ↦ 2]). { apply delta_app_zero_r. lia. }
        replace (@ctxt_app _ n n (n [0 ↦ 2]) (zero n)) with ((n + n) [0 ↦ 2]) in H1. clear H2.
        assert ((@ctxt_app _ n n (n [1 ↦ 2]) (zero n)) = (n + n)[1 ↦ 2]). { apply delta_app_zero_r. lia. }
        replace (@ctxt_app _ n n (n [1 ↦ 2]) (zero n)) with ((n + n) [1 ↦ 2]) in H1. clear H2.
        assert ((@ctxt_app _ n n (n [2 ↦ 2]) (zero n)) = (n + n)[2 ↦ 2]). { apply delta_app_zero_r. lia. }
        replace (@ctxt_app _ n n (n [2 ↦ 2]) (zero n)) with ((n + n) [2 ↦ 2]) in H1. clear H2.
        assert (((((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2]) ⨥ (zero n))
                = (((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2])).
        { apply sum_zero_gen_r with (c := (((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2])). }
        replace (((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2]) with 
                ((((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2]) ⨥ zero n) in H1. clear H2.
        replace (zero n ⨥ zero n) with (zero n). replace (zero n ⨥ zero n) with (zero n) in H1. 
        symmetry; assumption. 
        }
        replace (((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⊗ zero n) with 
                ((((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2]) ⨥ zero n).
        (* Commented this out as it is still throwing the error noted above.
        
        apply wf_par with (G1 := ((m + m) [0 ↦ 1])) (G2 := (zero m)) 
                          (D1 := (((n + n) [0 ↦ 2] ⨥ (n + n) [1 ↦ 2]) ⨥ (n + n) [2 ↦ 2]))
                          (D2 := (zero n)).
        *)

Admitted.
  

(* Tuples in tuples *)

(* nu {} {r_0, r_1, r_2, r_3, r_4, r_5} :
r_4 <- (r_0, r_1)
r_1 <- (r_0, r_2)
r_2 <- (r_0, r_0) 
r_5 <- (r_0, r_4) 

... trying to have r_5 of the form (r_0, (r_0, (r_0, (r_0, r_0)))) 
*)

Example tup_in_tup : term := 
bag 0 6 
  (par (def 4 (tup 0 1))
       (par (def 1 (tup 0 2))
            (par (def 2 (tup 0 0))
                 (def 5 (tup 0 4))))).

Theorem tup_in_tup_is_ws : forall m n,
    ws_term m n tup_in_tup.
Proof. intros m n. apply ws_bag. apply ws_par. 
  - apply ws_def. lia. 
    apply ws_tup; lia.
  - apply ws_par.
    + apply ws_def. lia. 
      apply ws_tup; lia.
    + apply ws_par.
      * apply ws_def. lia. 
        apply ws_tup; lia.
      * apply ws_def. lia. 
        apply ws_tup; lia.
Qed.

Lemma delta_dist : forall {n} x y z w,
  x < n -> (n[x ↦ y] ⨥ n[x ↦ z])w = n[x ↦ y]w + n[x ↦ z]w.
Proof. intros. destruct w.
  - destruct x. 
    + assert ((n [0 ↦ y] ⨥ n [0 ↦ z]) = n [0 ↦ y + z]). { apply delta_sum. }
      rewrite H0; apply delta_id. 
    + assert ((n [S x ↦ y] ⨥ n [S x ↦ z]) = n [S x ↦ y + z]). { apply delta_sum. }
      rewrite H0; apply delta_neq; lia.
  - destruct x. 
    + assert ((n [0 ↦ y] ⨥ n [0 ↦ z]) = n [0 ↦ y + z]). { apply delta_sum. }
      rewrite H0; apply delta_neq; lia.
    + assert ((n [S x ↦ y] ⨥ n [S x ↦ z]) = n [S x ↦ y + z]). { apply delta_sum. }
      rewrite H0; clear H0. assert ((S w) = (S x) \/ ~((S w) = (S x))) by lia. destruct H0. 
        * rewrite H0. assert (n [S x ↦ y] (S x) = y). { apply delta_id. } 
          rewrite H1; clear H1. 
          assert (n [S x ↦ z] (S x) = z). { apply delta_id. } 
          rewrite H1; clear H1. apply delta_id.
        * assert (n [S x ↦ y] (S w) = 0). { apply delta_neq; lia. } 
          rewrite H1; clear H1. 
          assert (n [S x ↦ z] (S w) = 0). { apply delta_neq; lia. } 
          rewrite H1; clear H1. apply delta_neq; lia.
Qed.
     

Theorem tup_in_tup_is_wf : forall m n,
    0 < m /\ 0 < n -> wf_term m n (zero m) (zero n) tup_in_tup.
Proof. intros m n H. destruct H as [Hm Hn].
eapply wf_bag with (G' := zero m) (D' := (n[0 ↦ 2] ⨥ n[1 ↦ 2] ⨥ n[2 ↦ 2] ⨥ n[3 ↦ 2] ⨥ n[4 ↦ 2] ⨥ n[5 ↦ 2])). 
- intros x H. inversion H.
- intros x H. inversion H.  
  + assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 5 = 2).
    { unfold sum. simpl. apply delta_id. }
    rewrite H0; lia.
  + inversion H1. 
    assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 4 = 2).
    { unfold sum. simpl.
      replace (S (S (n [5 ↦ 2] 4))) with ((n [5 ↦ 2] 4) + 2) by lia. 
      assert (n [5 ↦ 2] 4 = 0) by (apply delta_neq; lia). 
      rewrite H2; lia. }
    rewrite H2; lia. clear m0 H1 H0.
    inversion H3.
    assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 3 = 2).
    { unfold sum. simpl.
      replace (S (S (n [5 ↦ 2] 3))) with ((n [5 ↦ 2] 3) + 2) by lia. 
      assert (n [5 ↦ 2] 3 = 0) by (apply delta_neq; lia). 
      rewrite H0; lia. }
    rewrite H0; lia. clear m1 H3 H2.
    inversion H1. 
    assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 2 = 2).
    { unfold sum. simpl.
      replace (S (S (n [5 ↦ 2] 2))) with ((n [5 ↦ 2] 2) + 2) by lia. 
      assert (n [5 ↦ 2] 2 = 0) by (apply delta_neq; lia). 
      rewrite H2; lia. }
    rewrite H2; lia. clear m0 H1 H0. 
    inversion H3.
    assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 1 = 2).
    { unfold sum. simpl.
      replace (S (S (n [5 ↦ 2] 1))) with ((n [5 ↦ 2] 1) + 2) by lia. 
      assert (n [5 ↦ 2] 1 = 0) by (apply delta_neq; lia). 
      rewrite H0; lia. }
    rewrite H0; lia. clear m1 H3 H2. 
    inversion H1.
    assert ((((((n [0 ↦ 2] ⨥ n [1 ↦ 2]) ⨥ n [2 ↦ 2]) ⨥ n [3 ↦ 2]) ⨥ n [4 ↦ 2]) ⨥ n [5 ↦ 2]) 0 = 2).
    { unfold sum. simpl.
      replace (S (S (n [5 ↦ 2] 0))) with ((n [5 ↦ 2] 0) + 2) by lia. 
      assert (n [5 ↦ 2] 0 = 0) by (apply delta_neq; lia). 
      rewrite H2; lia. }
    rewrite H2; lia. clear m0 H1 H0.
    inversion H3.
-

Admitted.