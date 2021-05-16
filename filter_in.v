Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import List.

Import ListNotations.

Section FilterIn.

  Variable A : Type.

  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.


  Fixpoint take_while (f : A -> bool) (l : list A) :=
    match l with
    | [] => []
    | x::xs => if f x then [x] else x :: take_while f xs
    end.

  Fixpoint drop_while (f : A -> bool) (l : list A) :=
    match l with
    | [] => []
    | x::xs => if f x then xs else drop_while f xs
    end.

  Fixpoint drop_last (l : list A) :=
    match l with
    | [] => []
    | [x] => []
    | x::xs => x :: drop_last xs
    end.

  Fixpoint take_while_val (v : A) (l : list A) :=
    match l with
    | [] => []
    | x::xs => if eq_dec x v then [x] else x :: take_while_val v xs
    end.

  Fixpoint drop_while_val (v : A) (l : list A) :=
    match l with
    | [] => []
    | x::xs => if eq_dec x v then xs else drop_while_val v xs
    end.

  Theorem in_dec :
    forall (x : A) (l : list A),
      In x l \/ ~ In x l.
  Proof.
    induction l.
    - right; apply in_nil.
    - destruct (eq_dec a x).
      + subst.
        left; apply in_eq.
      + destruct IHl.
        left; simpl.
        right; apply H.
        right; simpl.
        unfold not; intro.
        destruct H0; contradiction.
  Qed.

  Theorem in_filter_in_source :
    forall (x : A) (l : list A) (f : A -> bool),
      In x (filter f l) -> In x l.
  Proof.
    intros.
    induction l.
    - inversion H.
    - destruct (eq_dec a x).
      + subst.
        simpl; left; reflexivity.
      + simpl in H.
        remember (f a); destruct b.
        * simpl in H.
          destruct H.
          contradiction.
          simpl; right.
          apply IHl in H; apply H.
        * simpl; right.
          apply IHl in H; apply H.
  Qed.

  Theorem not_in_source_not_in_filtered :
    forall (x : A) (l : list A) (f : A -> bool),
      ~ In x l -> ~ In x (filter f l).
  Proof.
    intros.
    induction l.
    - simpl; intro.
      apply H0.
    - simpl.
      subst.
      apply not_in_cons in H; destruct H.
      remember (f a); destruct b.
      + apply not_in_cons.
        split.
        apply H.
        apply IHl; apply H0.
      + apply IHl; apply H0.
  Qed.

  Lemma filter_true_in :
    forall (A : Type) (a : A) (l : list A) (f : A -> bool),
      f a = true -> In a l -> In a (filter f l).
  Proof.
    intros.
    rewrite filter_In.
    split.
    apply H0.
    apply H.
  Qed.

  Lemma filter_false_not_in :
      forall (A : Type) (a : A) (l : list A) (f : A -> bool),
        f a = false -> ~ In a (filter f l).
  Proof.
    intros.
    rewrite filter_In.
    unfold not.
    intros.
    destruct H0.
    rewrite H in H1.
    inversion H1.
  Qed.

  Lemma app_cons_cons_not_nil :
    forall  (A : Type) (x y : A) (l1 l2 l3 : list A),
      [] <> l1 ++ x :: l2 ++ y :: l3.
  Proof.
    intros.
    rewrite app_comm_cons.
    apply app_cons_not_nil.
  Qed.

  Lemma app_cons_cons_not_one :
    forall  (A : Type) (x y z: A) (l1 l2 l3 : list A),
      [z] <> l1 ++ x :: l2 ++ y :: l3.
  Proof.
    intros.
    unfold not.
    intros.
    destruct l1.
    destruct l2.
    destruct l3.
    simpl in H.
    discriminate H.
    discriminate H.
    discriminate H.
    simpl in H.
    assert (z <> a). {
      inversion H.
      apply app_cons_cons_not_nil in H2.
      unfold not.
      intros.
      apply H2.
    }
    inversion H.
    apply app_cons_cons_not_nil in H3.
    apply H3.
  Qed.

  Lemma filter_all_false_is_empty :
    forall (A : Type) (l : list A) (f : A -> bool),
      (forall (a : A),  In a l -> f a = false) -> filter f l = [].
  Proof.
    intros.
    induction l.
    - simpl.
      reflexivity.
    - simpl.
      simpl in H.
      remember (f a).
      destruct b.
      symmetry in Heqb.
      apply eq_true_false_abs in Heqb.
      destruct Heqb.
      + apply (H a).
        left.
        reflexivity.
      + apply IHl.
        intros.
        apply (H a0).
        right.
        apply H0.
  Qed.

  Theorem filter_false_count_occ :
    forall (a : A) (l : list A) (f : A -> bool),
     f a = false -> count_occ eq_dec (filter f l) a = 0.
  Proof.
    intros.
    rewrite <- count_occ_not_In.
    rewrite filter_In.
    unfold not.
    intros.
    destruct H0.
    rewrite H in H1.
    inversion H1.
  Qed.

  Theorem filter_true_count_occ :
    forall (a : A) (l : list A) (f : A -> bool),
      f a = true -> count_occ eq_dec (filter f l) a = count_occ eq_dec l a.
  Proof.
    intros.
    induction l.
    - simpl.
      reflexivity.
    - simpl.
      remember (f a0).
      remember (eq_dec a0 a).
      destruct s.
      + subst.
        rewrite H.
        rewrite <- IHl.
        apply count_occ_cons_eq.
        reflexivity.
      + subst.
        remember (f a0).
        destruct b.
        rewrite <- IHl.
        apply count_occ_cons_neq.
        apply n.
        apply IHl.
  Qed.

  Lemma filter_empty_false :
    forall (x : A) (l : list A) (f : A -> bool),
      In x l -> filter f l = [] -> f x = false.
  Proof.
    intros.
    induction l.
    - contradiction.
    - simpl in H.
      simpl in H0.
      remember (f a).
      destruct b.
      + inversion H0.
      + destruct (eq_dec a x).
        * subst.
          symmetry.
          apply Heqb.
        * apply IHl.
          inversion H.
          destruct H.
          contradiction.
          apply H.
          apply H1.
          apply H0.
  Qed.

  Lemma filter_identical_true :
    forall (x : A) (l : list A) (f : A -> bool),
      In x l -> filter f l = l -> f x = true.
  Proof.
    intros.
    rewrite <- H0 in H.
    rewrite filter_In in H.
    destruct H.
    apply H1.
  Qed.

  Theorem divide_list :
    forall (l: list A), exists (l1 l2 : list A), l = l1 ++ l2.
  Proof.
    intros.
    induction l.
    - exists [], [].
      auto.
    - exists [a], l.
      auto.
  Qed.

  Lemma cons_elm_not_eq_list :
    forall (a : A) (l: list A), l <> a :: l.
  Proof.
    unfold not.
    intros.
    induction l.
    - apply nil_cons in H.
      apply H.
    - apply IHl.
      destruct (eq_dec a0 a).
      + subst.
        inversion H.
        f_equal.
        apply H1.
      + inversion H.
        contradiction.
  Qed.

  Lemma filter_filter :
    forall (l: list A) (f : A -> bool),
      filter f (filter f l) = filter f l.
  Proof.
    intros.
    induction l.
    - auto.
    - remember (filter f (a :: l)).
      simpl in Heql0.
      remember (f a).
      destruct b.
      + rewrite Heql0.
        simpl.
        rewrite <- Heqb.
        rewrite IHl.
        reflexivity.
      + rewrite <- Heql0 in IHl.
        apply IHl.
  Qed.

  Lemma filter_two_func_true :
    forall (x y : A) (l : list A) (f : A -> bool),
      filter f l = [x; y] -> f x = true /\ f y = true.
  Proof.
    intros.
    split.
    - assert (In x (filter f l)). {
        rewrite H. apply in_eq.
      }
      rewrite filter_In in H0.
      destruct H0.
      apply H1.
    - assert (In y (filter f l)). {
        rewrite H; simpl; right; left; reflexivity.
      }
      rewrite filter_In in H0.
      destruct H0.
      apply H1.
  Qed.

  Theorem divide_list_take_while_val_drop_while_val :
    forall (v : A) (l : list A),
      take_while_val v l ++ drop_while_val v l = l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl.
      remember (eq_dec a v); destruct s.
      + reflexivity.
      + simpl.
        f_equal.
        apply IHl.
  Qed.

  Theorem in_divide_list_take_while_val_drop_while_val :
    forall (v : A) (l : list A),
      In v l -> drop_last (take_while_val v l) ++ [v] = take_while_val v l.
  Proof.
    intros.
    induction l.
    - inversion H.
    - simpl in H; destruct H.
      simpl.
      destruct (eq_dec a v).
      + subst.
        reflexivity.
      + contradiction.
      + destruct (eq_dec a v).
        * subst.
          simpl.
          destruct (eq_dec v v).
          reflexivity.
          contradiction.
        * assert (take_while_val v (a :: l) = a :: take_while_val v l). {
            simpl.
            destruct (eq_dec a v).
            contradiction.
            reflexivity.
          }
          assert (drop_last (a :: take_while_val v l) = a :: drop_last (take_while_val v l)). {
            destruct l.
            inversion H.
            simpl.
            remember (eq_dec a0 v); destruct s.
            reflexivity.
            reflexivity.
          }
          rewrite H0.
          rewrite H1.
          simpl.
          f_equal.
          apply IHl in H.
          apply H.
  Qed.

  Lemma in_dropped_list_in_source :
    forall (x y : A) (l : list A),
      In y (drop_while_val x l) -> In y l.
  Proof.
    intros.
    induction l.
    - inversion H.
    - simpl in H.
      destruct (eq_dec a x).
      + subst.
        simpl.
        right; apply H.
      + simpl.
        right; apply IHl in H; apply H.
  Qed.

  Lemma in_list_in_taken_list :
    forall (x : A) (l : list A),
      In x l -> In x (take_while_val x l).
  Proof.
    intros.
    induction l.
    - inversion H.
    - simpl.
      destruct (eq_dec a x).
      + subst; apply in_eq.
      + simpl.
        simpl in H; destruct H.
        * contradiction.
        * apply IHl in H.
          right.
          apply H.
  Qed.

  Lemma take_while_val_head :
    forall (x : A) (l : list A),
      take_while_val x (x :: l) = [x].
  Proof.
    intros.
    simpl.
    destruct (eq_dec x x).
    - reflexivity.
    - f_equal.
      contradiction.
  Qed.

  Lemma drop_while_val_head :
    forall (x : A) (l : list A),
      drop_while_val x (x :: l) = l.
  Proof.
    intros.
    simpl.
    destruct (eq_dec x x).
    - reflexivity.
    - contradiction.
  Qed.

  Lemma drop_while_val_cons :
    forall (x a : A) (l : list A),
      x <> a -> drop_while_val x (a :: l) = drop_while_val x l.
  Proof.
    intros.
    simpl.
    destruct (eq_dec a x).
    symmetry in e.
    - contradiction.
    - reflexivity.
  Qed.

  Lemma concat_cons_assoc :
    forall (x : A) (l1 l2 : list A),
      l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
  Proof.
    intros.
    destruct l1.
    - reflexivity.
    - simpl.
      f_equal.
      rewrite <- app_assoc.
      reflexivity.
  Qed.

  Lemma not_in_source_drop_while_val_eq_nil :
    forall (x : A) (l : list A),
      ~ In x l -> drop_while_val x l = [].
  Proof.
    intros.
    induction l.
    - simpl; reflexivity.
    - simpl.
      destruct (eq_dec a x).
      + subst.
        apply not_in_cons in H.
        destruct H; contradiction.
      + apply IHl.
        apply not_in_cons in H.
        destruct H.
        apply H0.
  Qed.

  Lemma drop_while_val_x_only_in_last_nil :
    forall (x : A) (l : list A),
      ~ In x l ->
      drop_while_val x (l ++ [x]) = [].
  Proof.
    intros.
    induction l.
    - simpl.
      destruct (eq_dec x x).
      + reflexivity.
      + reflexivity.
    - simpl.
      remember (eq_dec a x); destruct s.
      + subst.
        apply not_in_cons in H.
        destruct H.
        contradiction.
      + apply IHl.
        apply not_in_cons in H; destruct H.
        apply H0.
  Qed.

  Lemma split_list_by_not_in :
    forall (x : A) (l1 l2 l1' l2': list A) (f : A -> bool),
      ~In x l1 ->
      ~In x l1' ->
      l1' ++ [x] ++ l2' = l1 ++ [x] ++ l2 ->
      l1' = l1 /\ l2' = l2.
  Proof.
    induction l1.
    - intros.
      simpl in H1.
      destruct l1'.
      + simpl in H1; inversion H1.
        split; reflexivity; reflexivity.
      + simpl in H1.
        inversion H1; subst.
        apply Decidable.not_or in H0; destruct H0.
        contradiction.
    - intros.
      destruct l1'.
      + simpl in H1.
        inversion H1; subst.
        apply Decidable.not_or in H; destruct H.
        contradiction.
      + simpl in H1.
        inversion H1; subst.
        simpl in H; apply Decidable.not_or in H; destruct H.
        apply (IHl1 l2 l1 l2' f) in H2.
        destruct H2; subst.
        apply app_inv_tail in H4.
        split.
        * rewrite H4; reflexivity.
        * reflexivity.
        * apply H2.
        * apply (IHl1 l2 l1' l2' f) in H2.
          destruct H2; subst.
          reflexivity.
          simpl in H0.
          apply Decidable.not_or in H0; destruct H0.
          apply H3.
          apply H4.
  Qed.

  Lemma x_not_in_drop_last_take_while_val :
    forall (x : A) (l : list A),
      ~ In x (drop_last (take_while_val x l)).
  Proof.
    intros.
    induction l.
    - simpl.
      unfold not; intros.
      apply H.
    - simpl.
      destruct (eq_dec a x).
      + subst; simpl; unfold not; intros.
        apply H.
      + simpl.
        destruct (take_while_val x l).
        apply in_nil.
        unfold not; intro.
        simpl in H; destruct H.
        contradiction.
        destruct l0.
        * apply in_nil in H; apply H.
        * apply IHl; apply H.
  Qed.

  Theorem filter_split_take_while_val_drop_while_val :
    forall (x : A) (l l1 l2 : list A) (f : A -> bool),
      ~In x l1 ->
      filter f l = l1 ++ [x] ++ l2 ->
      l1 = filter f (drop_last (take_while_val x l)) /\
      l2 = filter f (drop_while_val x l).
  Proof.
    intros.
    assert (In x l). {
      assert (In x (filter f l)). {
        rewrite H0; apply in_elt.
      }
      apply (in_filter_in_source x l f).
      apply H1.
    }
    assert (f x = true). {
      assert (In x (filter f l)). {
        rewrite H0; apply in_elt.
      }
      apply filter_In in H2.
      destruct H2.
      apply H3.
    }
    rewrite <- (divide_list_take_while_val_drop_while_val x l) in H0.
    rewrite filter_app in H0.
    rewrite <- (in_divide_list_take_while_val_drop_while_val x l) in H0.
    rewrite filter_app in H0.
    remember (filter f [x]).
    simpl in Heql0.
    rewrite H2 in Heql0.
    rewrite Heql0 in H0.
    rewrite app_assoc_reverse in H0.
    assert (~ In x (filter f (drop_last (take_while_val x l)))). {
      apply not_in_source_not_in_filtered.
      apply x_not_in_drop_last_take_while_val.
    }
    apply (split_list_by_not_in x (filter f (drop_last (take_while_val x l))) (filter f (drop_while_val x l)) l1 l2 f).
    apply H3.
    apply H.
    rewrite H0; reflexivity.
    apply H1.
  Qed.


  Lemma filter_in_y_drop_while_val_x_l_filter :
    forall (x y : A) (l l1 l2 : list A) (f : A -> bool),
      ~ In x l1 ->
      In y l2 ->
      filter f l = l1 ++ [x] ++ l2 ->
      In y (filter f (drop_while_val x l)).
  Proof.
    intros.
    apply (filter_split_take_while_val_drop_while_val x l l1 l2 f) in H.
    destruct H.
    rewrite <- H2.
    apply H0.
    apply H1.
  Qed.

  Lemma filter_in_y_drop_while_val_x_l :
    forall (x y : A) (l l1 l2 : list A) (f : A -> bool),
      ~ In x l1 ->
      In y l2 ->
      filter f l = l1 ++ [x] ++ l2 ->
      In y (drop_while_val x l).
  Proof.
    intros.
    apply (in_filter_in_source y (drop_while_val x l) f).
    apply (filter_in_y_drop_while_val_x_l_filter x y l l1 l2 f).
    apply H.
    apply H0.
    apply H1.
  Qed.

  Lemma in_split_x_not_in_l1 :
    forall (x : A) (l : list A),
      In x l ->
      exists l1 l2 : list A, ~ In x l1 /\ l = l1 ++ x :: l2.
  Proof.
    intros.
    exists (drop_last (take_while_val x l)).
    exists (drop_while_val x l).
    split.
    - apply x_not_in_drop_last_take_while_val.
    - apply in_divide_list_take_while_val_drop_while_val in H.
      rewrite concat_cons_assoc.
      rewrite H.
      symmetry.
      apply divide_list_take_while_val_drop_while_val.
  Qed.

  Lemma filter_in_y_drop_while_val_x_l_sub :
    forall (x y : A) (l l1 l2 l3 : list A) (f : A -> bool),
      filter f l = l1 ++ [x] ++ l2 ++ [y] ++ l3 ->
      In y (drop_while_val x l).
  Proof.
    intros.
    assert (In x l1 \/ ~ In x l1). {
      apply in_dec.
    }
    destruct H0.
    - apply in_split_x_not_in_l1 in H0; destruct H0; destruct H0; destruct H0.
      rewrite H1 in H.
      simpl in H.
      rewrite app_assoc_reverse in H; simpl in H.
      remember (x1 ++ x :: l2 ++ y :: l3).
      apply (filter_in_y_drop_while_val_x_l x y l x0 l0 f).
      apply H0.
      rewrite Heql0.
      rewrite concat_cons_assoc; rewrite app_assoc.
      apply in_elt.
      apply H.
    - apply (filter_in_y_drop_while_val_x_l  x y l l1 (l2 ++ [y] ++ l3) f).
      apply H0.
      apply in_elt.
      apply H.
  Qed.

  Theorem filter_keep_order :
    forall (x y : A) (l l1 l2 l3 : list A) (f : A -> bool),
      filter f l = l1 ++ [x] ++ l2 ++ [y] ++ l3 ->
      exists (l1' l2' l3' : list A), l = l1' ++ [x] ++ l2' ++ [y] ++ l3'.
  Proof.
    intros.
    exists (drop_last (take_while_val x l)).
    exists (drop_last (take_while_val y (drop_while_val x l))).
    exists (drop_while_val y (drop_while_val x l)).
    assert (In x l /\ f x = true). {
      rewrite <- filter_In.
      rewrite H.
      apply in_elt.
    }
    destruct H0.
    assert (In y (drop_while_val x l)). {
      apply (filter_in_y_drop_while_val_x_l_sub x y l l1 l2 l3 f).
      apply H.
    }
    apply in_divide_list_take_while_val_drop_while_val in H2.
    rewrite app_assoc.
    remember (drop_while_val x l).
    remember (drop_last (take_while_val y l0) ++ [y] ++ drop_while_val y l0).
    rewrite app_assoc in Heql4.
    rewrite H2 in Heql4.
    rewrite divide_list_take_while_val_drop_while_val in Heql4.
    subst.
    apply in_divide_list_take_while_val_drop_while_val in H0.
    rewrite H0.
    rewrite divide_list_take_while_val_drop_while_val.
    reflexivity.
  Qed.

End FilterIn.
