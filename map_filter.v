Require Import List.

Section MapFilter.

  Lemma not_in_map_not_in_map_filter :
    forall (A B : Type) (l : list A) (f1 : A -> bool) (f2 : A -> B) (e : B),
      ~ In e (map f2 l) -> ~ In e (map f2 (filter f1 l)).
  Proof.
    intros.
    induction l.
    - simpl; auto.
    - simpl in H.
      apply Decidable.not_or in H.
      destruct H.
      simpl.
      remember (f1 a) as b; destruct b.
      + simpl.
        unfold not; intro.
        destruct H1.
        * apply H; apply H1.
        * apply IHl.
          apply H0.
          apply H1.
      + apply IHl.
        apply H0.
  Qed.

  Lemma nodup_map_filter
    : forall (A B : Type) (l : list A) (f1 : A -> bool) (f2 : A -> B),
      NoDup (map f2 l) -> NoDup (map f2 (filter f1 l)).
  Proof.
    intros.
    induction l.
    - simpl; auto.
    - simpl.
      simpl in H.
      rewrite NoDup_cons_iff in H.
      destruct H.
      remember (f1 a) as b; destruct b.
      + simpl.
        rewrite NoDup_cons_iff.
        split.
        apply not_in_map_not_in_map_filter.
        apply H.
        apply IHl.
        apply H0.
      + apply IHl.
        simpl in H.
        apply H0.
  Qed.

End MapFilter.
