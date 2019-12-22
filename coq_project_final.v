Require Import List.
Require Import Nat.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


(*define insert sort *) 

Fixpoint insert (n : nat) (sorted : list nat) : list nat :=
  match sorted with
  | nil => n :: nil
  | m :: t => if n <? m then n :: sorted
                       else m :: (insert n t)
  end.

Example insert1 : insert 5 [4;6] = [4;5;6].
 Proof. reflexivity. Qed.

Example insert2 : insert 7 [2;3;5;7;7;9;8] = [2;3;5;7;7;7;9;8].
 Proof. reflexivity. Qed.

Fixpoint insert_sort (arr : list nat) : list nat :=
  match arr with
  | nil => nil
  | m :: t =>insert m (insert_sort t)
  end. 

Check insert_sort [7;5;9;8;3;7;7;2].

Example test_insert_sort1 : insert_sort [7;5;9;8;3;7;7;2] = [2;3;5;7;7;7;8;9].
 Proof. reflexivity. Qed.

Example test_insert_sort2 : insert_sort [] = [].
 Proof. reflexivity. Qed.

Example test_insert_sort3 : insert_sort [5;4;3;2;1;0] = [0;1;2;3;4;5].
 Proof. reflexivity. Qed.

(*define count func*)

Fixpoint count (v : nat) (l : list nat) : nat :=
  match l with
  | nil => O
  | h :: t => if v =? h then S(count v t)
                        else count v t
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.

(*define is_sorted*)


Fixpoint is_sorted (arr : list nat) : bool :=
  match arr with
  | nil => true
  | h :: t => match t with
               | nil => true
               | k :: g => if h <=? k then is_sorted t 
                                      else false
               end
  end.

Example test_is_sorted1: is_sorted [7;5;9;8;3;7;7;2] = false.
  Proof. reflexivity. Qed.

Example test_is_sorted2: is_sorted [2;3;5;7;7;7;8;9] = true.
  Proof. reflexivity. Qed.

Example test_is_sorted3: is_sorted [] = true.
  Proof. reflexivity. Qed.

(*Proof*)

(* nat lemmas *)

Lemma plus_1_neq_0_left : forall n : nat,
  S n =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Lemma plus_1_neq_0_right : forall n : nat,
  0 =? S n = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Lemma nat_is_positive_right : forall n : nat,
  0 <? S n = true.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Lemma nat_is_positive_right2 : forall n : nat,
  0 <=? S n = true.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Lemma nat_is_not_negative_left : forall n : nat,
  S n <? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

(* comparison lemmas *)

Lemma mon_uneq :
   forall n m : nat, S n <? S m = true -> n <? m = true.
Proof.
intros n m. destruct (n <? m) eqn:E; try auto.
unfold ltb in *. remember (S n) as t. simpl.
rewrite E. auto.
Qed.

Lemma eq_not_less :
  forall n t : nat, n =? t = true -> n <? t = false.
Proof.
intros n. induction n.
  - intros t L. destruct t.
     + reflexivity.
     + rewrite plus_1_neq_0_right in L. discriminate L.
  - intros t L. destruct t.
     + simpl. rewrite plus_1_neq_0_left in L. discriminate L.
     + simpl in L. apply IHn. rewrite -> L. reflexivity.
Qed.

Lemma eq_ref :
  forall n : nat, n =? n = true.
Proof.
  induction n. 
  + reflexivity. 
  + simpl. rewrite -> IHn. reflexivity. 
Qed.

Lemma eq_or_less_ref :
  forall n : nat, n <=? n = true.
Proof.
  induction n. 
  + reflexivity. 
  + simpl. rewrite -> IHn. reflexivity. 
Qed.

Lemma less_is_less_or_eq :
  forall n m : nat, n <? m = true -> (n <=? m) = true.
Proof.
  intros n. induction n.
  - intros m L. destruct m.
     + reflexivity.
     + rewrite nat_is_positive_right2. reflexivity.
  - intros m L. destruct m.
     + simpl. rewrite nat_is_not_negative_left in L. discriminate L.
     + simpl in L. apply IHn. rewrite -> mon_uneq. reflexivity.
       rewrite -> L. reflexivity.
Qed.

Lemma eq_is_less_or_eq :
  forall n m : nat, n =? m = true -> (n <=? m) = true.
Proof.
  intros n. induction n.
  - intros m L. destruct m.
     + reflexivity.
     + rewrite nat_is_positive_right2. reflexivity.
  - intros m L. destruct m.
     + simpl. rewrite plus_1_neq_0_left in L. discriminate L.
     + simpl in L. apply IHn. apply L.
Qed.

Lemma h0:
  forall n m, n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m L. destruct m.
    + reflexivity.
    + rewrite plus_1_neq_0_right in L. discriminate.
  - intros m L. destruct m.
    + rewrite plus_1_neq_0_left in L. discriminate.
    + simpl in L. 
      assert (H: n = m -> S n = S m). { intro. rewrite <-H. reflexivity. }
      apply H. apply IHn. apply L.
Qed.

Lemma h0b:
  forall n m, n = m -> n =? m = true.
Proof.
  intros n m L.
  rewrite L.
  apply eq_ref.
Qed.

Lemma trans_eq:
  forall n m k, n =? m = true /\ k =? m = true -> n =? k = true.
Proof.
  intros n m k [L1 L2].
  apply h0 in L1. apply h0 in L2.
  rewrite <- L1 in L2. symmetry in L2. apply h0b in L2. apply L2.
Qed.

Lemma leb_n0 : forall n, n <=? 0 = true -> n =? 0 = true.
Proof. destruct n; intro H.
apply eq_ref.
simpl in H. discriminate H.
Qed.

Lemma trans_leb:
  forall n m k, n <=? m = true /\ m <=? k = true -> n <=? k = true.
Proof.
intros n m k. generalize dependent m. generalize dependent n.
induction k; intros n m H; destruct H as [H1 H2].
- apply leb_n0 in H2. apply h0 in H2. rewrite H2 in H1. assumption.
- destruct n.
  + reflexivity.
  + simpl. destruct m.
    * simpl in H1. discriminate.
    * apply IHk with (m := m). simpl in H1, H2. auto.
Qed.

Search _ le "trans".


Lemma l4 :
 forall n k, (n <? k = false /\ n =? k = false) -> k <? n = true.
Proof.
unfold ltb. induction n.
- destruct k; simpl; intro H; destruct H; discriminate.
- destruct k; intro H.
  + reflexivity.
  + apply IHn. destruct H as [H1 H2]. remember (S n) as t in H1.
    simpl in H1, H2. rewrite Heqt in H1. rewrite H1, H2. split; reflexivity.
Qed.

Lemma leb_antisym : forall n m, (n <=? m) = true /\ (m <=? n) = true
 -> (n =? m) = true.
Proof.
induction n, m; try reflexivity; simpl; intro H;
destruct H as [H1 H2]; try discriminate.
apply IHn. split; assumption.
Qed.

Lemma eqn_sym : forall n m, (n =? m) = (m =? n).
Proof. induction n, m; simpl; try reflexivity; apply IHn. Qed.

Lemma eq1:
  forall n m, n <=? m = true /\ n <? m = false -> n =? m = true.

Proof.
intros n m H. destruct H as [H1 H2].
destruct (n =? m) eqn: E1; try reflexivity.
rewrite <- H2. apply l4. split.
- destruct (m <? n) eqn: E2; try reflexivity.
  apply less_is_less_or_eq in E2.
  rewrite <- E1. symmetry. apply leb_antisym.
  split; assumption.
- rewrite <- E1. apply eqn_sym.
Qed.


(* sort_array lemmas *)

Lemma push_in_nonsorted:
  forall l m, is_sorted (l) = false -> is_sorted(m :: l) = false.
Proof.
  intros l n L.
  simpl.
  destruct l as [| t h] eqn:E1.
  - simpl in L. discriminate.
  -  destruct (n <=? t) eqn:E2.
    + apply L.
    + reflexivity.   
Qed.


Lemma sublist_of_sorted_is_sorted :
  forall l n, is_sorted (n :: l) = true -> is_sorted l = true.
Proof.
  intros l n L.
  destruct (is_sorted l) as [| t h] eqn:E1.
  - reflexivity.
  - apply push_in_nonsorted with(m:=n) in E1. 
    rewrite E1 in L. discriminate.   
Qed.

Lemma l0:
 forall n m, n =? m = true -> [n] = [m].
Proof.
  intros n m L.
  rewrite h0 with (n:=n) (m:=m). reflexivity.
  apply L.
Qed.

Lemma h1:
 forall n m, [n] = [m] -> n <=? m = true .
Proof.
  intros n m L.
  rewrite h0 with (n:=n) (m:=m). apply eq_or_less_ref.
  injection L. intros K. apply h0b. apply K.
Qed.

Lemma h3:
 forall t n h k g, t :: n :: h = k :: g -> t =? k = true.
Proof.
 intros t n h k g L.
 injection L. intros H1 H2. apply h0b. apply H2.
Qed.

Lemma h4:
  forall t n k g, t :: n = k :: g -> t =? k = true.
Proof.
 intros t n k g L.
 injection L. intros H1 H2. apply h0b. apply H2.
Qed.

Lemma l2 :
  forall t n h,  n =? t = true -> insert n h = insert t h.
Proof.
  intros t n h L.
  simpl.
  destruct h as [| a l] eqn:E1.
  - simpl. apply l0. apply L.  
  - simpl. rewrite h0 with (n:=n) (m:=t). 
    destruct (t <=? a) eqn:E2.
    + reflexivity.
    + reflexivity.
    + apply L.
Qed.

(* sorting proof *)

Theorem invariance_of_occurrences : 
  forall l n, count n (insert n l) = S (count n l).
Proof.
  intros l.
  induction l as [| t h IHl].
  - intros n. simpl.
    rewrite eq_ref. reflexivity. 
  - intros n. simpl. destruct (n =? t) eqn:E1.
      + rewrite eq_not_less. simpl. rewrite E1. rewrite IHl. reflexivity. 
        rewrite E1. reflexivity.
      + destruct (n <? t) eqn:E2.
          * simpl. rewrite eq_ref. rewrite E1. reflexivity. 
          * simpl. rewrite E1. rewrite IHl. reflexivity. 
Qed.

Theorem independence_of_occurrences :
  forall l n m, n =? m = false -> count n (insert m l) = count n l.
Proof.
  intros l.
  induction l as [| t h IHl].
  - intros n m L. simpl.
    rewrite L. reflexivity. 
  - intros n m L. simpl. destruct (m =? t) eqn:E1.
      { rewrite eq_not_less. simpl. destruct (n =? t) eqn:E2.
          - rewrite IHl. reflexivity. 
            rewrite L. reflexivity.
          - rewrite IHl. reflexivity.
            rewrite L. reflexivity.
          - rewrite E1. reflexivity. }
      { destruct (m <? t) eqn:E3.
          - destruct (n =? t) eqn:E4. 
              + simpl. rewrite L. rewrite E4. reflexivity.
              + simpl. rewrite E4. rewrite L. reflexivity.
          - destruct (n =? t) eqn:E4. 
              + simpl. rewrite E4. rewrite IHl. reflexivity.
                rewrite L. reflexivity.
              + simpl. rewrite E4. rewrite IHl. reflexivity.
                rewrite L. reflexivity. } 
Qed.

Lemma l1 :
 forall t h k g, is_sorted (t :: h) = true /\ 
   insert t h = k :: g -> t <=? k = true.
Proof.
  intros t h k g [L1 L2].
  simpl in L1. destruct h.
  - simpl in L2. 
    destruct g.
    + apply h1. apply L2.
    + discriminate.
  - destruct (t <=? n) eqn:E1.
    + simpl in L2.
      destruct (t <? n) eqn:E2.
      * simpl in L2. apply h3 in L2. 
        apply eq_is_less_or_eq in L2.
        apply L2.
      * apply h4 in L2. apply eq_is_less_or_eq. apply trans_eq with (m:=n). 
        split. apply eq1. split.
        apply E1. apply E2. 
        apply h0 with (n:=n) (m:=k) in L2. rewrite L2. apply eq_ref.
    + discriminate.   
Qed.

Lemma l3 :
 forall t h n k g, is_sorted (t :: h) = true /\ 
   (insert n h = k :: g /\ t <? n = true) -> t <=? k = true.
Proof.
  intros t h n k g [L1 [L2 L3]].
  simpl in L1. destruct h as [|x p].
  - simpl in L2. 
    destruct g.
    + apply h1 in L2. apply less_is_less_or_eq in L3.
      apply trans_leb with (m:=n). split.
      apply L3. apply L2.
    + discriminate.
  - destruct (t <=? x) eqn:E1.
    + simpl in L2.
      destruct (n <? x) eqn:E2.
      * apply h3 in L2. 
        apply less_is_less_or_eq in L3.
        apply h0 in L2. rewrite <-L2. apply L3.
      * apply h4 in L2. apply h0 in L2.
        rewrite <-L2. apply E1.
    + discriminate.  
Qed.

Theorem sorting_preservation : 
  forall l n, is_sorted l = true -> is_sorted (insert n l) = true.
Proof.
  intros l.
  induction l as [| t h IHl].
  - intros n L. simpl. reflexivity.
  - intros n L. simpl. 
    destruct (n =? t) eqn:E1.
      + rewrite eq_not_less. simpl.
        destruct (insert n h) as [| k g] eqn:E2.
          * reflexivity.
          * destruct (t <=? k) eqn:E3.
            { rewrite <- E2. rewrite IHl. 
              reflexivity. apply sublist_of_sorted_is_sorted with (n:=t).
              rewrite L. reflexivity. }
            { rewrite l1 with (t:=t) (h:=h) (k:=k) (g:=g) in E3. discriminate.
              split. apply L. 
              rewrite <- l2 with (n:=n). apply E2. 
              apply E1. } 
          * rewrite E1. reflexivity.
      + destruct (n <? t) eqn:E4.
          * simpl. rewrite less_is_less_or_eq with (n:=n) (m:=t).
            destruct (h) as [| k g] eqn:E5.
            { reflexivity. }
            { destruct (t <=? k) eqn:E6.
              - apply sublist_of_sorted_is_sorted with (n:=t).
                rewrite L. reflexivity. 
              - simpl in L. rewrite E6 in L. discriminate L. }
            {rewrite E4. reflexivity. }
          * simpl. destruct (insert n h) as [| k g] eqn:E7.
            { reflexivity. }
            { destruct (t <=? k) eqn:E8.
              - rewrite <- E7. apply IHl. 
                apply sublist_of_sorted_is_sorted with (n:=t). apply L.
              - rewrite l3 with (t:=t) (h:=h) (n:=n) (k:=k) (g:=g) in E8. discriminate E8.
                split. apply L. 
                split. apply E7.
                apply l4. split. apply E4. apply E1. } 
Qed.

Lemma sort_is_sort : forall l, is_sorted (insert_sort l) = true.
Proof.
induction l.
- simpl. reflexivity.
- simpl. apply sorting_preservation. rewrite IHl. reflexivity.
Qed.

(* Check if there are any assumptions still unproved (admitted or otherwise).*)
Print Assumptions sort_is_sort.


