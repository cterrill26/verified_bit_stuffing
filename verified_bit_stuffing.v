Require Import Bool List Program Arith Lia FunInd Recdef.
Import ListNotations.

(*returns true if a starts with k, else false*)
Fixpoint starts_with (a k : list bool) : bool :=
  match a,k with
    | ha::ta, hk::tk => eqb ha hk && starts_with ta tk
    | _, [] => true
    | _, _ => false
  end.


(*returns true if a contains k, else false*)
Fixpoint contains (a k : list bool) : bool :=
  match a,k with
    | ha::ta, hk::tk => starts_with a k || contains ta k
    | _, [] => true
    | _, _ => false
  end.


(*false is stuffed after two consecutive trues*)
Function stuff (a : list bool) {measure length a}: list bool :=
  match a with
    | [] => []
    | ha::ta => if starts_with a [true;true] then 
                  [true;true]++(false::(stuff (skipn 2 a))) 
                else 
                  ha::(stuff ta)
  end.
  Proof.
    - intros. rewrite skipn_length. simpl. lia.
    - intros. simpl. auto.
  Qed.


(*after two consecutive trues, the following bit is removed*)
Function unstuff (a : list bool) {measure length a}: list bool :=
  match a with
    | [] => []
    | ha::ta => if starts_with a [true;true] then  
                  [true;true]++(unstuff (skipn 3 a))
                else 
                  ha::(unstuff ta)
  end.
  Proof. 
    - intros. rewrite skipn_length. simpl. lia.
    - intros. simpl. auto.
  Qed.


(*flags are prepended and appended*)
Definition add_flags (a : list bool) :=
  [false;true;true;true;false] ++ a ++ [false;true;true;true;false].


(*returns list up until the flag*)
Fixpoint remove_end_flag (a : list bool) :=
  match a with
    | [] => []
    | ha::ta => if starts_with a [false;true;true;true;false] then
                  []
                else
                  ha::(remove_end_flag ta)
  end.


(*removes beginning and end flags*)
Definition remove_flags (a : list bool) :=
  if starts_with a [false;true;true;true;false] then
    remove_end_flag (skipn 5 a)
  else
    [].


Lemma starts_with_nil : forall (a : list bool), starts_with a [] = true.
  intros.
  case a.
    - simpl. reflexivity.
    - intros. simpl. reflexivity.
Qed.


Lemma stuff_unstuff_eq_size1 : forall (ha : bool), [ha] = unstuff (stuff [ha]).
  intros.
  rewrite stuff_equation. 
  simpl. 
  replace (eqb ha true && false) with false.
    * rewrite stuff_equation. rewrite unstuff_equation. simpl. replace (eqb ha true && false) with false. 
      -- rewrite unstuff_equation. reflexivity.
      -- symmetry. apply andb_false_intro2. reflexivity.
    * symmetry. apply andb_false_intro2. reflexivity.
Qed.


Lemma list_dual_induction (P : list bool -> Prop) :
  P [] ->
  (forall (b: bool), P [b]) ->
  (forall (ha hta : bool) (tta : list bool), P tta -> P (hta::tta) -> P (ha::hta::tta)) ->
  forall (a : list bool), P a.
Proof.
  intros H0 H1 Hstep tta.
  enough (P tta /\ forall (hta: bool), P (hta::tta)) by tauto.
  induction tta as [| htta ttta IH].
    - split. apply H0. apply H1.
    - destruct IH as [IH0 IH1]. split.
      + apply IH1.
      + intros hta. pose (IH1' := IH1 htta). pose (H2 := Hstep hta htta ttta IH0 IH1'). exact H2.
Qed.

Lemma stuff_no_contains_three_true : forall (a : list bool), ~Is_true (contains (stuff a) [true; true; true]).
  intros.
  induction a as [|ha | ha hta tta H0 H1] using list_dual_induction.
    - rewrite stuff_equation. simpl. auto.
    - rewrite stuff_equation. simpl. replace (eqb ha true && false) with false.
      + rewrite stuff_equation. simpl. replace (eqb ha true && false) with false. 
        * auto.
        * symmetry. apply andb_false_intro2. reflexivity.
      + symmetry. apply andb_false_intro2. reflexivity.
    - case ha.
      + destruct hta.  
        * rewrite stuff_equation. simpl. replace (starts_with tta []) with true.
          -- simpl. exact H0.
          -- symmetry. apply starts_with_nil.
        * rewrite stuff_equation. simpl. rewrite stuff_equation. simpl. exact H0.
      + rewrite stuff_equation. simpl. exact H1. 
Qed.


Lemma contains_remove_front : forall (a tk : list bool) (hk : bool), 
      Is_true (contains a (hk::tk)) -> Is_true (contains a tk).
  intros.
  induction a as [| ha ta IH].
    - case tk. all: simpl. all: auto.
    - destruct tk as [| htk ttk].
      + simpl. exact I.
      + simpl contains. enough (contains ta (htk :: ttk) = true).
        * rewrite H0. rewrite orb_true_r. simpl. exact I.
        * simpl in H. 
          pose (H' := orb_prop_elim (eqb ha hk && starts_with ta (htk :: ttk)) (contains ta (hk :: htk :: ttk)) H).
          destruct H' as [HL | HR].
            -- destruct (eqb ha hk). 
              ++ rewrite andb_true_l in HL. 
                 pose (HL' := Is_true_eq_true (starts_with ta (htk :: ttk)) HL). destruct ta as [|hta tta]. 
                ** simpl in HL'. contradiction.
                ** simpl. simpl in HL'. rewrite HL'. auto.
              ++ rewrite andb_false_l in HL. contradiction.
            -- pose (use_IH := IH HR). apply Is_true_eq_true in use_IH. rewrite use_IH. reflexivity.
Qed.


Lemma contains_reverse : forall (a k : list bool), Is_true (contains a k) <-> Is_true (contains (rev a) (rev k)).
  intros.
  split.
    - intros.
      induction a as [| ta ha IH] using rev_ind.
        + destruct k. 
          * simpl. exact I.
          * simpl in H. contradiction.
        + destruct k as [| tk hk] using rev_ind.
          * simpl. case (rev (ha ++ [ta])). all: simpl. all: auto.
          * 
Admitted.


Lemma contains_remove_back : forall (a hk : list bool) (tk : bool), 
      Is_true (contains a (hk++[tk])) -> Is_true (contains a hk).
  intros.
  apply contains_reverse in H. 
  rewrite rev_app_distr in H. 
  simpl in H.
  apply contains_remove_front in H.
  apply contains_reverse in H. 
  exact H.
Qed.


Lemma contains_flag_implies_contains_three_true : forall (a : list bool), 
      Is_true (contains a [false; true; true; true; false]) -> Is_true (contains a [true; true; true]).
  intros.
  pose (H1 := contains_remove_front a [true; true; true; false] false H).
  pose (H2 := contains_remove_back a [true; true; true] false H1).
  exact H2.
Qed.


Lemma stuff_no_contains_flag : forall (a : list bool), ~Is_true (contains (stuff a) [false; true; true; true; false]).
  intros.
  unfold not.
  intros H.
  pose (H1 := contains_flag_implies_contains_three_true (stuff a) H).
  pose (H2 := stuff_no_contains_three_true a).
  contradiction.
Qed.


Lemma stuff_no_flag_overlap_real_flag : forall (a : list bool) (b0 b1 b2 b3 : bool), 
        [b0; b1; b2; b3] = stuff a -> ~Is_true (contains ([b0; b1; b2; b3] ++ [false;true;true;true]) [false;true;true;true;false]).
  intros.
  destruct b0,b1,b2,b3.
    all: auto.
    pose (H1 := stuff_no_contains_three_true a). 
    rewrite <- H in H1.
    simpl in H1.
    contradiction.
Qed.


Lemma stuff_remove_end_flag : forall (a : list bool), 
        remove_end_flag (stuff a ++ [false; true; true; true; false]) = stuff a ++ remove_end_flag([false; true; true; true; false]).
  intros.
  induction a as [| ha ta IH].
    - simpl. rewrite stuff_equation. simpl. reflexivity.
    - 
Admitted.


Lemma add_remove_flags_eq : forall (a : list bool), stuff a = remove_flags (add_flags (stuff a)).
  intros.
  unfold add_flags.
  unfold remove_flags.
  simpl.
  replace (starts_with (stuff a ++ [false; true; true; true; false]) []) with true.
    - rewrite stuff_remove_end_flag. simpl. symmetry. apply app_nil_r.
    - symmetry. apply starts_with_nil.
Qed.


Lemma stuff_unstuff_eq : forall (a : list bool), a = unstuff (stuff a).
  intros.
  induction a as [|ha | ha hta tta H0 H1] using list_dual_induction.
    - rewrite stuff_equation. rewrite unstuff_equation. reflexivity.
    - apply stuff_unstuff_eq_size1.
    - case ha.
      + case hta.
        * rewrite stuff_equation. simpl. rewrite starts_with_nil. rewrite unstuff_equation. simpl. rewrite H0 at 1. reflexivity.
        * rewrite stuff_equation. simpl. rewrite stuff_equation. simpl. rewrite unstuff_equation. simpl. rewrite unstuff_equation. simpl. rewrite H0 at 1. reflexivity.
      + rewrite stuff_equation. simpl. rewrite unstuff_equation. simpl. rewrite H1 at 1. reflexivity.
Qed. 


Theorem valid_communication : forall (a : list bool), a = unstuff (remove_flags (add_flags (stuff a))).
  intros.
  replace (remove_flags (add_flags (stuff a))) with (stuff a).
    - apply stuff_unstuff_eq.
    - apply add_remove_flags_eq.
Qed.