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


Definition ends_with (a k : list bool) : bool :=
  starts_with (rev a) (rev k).


Lemma starts_with_ends_with : forall (a k : list bool), Is_true (starts_with a k) <-> Is_true (ends_with (rev a) (rev k)).
  intros.
  split.
    - intros. unfold ends_with. rewrite rev_involutive. rewrite rev_involutive. exact H.
    - intros. unfold ends_with in H. rewrite rev_involutive in H. rewrite rev_involutive in H. exact H. 
Qed.


Lemma starts_with_append : forall (ha k : list bool) (ta : bool), Is_true (starts_with ha k) -> Is_true (starts_with (ha ++ [ta]) k).
  intros ha.
  induction ha as [| hha tha IH]. 
    - intros. destruct k. all: auto. contradiction.
    - intros k ta H.
      destruct k as [| hk tk].
       + auto.
       + simpl. simpl in H. apply andb_prop_elim in H. destruct H as [HL HR]. 
         pose (apply_IH := IH tk ta HR).
         apply Is_true_eq_true in HL. rewrite HL.
         simpl. exact apply_IH. 
Qed.


Lemma not_is_true_iff_false: forall (b : bool), ~Is_true b <-> b = false.
    intros.
    split.
    - intros. destruct b.
      + simpl in H. contradiction.
      + reflexivity.
    - intros. rewrite H. auto.
Qed.

Lemma starts_with_length : forall (ha k : list bool) (ta : bool), ~Is_true (starts_with ha k) -> Is_true (starts_with (ha ++ [ta]) k) -> length (ha ++ [ta]) = length k.
  intros ha.
  induction ha as [| hha tha IH].
    - intros. simpl. destruct k as [| hk [| hta tk]].
      + simpl in H. lia.
      + simpl. reflexivity.
      + simpl in H0. apply Is_true_eq_true in H0. lia. 
    - destruct k as [| hk tk].
      + intros. simpl in H. lia.
      + intros. pose (IH' := IH tk ta).
        simpl in H. simpl in H0. apply andb_prop_elim in H0. destruct H0 as [H0L H0R]. 
        apply Is_true_eq_true in H0L.
        rewrite H0L in H. simpl in H. 
        pose (IH'' := IH' H). simpl. auto.
Qed.


Lemma starts_with_eq : forall (a k : list bool), Is_true (starts_with a k) -> length a = length k -> a = k.
  intros a.
  induction a as [| ha ta IH].
    - intros. destruct k.
      + auto.
      + simpl in H. tauto.
    - intros. destruct k as [| hk tk].
      + simpl in H0. lia.
      + pose (IH' := IH tk).
        simpl in H. apply andb_prop_elim in H. destruct H as [HL HR]. simpl in H0.
        assert (length ta = length tk).
          * auto.
          * pose (IH'' := IH' HR H).
            apply Is_true_eq_true in HL.
            rewrite eqb_true_iff in HL.
            rewrite IH''. rewrite HL. auto.
Qed.


Lemma starts_with_itself : forall (a : list bool), starts_with a a = true.
  intros a.
  induction a as [| ha ta IH].
    - simpl. auto.
    - simpl. rewrite eqb_reflx. simpl. auto.
Qed.

Lemma starts_with_at_end : forall (ha k : list bool) (ta : bool), Is_true (starts_with (ha ++ [ta]) k) -> starts_with ha k = true \/ ends_with (ha ++ [ta]) k = true.
  intros ha.
  induction ha as [|hha tha IH]. 
    - intros. destruct k as [| hk [| hta ttk]].
      + simpl. auto.
      + unfold ends_with. simpl. simpl in H. apply Is_true_eq_true in H. rewrite H. auto.
      + simpl in H. apply Is_true_eq_true in H. rewrite andb_false_r in H. auto.
    - intros. destruct k as [| hk tk]. 
      + simpl. auto.
      + simpl in H. 
        apply Is_true_eq_true in H.
        apply andb_true_iff in H.
        destruct H as [HL HR].
        simpl. apply Is_true_eq_left in HR.
        pose proof (IH' := IH tk ta HR). 
        pose proof (sw_len := starts_with_length tha tk ta).
        destruct (starts_with tha tk).
          * rewrite HL. simpl. auto.
          * assert (~ Is_true false).
            -- auto.
            -- pose proof (sw_len' := sw_len H HR).
               pose proof (eq := starts_with_eq (tha ++ [ta]) tk HR sw_len').
               unfold ends_with.
               simpl. rewrite eq. apply eqb_prop in HL. rewrite HL. 
               enough (starts_with (rev tk ++ [hk]) (rev tk ++ [hk]) = true).
                  ** rewrite H0. auto.
                  ** apply starts_with_itself.
Qed.


Lemma contains_at_end : forall (ha k : list bool) (ta : bool), Is_true (contains (ha ++ [ta]) k) -> contains ha k = true \/ ends_with (ha ++ [ta]) k = true.
  intros. 
  induction ha as [|hha tha IH].
  - enough (ends_with ([] ++ [ta]) k = true).
    + rewrite H0. auto.
    + destruct k as [| hk [| htk ttk]].
      * unfold ends_with. simpl. reflexivity.
      * unfold ends_with. simpl. simpl in H. 
         apply Is_true_eq_true in H. rewrite orb_false_r in H. exact H.
      * simpl in H. rewrite orb_false_r in H. simpl in H. rewrite andb_false_r in H. auto.
  - destruct k as [| hk tk].
    + simpl. auto.
    + simpl in H.
      apply orb_prop_elim in H.
      destruct H as [HL | HR]. 
        * pose (sw_at_end := starts_with_at_end (hha::tha) (hk::tk) (ta)).
           simpl in sw_at_end.
           pose (sw_at_end' := sw_at_end HL).
           destruct sw_at_end' as [SWL | SWR].
            -- simpl. rewrite SWL. simpl. auto.
            -- simpl. rewrite SWR. auto.
        * pose (H' := IH HR).
           unfold ends_with. simpl. unfold ends_with in H'. simpl in H'. 
           destruct H' as [Hl' | HR'].
            -- rewrite Hl'. lia.
            -- apply Is_true_eq_left in HR'. 
                pose (sw_append := starts_with_append (rev (tha ++ [ta])) (rev tk ++ [hk]) hha HR').
                apply Is_true_eq_true in sw_append.
                rewrite sw_append. auto.
Qed.


Lemma contains_reverse_forward : forall (a k : list bool), Is_true (contains a k) -> Is_true (contains (rev a) (rev k)).
  intros a k H.
  induction a as [| ta ha IH] using rev_ind.
    - destruct k.
      + simpl. auto.
      + simpl in H. contradiction.
    - pose (H1 := contains_at_end ha k ta H).
      destruct k as [| hk tk].
      + rewrite rev_unit. simpl. auto.
      + rewrite rev_unit. destruct H1 as [H1L | H1R].
        *  apply Is_true_eq_left in H1L.
           pose (H2 := IH H1L). apply Is_true_eq_true in H2. simpl. simpl in H2.
           rewrite H2. rewrite orb_true_r. case (rev tk ++ [hk]). all: simpl. all: auto.
        *  unfold ends_with in H1R. 
           rewrite rev_unit in H1R. 
           simpl. simpl in H1R.
           rewrite H1R. simpl. case (rev tk ++ [hk]). all: simpl. all: auto.
Qed.

Lemma contains_reverse : forall (a k : list bool), Is_true (contains a k) <-> Is_true (contains (rev a) (rev k)).
  split.
    - apply contains_reverse_forward. 
    - replace a with (rev (rev a)) at 2.
      + replace k with (rev (rev k)) at 2.
        * apply contains_reverse_forward. 
        * rewrite rev_involutive. reflexivity.
      + rewrite rev_involutive. reflexivity.
Qed.


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


Lemma stuff_and_partial_flag_no_contains_flag : forall (a b: list bool) , 
        b = stuff a -> ~Is_true (contains (b ++ [false;true;true;true]) [false;true;true;true;false]).
  intros.
  pose (apply_contains_reverse := contains_reverse (b ++ [false; true; true; true]) [false; true; true; true; false]).
  destruct apply_contains_reverse as [revl revr].
  repeat rewrite <- app_assoc in revl. simpl in revl.
  unfold not.
  intros false_H.
  pose (rev_false_H := revl false_H).
  rewrite rev_app_distr in rev_false_H. simpl in rev_false_H.
  pose (apply_contains_reverse' := contains_reverse (rev b) [false; true; true; true; false]).
  simpl in apply_contains_reverse'.
  rewrite rev_involutive in apply_contains_reverse'.
  rewrite H in apply_contains_reverse' at 2.
  destruct (contains (rev b) [false; true; true; true; false]).
    - destruct apply_contains_reverse'. 
       simpl in H0.
       pose (H2 := stuff_no_contains_flag a).
       auto.
    - rewrite orb_false_r in rev_false_H.
       assert (Is_true (contains (rev b) [true; true; true; false])).
        + destruct (rev b). 
          * contradiction.
          * simpl.
            simpl in rev_false_H.
            apply Is_true_eq_true in rev_false_H.
            rewrite rev_false_H.
            simpl. exact I.
        + apply contains_reverse in H0.
          rewrite rev_involutive in H0.
          simpl in H0.
          rewrite H in H0.
          apply contains_remove_front in H0.
          pose (H1 := stuff_no_contains_three_true a).
          contradiction.
Qed.


Lemma no_flag_remove_end_flag : forall (a : list bool) , 
        ~Is_true(contains (a ++ [false; true; true; true]) [false; true; true; true; false]) -> 
        remove_end_flag (a ++ [false; true; true; true; false]) = a ++ remove_end_flag [false;true;true;true;false].
  intros.
  induction a as [| ha ta IH].
    - simpl. reflexivity.
    - simpl. simpl in H. simpl in IH.
      apply not_is_true_iff_false in H.
      apply orb_false_iff in H.
      destruct H as [HL HR].
      assert (eqb ha false && starts_with (ta ++ [false; true; true; true; false]) [true; true; true; false] = false).
        + apply andb_false_iff in HL.
          destruct HL as [HLL | HLR].
            * rewrite HLL. simpl. auto.
            * destruct ta as [|[] [|[] [|[] [|[] [|]]]]].
              all: simpl. all: simpl in HLR. all: lia.
        + rewrite H. apply not_is_true_iff_false in HR.
          pose (apply_IH := IH HR).
          rewrite apply_IH.
          reflexivity.
Qed.


Lemma add_remove_flags_eq : forall (a : list bool), stuff a = remove_flags (add_flags (stuff a)).
  intros.
  unfold add_flags.
  unfold remove_flags.
  simpl.
  replace (starts_with (stuff a ++ [false; true; true; true; false]) []) with true.
    - pose (b := stuff a). assert (b = stuff a).
      + auto.
      + pose (no_flag := stuff_and_partial_flag_no_contains_flag a b H).
        pose (H0 := no_flag_remove_end_flag b no_flag).
        rewrite H in H0.
        simpl in H0. rewrite app_nil_r in H0. symmetry in H0. exact H0.
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

Recursive Extraction stuff unstuff add_flags remove_flags.