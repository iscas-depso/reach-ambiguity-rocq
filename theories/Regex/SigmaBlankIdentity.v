From Stdlib Require Import List.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Regex Require Import KleeneSemantics.

(** The paper uses the Kleene-algebra identity
    [(Sigma* blank)* Sigma* = (Sigma + blank)*].

    This file proves the identity directly over the existing inductive
    regex semantics [matches].  [Sigma] is represented by a finite list of
    symbols.  No [NoDup] assumption is needed: duplicates do not change the
    language denoted by the finite alternation below. *)

Section SigmaBlankIdentity.
  Context {A : Type}.

  Fixpoint sigma_regex (sigma : list A) : regex A :=
    match sigma with
    | [] => Empty
    | a :: sigma' => Alt (Atom a) (sigma_regex sigma')
    end.

  Definition sigma_star_regex (sigma : list A) : regex A :=
    Star (sigma_regex sigma).

  Definition sigma_plus_blank_regex
      (sigma : list A) (blank : A) : regex A :=
    Alt (sigma_regex sigma) (Atom blank).

  Definition sigma_star_blank_regex
      (sigma : list A) (blank : A) : regex A :=
    Cat (sigma_star_regex sigma) (Atom blank).

  Definition sigma_star_blank_star_sigma_star_regex
      (sigma : list A) (blank : A) : regex A :=
    Cat (Star (sigma_star_blank_regex sigma blank))
        (sigma_star_regex sigma).

  Definition sigma_plus_blank_star_regex
      (sigma : list A) (blank : A) : regex A :=
    Star (sigma_plus_blank_regex sigma blank).

  Definition sigma_or_blank
      (sigma : list A) (blank a : A) : Prop :=
    In a sigma \/ a = blank.

  Lemma forall_app_intro :
    forall (P : A -> Prop) xs ys,
      Forall P xs ->
      Forall P ys ->
      Forall P (xs ++ ys).
  Proof.
    intros P xs ys Hxs Hys.
    induction Hxs as [| x xs Hx _ IH]; simpl.
    - exact Hys.
    - constructor; assumption.
  Qed.

  Lemma forall_app_inv :
    forall (P : A -> Prop) xs ys,
      Forall P (xs ++ ys) ->
      Forall P xs /\ Forall P ys.
  Proof.
    intros P xs ys H.
    induction xs as [| x xs IH]; simpl in H.
    - split; [constructor | exact H].
    - inversion H as [| y ys' Hy Hys Heq]; subst.
      destruct (IH Hys) as [Hxs Htail].
      split.
      + constructor; assumption.
      + exact Htail.
  Qed.

  Lemma forall_impl :
    forall (P Q : A -> Prop) xs,
      (forall x, P x -> Q x) ->
      Forall P xs ->
      Forall Q xs.
  Proof.
    intros P Q xs Himpl Hxs.
    induction Hxs as [| x xs Hx _ IH]; constructor; auto.
  Qed.

  Lemma sigma_regex_sound :
    forall sigma w,
      matches (sigma_regex sigma) w ->
      exists a, w = [a] /\ In a sigma.
  Proof.
    induction sigma as [| a sigma IH]; intros w Hmatch; simpl in Hmatch.
    - inversion Hmatch.
    - inversion Hmatch; subst.
      + match goal with
        | Hatom : matches (Atom a) _ |- _ =>
            inversion Hatom; subst;
            exists a; split; [reflexivity | simpl; auto]
        end.
      + match goal with
        | Htail : matches (sigma_regex sigma) _ |- _ =>
            apply IH in Htail as [b [-> Hin]];
            exists b; split; [reflexivity | simpl; auto]
        end.
  Qed.

  Lemma sigma_regex_complete :
    forall sigma a,
      In a sigma ->
      matches (sigma_regex sigma) [a].
  Proof.
    induction sigma as [| b sigma IH]; intros a Hin; simpl in Hin.
    - contradiction.
    - destruct Hin as [-> | Hin].
      + simpl. apply M_AltL. apply M_Atom.
      + simpl. apply M_AltR. now apply IH.
  Qed.

  Theorem sigma_regex_correct :
    forall sigma w,
      matches (sigma_regex sigma) w <->
      exists a, w = [a] /\ In a sigma.
  Proof.
    intros sigma w. split.
    - apply sigma_regex_sound.
    - intros [a [-> Hin]]. now apply sigma_regex_complete.
  Qed.

  Lemma sigma_star_sound :
    forall sigma w,
      matches (sigma_star_regex sigma) w ->
      Forall (fun a => In a sigma) w.
  Proof.
    intros sigma w Hmatch.
    unfold sigma_star_regex in Hmatch.
    remember (Star (sigma_regex sigma)) as rstar eqn:Hrstar.
    induction Hmatch; inversion Hrstar; subst.
    - constructor.
    - apply sigma_regex_sound in Hmatch1 as [a [-> Hin]].
      constructor; [exact Hin |].
      apply IHHmatch2. reflexivity.
  Qed.

  Lemma sigma_star_complete :
    forall sigma w,
      Forall (fun a => In a sigma) w ->
      matches (sigma_star_regex sigma) w.
  Proof.
    intros sigma w Hover.
    unfold sigma_star_regex.
    induction Hover as [| a w Hin _ IH].
    - apply M_Star0.
    - change (a :: w) with ([a] ++ w).
      eapply M_StarApp.
      + now apply sigma_regex_complete.
      + discriminate.
      + exact IH.
  Qed.

  Theorem sigma_star_correct :
    forall sigma w,
      matches (sigma_star_regex sigma) w <->
      Forall (fun a => In a sigma) w.
  Proof.
    intros sigma w. split.
    - apply sigma_star_sound.
    - apply sigma_star_complete.
  Qed.

  Lemma sigma_plus_blank_sound :
    forall sigma blank w,
      matches (sigma_plus_blank_regex sigma blank) w ->
      exists a, w = [a] /\ sigma_or_blank sigma blank a.
  Proof.
    intros sigma blank w Hmatch.
    unfold sigma_plus_blank_regex in Hmatch.
    inversion Hmatch; subst.
    - apply sigma_regex_sound in H2 as [a [-> Hin]].
      exists a. split; [reflexivity | now left].
    - inversion H2; subst.
      exists blank. split; [reflexivity | now right].
  Qed.

  Lemma sigma_plus_blank_complete :
    forall sigma blank a,
      sigma_or_blank sigma blank a ->
      matches (sigma_plus_blank_regex sigma blank) [a].
  Proof.
    intros sigma blank a [Hin | ->].
    - unfold sigma_plus_blank_regex.
      apply M_AltL. now apply sigma_regex_complete.
    - unfold sigma_plus_blank_regex.
      apply M_AltR. apply M_Atom.
  Qed.

  Lemma sigma_plus_blank_star_sound :
    forall sigma blank w,
      matches (sigma_plus_blank_star_regex sigma blank) w ->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w Hmatch.
    unfold sigma_plus_blank_star_regex in Hmatch.
    remember (Star (sigma_plus_blank_regex sigma blank)) as rstar
      eqn:Hrstar.
    induction Hmatch; inversion Hrstar; subst.
    - constructor.
    - apply sigma_plus_blank_sound in Hmatch1 as [a [-> Hin]].
      constructor; [exact Hin |].
      apply IHHmatch2. reflexivity.
  Qed.

  Lemma sigma_plus_blank_star_complete :
    forall sigma blank w,
      Forall (sigma_or_blank sigma blank) w ->
      matches (sigma_plus_blank_star_regex sigma blank) w.
  Proof.
    intros sigma blank w Hover.
    unfold sigma_plus_blank_star_regex.
    induction Hover as [| a w Hin _ IH].
    - apply M_Star0.
    - change (a :: w) with ([a] ++ w).
      eapply M_StarApp.
      + now apply sigma_plus_blank_complete.
      + discriminate.
      + exact IH.
  Qed.

  Theorem sigma_plus_blank_star_correct :
    forall sigma blank w,
      matches (sigma_plus_blank_star_regex sigma blank) w <->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w. split.
    - apply sigma_plus_blank_star_sound.
    - apply sigma_plus_blank_star_complete.
  Qed.

  Lemma sigma_star_blank_sound :
    forall sigma blank w,
      matches (sigma_star_blank_regex sigma blank) w ->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w Hmatch.
    unfold sigma_star_blank_regex in Hmatch.
    inversion Hmatch; subst.
    match goal with
    | Hatom : matches (Atom blank) _ |- _ =>
        inversion Hatom; subst; clear Hatom
    end.
    apply forall_app_intro.
    - eapply (forall_impl
                (fun a => In a sigma)
                (sigma_or_blank sigma blank)).
      + intros a Hin. unfold sigma_or_blank. now left.
      + match goal with
        | Hsigma : matches (sigma_star_regex sigma) _ |- _ =>
            now apply sigma_star_sound
        end.
    - constructor; [unfold sigma_or_blank; now right | constructor].
  Qed.

  Lemma sigma_star_blank_complete :
    forall sigma blank w,
      matches (sigma_star_regex sigma) w ->
      matches (sigma_star_blank_regex sigma blank) (w ++ [blank]).
  Proof.
    intros sigma blank w Hsigma.
    unfold sigma_star_blank_regex.
    apply M_Cat.
    - exact Hsigma.
    - apply M_Atom.
  Qed.

  Lemma sigma_star_blank_blocks_sound :
    forall sigma blank w,
      matches (Star (sigma_star_blank_regex sigma blank)) w ->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w Hmatch.
    remember (Star (sigma_star_blank_regex sigma blank)) as rstar
      eqn:Hrstar.
    induction Hmatch; inversion Hrstar; subst.
    - constructor.
    - apply forall_app_intro.
      + now apply sigma_star_blank_sound.
      + apply IHHmatch2. reflexivity.
  Qed.

  Lemma matches_star_append :
    forall (r : regex A) u v,
      matches (Star r) u ->
      matches r v ->
      v <> [] ->
      matches (Star r) (u ++ v).
  Proof.
    intros r u v Hstar Hv Hnonempty.
    remember (Star r) as rstar eqn:Hrstar.
    revert r Hrstar v Hv Hnonempty.
    induction Hstar; intros r0 Hrstar v Hv Hnonempty;
      inversion Hrstar; subst.
    - simpl.
      rewrite <- (app_nil_r v).
      eapply M_StarApp with (w1 := v) (w2 := []).
      + exact Hv.
      + exact Hnonempty.
      + apply M_Star0.
    - rewrite <- app_assoc.
      eapply M_StarApp with (w1 := w1) (w2 := w2 ++ v).
      + exact Hstar1.
      + exact H.
      + eapply IHHstar2; eauto.
  Qed.

  Lemma sigma_star_blank_star_sigma_star_sound :
    forall sigma blank w,
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w ->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w Hmatch.
    unfold sigma_star_blank_star_sigma_star_regex in Hmatch.
    inversion Hmatch; subst.
    apply forall_app_intro.
    - now apply sigma_star_blank_blocks_sound.
    - eapply (forall_impl
                (fun a => In a sigma)
                (sigma_or_blank sigma blank)).
      + intros a Hin. unfold sigma_or_blank. now left.
      + now apply sigma_star_sound.
  Qed.

  Lemma sigma_star_blank_star_sigma_star_append_sigma :
    forall sigma blank w a,
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w ->
      In a sigma ->
      matches
        (sigma_star_blank_star_sigma_star_regex sigma blank)
        (w ++ [a]).
  Proof.
    intros sigma blank w a Hmatch Hin.
    unfold sigma_star_blank_star_sigma_star_regex in *.
    inversion Hmatch; subst.
    rewrite <- app_assoc.
    apply M_Cat.
    - assumption.
    - apply sigma_star_complete.
      apply forall_app_intro.
      + now apply sigma_star_sound.
      + constructor; [exact Hin | constructor].
  Qed.

  Lemma sigma_star_blank_star_sigma_star_append_blank :
    forall sigma blank w,
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w ->
      matches
        (sigma_star_blank_star_sigma_star_regex sigma blank)
        (w ++ [blank]).
  Proof.
    intros sigma blank w Hmatch.
    unfold sigma_star_blank_star_sigma_star_regex in *.
    inversion Hmatch; subst.
    rewrite <- app_assoc.
    rewrite <- (app_nil_r (w1 ++ (w2 ++ [blank]))).
    apply M_Cat.
    - eapply matches_star_append.
      + exact H1.
      + apply sigma_star_blank_complete. exact H3.
      + destruct w2; discriminate.
    - apply M_Star0.
  Qed.

  Lemma sigma_star_blank_star_sigma_star_complete :
    forall sigma blank w,
      Forall (sigma_or_blank sigma blank) w ->
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w.
  Proof.
    intros sigma blank w Hover.
    induction w using rev_ind.
    - unfold sigma_star_blank_star_sigma_star_regex.
      change ([] : list A) with (([] : list A) ++ ([] : list A)).
      apply M_Cat; apply M_Star0.
    - destruct (forall_app_inv _ _ _ Hover) as [Hover_w Hover_x].
      inversion Hover_x as [| y ys Hy Hnil Heq]; subst.
      destruct Hy as [Hin | ->].
      + apply sigma_star_blank_star_sigma_star_append_sigma.
        * now apply IHw.
        * exact Hin.
      + apply sigma_star_blank_star_sigma_star_append_blank.
        now apply IHw.
  Qed.

  Theorem sigma_star_blank_star_sigma_star_correct :
    forall sigma blank w,
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w <->
      Forall (sigma_or_blank sigma blank) w.
  Proof.
    intros sigma blank w. split.
    - apply sigma_star_blank_star_sigma_star_sound.
    - apply sigma_star_blank_star_sigma_star_complete.
  Qed.

  Theorem sigma_star_blank_star_sigma_star_equiv :
    forall sigma blank w,
      matches (sigma_star_blank_star_sigma_star_regex sigma blank) w <->
      matches (sigma_plus_blank_star_regex sigma blank) w.
  Proof.
    intros sigma blank w. split.
    - intros Hmatch.
      apply sigma_plus_blank_star_complete.
      now apply sigma_star_blank_star_sigma_star_sound.
    - intros Hmatch.
      apply sigma_star_blank_star_sigma_star_complete.
      now apply sigma_plus_blank_star_sound.
  Qed.
End SigmaBlankIdentity.

Section SigmaBlankIdentityExamples.
  Example sigma_blank_identity_empty_sigma_accepts_blanks :
    matches
      (sigma_star_blank_star_sigma_star_regex ([] : list bool) true)
      [true; true] /\
    matches
      (sigma_plus_blank_star_regex ([] : list bool) true)
      [true; true].
  Proof.
    assert
      (Hover :
        Forall (sigma_or_blank ([] : list bool) true) [true; true]).
    {
      constructor.
      - unfold sigma_or_blank. now right.
      - constructor.
        + unfold sigma_or_blank. now right.
        + constructor.
    }
    split.
    - apply sigma_star_blank_star_sigma_star_complete.
      exact Hover.
    - apply sigma_plus_blank_star_complete.
      exact Hover.
  Qed.

  Example sigma_blank_identity_bool_accepts_mixed :
    matches
      (sigma_star_blank_star_sigma_star_regex [true] false)
      [true; false; true] /\
    matches
      (sigma_plus_blank_star_regex [true] false)
      [true; false; true].
  Proof.
    assert
      (Hover :
        Forall (sigma_or_blank [true] false) [true; false; true]).
    {
      constructor.
      - unfold sigma_or_blank. left. simpl. auto.
      - constructor.
        + unfold sigma_or_blank. now right.
        + constructor.
          * unfold sigma_or_blank. left. simpl. auto.
          * constructor.
    }
    split.
    - apply sigma_star_blank_star_sigma_star_complete.
      exact Hover.
    - apply sigma_plus_blank_star_complete.
      exact Hover.
  Qed.
End SigmaBlankIdentityExamples.
