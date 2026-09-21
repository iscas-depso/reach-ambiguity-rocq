From Stdlib Require Import List Arith Bool.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import FiniteAmbiguity.
From PositionAutomata.Regex Require Import FolianceProperties.

(** Paper-aligned examples.

    The project syntax does not have native character classes or counted
    repetitions yet.  This file models paper Example 1,

      [^\x3e]{0,300}\x2fURI\x28data

    with explicit atoms for byte literals and one class atom [not_gt].  The
    counted repetition {0,n} is represented by n copies of (not_gt | eps).
    The definitions for n = 300 and attack length 150 are present; the proved
    examples use the small instance n = 4, m = 2, where C(4,2) = 6 is cheap to
    compute and directly illustrates the same mechanism. *)

Inductive foliance_demo_symbol : Type :=
| Byte : nat -> foliance_demo_symbol
| NotGt : foliance_demo_symbol.

Definition foliance_demo_symbol_eqb (x y : foliance_demo_symbol) : bool :=
  match x, y with
  | Byte x', Byte y' => Nat.eqb x' y'
  | NotGt, NotGt => true
  | _, _ => false
  end.

Definition byte_gt : foliance_demo_symbol := Byte 62.       (* \x3e, '>' *)
Definition byte_slash : foliance_demo_symbol := Byte 47.    (* \x2f, '/' *)
Definition byte_lparen : foliance_demo_symbol := Byte 40.   (* \x28, '(' *)
Definition byte_U : foliance_demo_symbol := Byte 85.
Definition byte_R : foliance_demo_symbol := Byte 82.
Definition byte_I : foliance_demo_symbol := Byte 73.
Definition byte_d : foliance_demo_symbol := Byte 100.
Definition byte_a : foliance_demo_symbol := Byte 97.
Definition byte_t : foliance_demo_symbol := Byte 116.
Definition byte_x : foliance_demo_symbol := Byte 120.

Definition foliance_demo_label_matches
    (label input : foliance_demo_symbol) : bool :=
  match label, input with
  | Byte x, Byte y => Nat.eqb x y
  | NotGt, Byte y => negb (Nat.eqb y 62)
  | _, _ => false
  end.

Definition foliance_demo_alphabet : list foliance_demo_symbol :=
  [byte_x; byte_slash; byte_U; byte_R; byte_I; byte_lparen;
   byte_d; byte_a; byte_t; byte_gt].

Definition opt_not_gt : regex foliance_demo_symbol :=
  Alt (Atom NotGt) Eps.

Fixpoint repeat_cat {A : Type} (n : nat) (r : regex A) : regex A :=
  match n with
  | O => Eps
  | S n' => Cat r (repeat_cat n' r)
  end.

Definition foliance_demo_suffix : regex foliance_demo_symbol :=
  Cat (Atom byte_slash)
    (Cat (Atom byte_U)
      (Cat (Atom byte_R)
        (Cat (Atom byte_I)
          (Cat (Atom byte_lparen)
            (Cat (Atom byte_d)
              (Cat (Atom byte_a)
                (Cat (Atom byte_t) (Atom byte_a)))))))).

Definition foliance_demo_regex (n : nat) : regex foliance_demo_symbol :=
  Cat (repeat_cat n opt_not_gt) foliance_demo_suffix.

Fixpoint repeat_symbol {A : Type} (n : nat) (a : A) : list A :=
  match n with
  | O => []
  | S n' => a :: repeat_symbol n' a
  end.

Definition foliance_demo_regex_300 : regex foliance_demo_symbol :=
  foliance_demo_regex 300.

Definition foliance_demo_attack_150 : list foliance_demo_symbol :=
  repeat_symbol 150 byte_x.

Definition foliance_demo_regex_4 : regex foliance_demo_symbol :=
  foliance_demo_regex 4.

Definition foliance_demo_attack_2 : list foliance_demo_symbol :=
  repeat_symbol 2 byte_x.

Definition foliance_demo_nfa_4 : @finite_nfa foliance_demo_symbol :=
  regex_foliance_nfa
    foliance_demo_alphabet
    foliance_demo_label_matches
    foliance_demo_regex_4.

Example foliance_demo_attack_2_rejected :
  rejectedb foliance_demo_nfa_4 foliance_demo_attack_2 = true.
Proof. vm_compute. reflexivity. Qed.

Example foliance_demo_prefix_xx_eta :
  eta_word foliance_demo_nfa_4 foliance_demo_attack_2 = 6.
Proof. vm_compute. reflexivity. Qed.

Example foliance_demo_attack_2_eta_prefix_max :
  eta_prefix_max foliance_demo_nfa_4 foliance_demo_attack_2 = 6.
Proof. vm_compute. reflexivity. Qed.

Example foliance_demo_attack_2_is_6_foliance :
  k_folianceb foliance_demo_nfa_4 6 foliance_demo_attack_2 = true.
Proof. vm_compute. reflexivity. Qed.

Example foliance_demo_attack_2_sound_witness :
  k_foliance foliance_demo_nfa_4 6 foliance_demo_attack_2.
Proof.
  apply k_folianceb_correct.
  vm_compute. reflexivity.
Qed.
