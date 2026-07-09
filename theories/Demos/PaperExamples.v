From Stdlib Require Import List Arith Bool.
Import ListNotations.

From PositionAutomata.Core Require Import Syntax.
From PositionAutomata.Ambiguity Require Import DegreeofAmbiguity.
From PositionAutomata.Regex Require Import ReachAmbiguityFoliance.

(** Paper-aligned examples.

    The project syntax does not have native character classes or counted
    repetitions yet.  This file models paper Example 1,

      [^\x3e]{0,300}\x2fURI\x28data

    with explicit atoms for byte literals and one class atom [not_gt].  The
    counted repetition {0,n} is represented by n copies of (not_gt | eps).
    The definitions for n = 300 and attack length 150 are present; the proved
    examples use the small instance n = 4, m = 2, where C(4,2) = 6 is cheap to
    compute and directly illustrates the same mechanism. *)

Inductive paper_symbol : Type :=
| Byte : nat -> paper_symbol
| NotGt : paper_symbol.

Definition paper_symbol_eqb (x y : paper_symbol) : bool :=
  match x, y with
  | Byte x', Byte y' => Nat.eqb x' y'
  | NotGt, NotGt => true
  | _, _ => false
  end.

Definition byte_gt : paper_symbol := Byte 62.       (* \x3e, '>' *)
Definition byte_slash : paper_symbol := Byte 47.    (* \x2f, '/' *)
Definition byte_lparen : paper_symbol := Byte 40.   (* \x28, '(' *)
Definition byte_U : paper_symbol := Byte 85.
Definition byte_R : paper_symbol := Byte 82.
Definition byte_I : paper_symbol := Byte 73.
Definition byte_d : paper_symbol := Byte 100.
Definition byte_a : paper_symbol := Byte 97.
Definition byte_t : paper_symbol := Byte 116.
Definition byte_x : paper_symbol := Byte 120.

Definition paper_label_matches
    (label input : paper_symbol) : bool :=
  match label, input with
  | Byte x, Byte y => Nat.eqb x y
  | NotGt, Byte y => negb (Nat.eqb y 62)
  | _, _ => false
  end.

Definition paper_alphabet : list paper_symbol :=
  [byte_x; byte_slash; byte_U; byte_R; byte_I; byte_lparen;
   byte_d; byte_a; byte_t; byte_gt].

Definition opt_not_gt : regex paper_symbol :=
  Alt (Atom NotGt) Eps.

Fixpoint repeat_cat {A : Type} (n : nat) (r : regex A) : regex A :=
  match n with
  | O => Eps
  | S n' => Cat r (repeat_cat n' r)
  end.

Definition paper_example1_suffix : regex paper_symbol :=
  Cat (Atom byte_slash)
    (Cat (Atom byte_U)
      (Cat (Atom byte_R)
        (Cat (Atom byte_I)
          (Cat (Atom byte_lparen)
            (Cat (Atom byte_d)
              (Cat (Atom byte_a)
                (Cat (Atom byte_t) (Atom byte_a)))))))).

Definition paper_example1_regex (n : nat) : regex paper_symbol :=
  Cat (repeat_cat n opt_not_gt) paper_example1_suffix.

Fixpoint repeat_symbol {A : Type} (n : nat) (a : A) : list A :=
  match n with
  | O => []
  | S n' => a :: repeat_symbol n' a
  end.

Definition paper_example1_regex_300 : regex paper_symbol :=
  paper_example1_regex 300.

Definition paper_example1_attack_150 : list paper_symbol :=
  repeat_symbol 150 byte_x.

Definition paper_example1_regex_4 : regex paper_symbol :=
  paper_example1_regex 4.

Definition paper_example1_attack_2 : list paper_symbol :=
  repeat_symbol 2 byte_x.

Definition paper_example1_nfa_4 : @finite_nfa paper_symbol :=
  regex_foliance_nfa
    paper_alphabet
    paper_label_matches
    paper_example1_regex_4.

Example paper_example1_attack_2_rejected :
  rejectedb paper_example1_nfa_4 paper_example1_attack_2 = true.
Proof. vm_compute. reflexivity. Qed.

Example paper_example1_prefix_xx_eta :
  eta_word paper_example1_nfa_4 paper_example1_attack_2 = 6.
Proof. vm_compute. reflexivity. Qed.

Example paper_example1_attack_2_eta_prefix_max :
  eta_prefix_max paper_example1_nfa_4 paper_example1_attack_2 = 6.
Proof. vm_compute. reflexivity. Qed.

Example paper_example1_attack_2_is_6_foliance :
  k_folianceb paper_example1_nfa_4 6 paper_example1_attack_2 = true.
Proof. vm_compute. reflexivity. Qed.

Example paper_example1_attack_2_sound_witness :
  k_foliance paper_example1_nfa_4 6 paper_example1_attack_2.
Proof.
  apply k_folianceb_correct.
  vm_compute. reflexivity.
Qed.
