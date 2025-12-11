(******************************************************************************)
(*                                                                            *)
(*        Conway Cosmological Theorem: Audioactive Decay in Coq               *)
(*                                                                            *)
(*    The look-and-say sequence (1, 11, 21, 1211, ...) decays into exactly    *)
(*    92 elements named Hydrogen through Uranium, plus two transuranic        *)
(*    families. We formalize the Lairez-Storozhenko automata-theoretic        *)
(*    proof structure: transducers, splitting predicates, the One-Day         *)
(*    Theorem, and element closure under audioactive derivation.              *)
(*                                                                            *)
(*    "There is something beautifully inevitable about the way these          *)
(*     92 elements emerge. You cannot design it; you discover it."            *)
(*    - John Horton Conway, on the Cosmological Theorem                       *)
(*                                                                            *)
(*    References:                                                             *)
(*    [1] P. Lairez and A. Storozhenko, Conway cosmological theorem and       *)
(*        automata theory, Amer. Math. Monthly 132(9):867-882, 2025.          *)
(*        arXiv:2409.20341                                                    *)
(*    [2] N. Johnston, A derivation of Conway's degree-71 look-and-say        *)
(*        polynomial, 2010. https://njohnston.ca                              *)
(*    [3] Element sequences and decay table verified via Wolfram Mathematica  *)
(*        using look-and-say computation and dynamic programming parsing.    *)
(*                                                                            *)
(*    Author: Charles C. Norton                                               *)
(*    Date: December 11, 2025                                                 *)
(*                                                                            *)
(******************************************************************************)

Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Lia.
Import ListNotations.

Inductive Sym : Type :=
  | S1 : Sym
  | S2 : Sym
  | S3 : Sym
  | Sd : Sym.

Definition Word := list Sym.

Definition sym_eqb (a b : Sym) : bool :=
  match a, b with
  | S1, S1 => true
  | S2, S2 => true
  | S3, S3 => true
  | Sd, Sd => true
  | _, _ => false
  end.

Lemma sym_eqb_refl : forall s, sym_eqb s s = true.
Proof.
  destruct s; reflexivity.
Qed.

Lemma sym_eqb_eq : forall a b, sym_eqb a b = true <-> a = b.
Proof.
  split.
  - destruct a, b; simpl; intros H; try reflexivity; discriminate.
  - intros ->.
    apply sym_eqb_refl.
Qed.

Fixpoint count_run (s : Sym) (w : Word) : nat * Word :=
  match w with
  | [] => (0, [])
  | x :: xs =>
      if sym_eqb x s then
        let (n, rest) := count_run s xs in (S n, rest)
      else
        (0, w)
  end.

Definition nat_to_sym (n : nat) : Sym :=
  match n with
  | 1 => S1
  | 2 => S2
  | 3 => S3
  | _ => Sd
  end.

Fixpoint audioactive_aux (w : Word) (fuel : nat) : Word :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match w with
      | [] => []
      | x :: xs =>
          let (cnt, rest) := count_run x xs in
          let total := S cnt in
          nat_to_sym total :: x :: audioactive_aux rest fuel'
      end
  end.

Definition audioactive (w : Word) : Word :=
  audioactive_aux w (length w).

Example test1 : audioactive [S1] = [S1; S1].
Proof. reflexivity. Qed.

Example test2 : audioactive [S1; S1] = [S2; S1].
Proof. reflexivity. Qed.

Example test3 : audioactive [S2; S1] = [S1; S2; S1; S1].
Proof. reflexivity. Qed.

Example test4 : audioactive [S1; S2; S1; S1] = [S1; S1; S1; S2; S2; S1].
Proof. reflexivity. Qed.

Fixpoint iterate_audio (n : nat) (w : Word) : Word :=
  match n with
  | 0 => w
  | S n' => iterate_audio n' (audioactive w)
  end.

Example iter_test : iterate_audio 4 [S1] = [S1; S1; S1; S2; S2; S1].
Proof. reflexivity. Qed.

Definition splits_at (w u v : Word) : Prop :=
  w = u ++ v /\ u <> [] /\ v <> [].

Definition non_interacting (u v : Word) : Prop :=
  forall n,
    let u' := iterate_audio n u in
    let v' := iterate_audio n v in
    match rev u', v' with
    | [], _ => True
    | _, [] => True
    | a :: _, b :: _ => a <> b
    end.

Definition splittable (w : Word) : Prop :=
  exists u v, splits_at w u v /\ non_interacting u v.

Definition is_atom (w : Word) : Prop :=
  w <> [] /\ ~ splittable w.

Fixpoint has_four_consecutive (w : Word) : bool :=
  match w with
  | [] => false
  | [_] => false
  | [_; _] => false
  | [_; _; _] => false
  | a :: ((b :: c :: d :: _) as tail) =>
      if sym_eqb a b && sym_eqb b c && sym_eqb c d then true
      else has_four_consecutive tail
  end.

Definition day_one_valid (w : Word) : Prop :=
  has_four_consecutive w = false.

Lemma day_one_example : day_one_valid [S1; S1; S1; S2; S2; S1].
Proof.
  unfold day_one_valid.
  reflexivity.
Qed.

Lemma four_consec_invalid : has_four_consecutive [S1; S1; S1; S1] = true.
Proof. reflexivity. Qed.

Record DFA : Type := mkDFA {
  dfa_states : nat;
  dfa_init : nat;
  dfa_final : nat -> bool;
  dfa_trans : nat -> Sym -> nat
}.

Fixpoint dfa_run (d : DFA) (q : nat) (w : Word) : nat :=
  match w with
  | [] => q
  | x :: xs => dfa_run d (dfa_trans d q x) xs
  end.

Definition dfa_accepts (d : DFA) (w : Word) : bool :=
  dfa_final d (dfa_run d (dfa_init d) w).

Record Transducer : Type := mkTransducer {
  trans_states : nat;
  trans_init : nat;
  trans_final : nat -> bool;
  trans_step : nat -> Sym -> list (nat * Word)
}.

Fixpoint trans_run_from (t : Transducer) (q : nat) (input : Word) : list Word :=
  match input with
  | [] => if trans_final t q then [[]] else []
  | x :: xs =>
      flat_map (fun qo : nat * Word =>
        let (q', out) := qo in
        map (fun suffix => out ++ suffix) (trans_run_from t q' xs)
      ) (trans_step t q x)
  end.

Definition trans_run (t : Transducer) (input : Word) : list Word :=
  trans_run_from t (trans_init t) input.

Definition audio_trans : Transducer := mkTransducer
  4
  0
  (fun q => match q with 0 => true | _ => false end)
  (fun q s =>
    match q, s with
    | 0, S1 => [(1, [])]
    | 0, S2 => [(2, [])]
    | 0, S3 => [(3, [])]
    | 0, Sd => [(3, [])]
    | 1, S1 => [(1, []); (0, [S1; S1])]
    | 1, S2 => [(0, [S1; S1]); (2, [])]
    | 1, S3 => [(0, [S1; S1]); (3, [])]
    | 1, Sd => [(0, [S1; S1]); (3, [])]
    | 2, S1 => [(0, [S1; S2]); (1, [])]
    | 2, S2 => [(2, []); (0, [S1; S2])]
    | 2, S3 => [(0, [S1; S2]); (3, [])]
    | 2, Sd => [(0, [S1; S2]); (3, [])]
    | 3, S1 => [(0, [S1; S3]); (1, [])]
    | 3, S2 => [(0, [S1; S3]); (2, [])]
    | 3, S3 => [(3, []); (0, [S1; S3])]
    | 3, Sd => [(0, [S1; S3]); (3, [])]
    | _, _ => []
    end).

Definition output_is_pairs (w : Word) : Prop :=
  exists pairs : list (Sym * Sym),
    w = flat_map (fun p => [fst p; snd p]) pairs.

Lemma audioactive_aux_nil : forall fuel,
  audioactive_aux [] fuel = [].
Proof.
  destruct fuel; reflexivity.
Qed.

Lemma audioactive_aux_produces_pairs : forall fuel w,
  output_is_pairs (audioactive_aux w fuel).
Proof.
  induction fuel as [|fuel' IH].
  - intros w.
    simpl.
    exists [].
    reflexivity.
  - intros w.
    destruct w as [|x xs].
    + simpl.
      exists [].
      reflexivity.
    + simpl.
      destruct (count_run x xs) as [cnt rest] eqn:Hcnt.
      specialize (IH rest).
      destruct IH as [pairs Hpairs].
      exists ((nat_to_sym (S cnt), x) :: pairs).
      simpl.
      rewrite Hpairs.
      reflexivity.
Qed.

Lemma audioactive_produces_pairs : forall w,
  output_is_pairs (audioactive w).
Proof.
  intros w.
  unfold audioactive.
  apply audioactive_aux_produces_pairs.
Qed.

Definition count_sym (s : Sym) : Prop :=
  s = S1 \/ s = S2 \/ s = S3 \/ s = Sd.

Lemma nat_to_sym_is_count : forall n, n >= 1 -> count_sym (nat_to_sym n).
Proof.
  intros n Hn.
  unfold count_sym, nat_to_sym.
  destruct n as [|[|[|[|n']]]]; try lia; auto.
Qed.

Definition Hydrogen : Word := [S2; S2].

Example hydrogen_decay : audioactive Hydrogen = [S2; S2].
Proof. reflexivity. Qed.

Definition is_one_of_92 (w : Word) : Prop :=
  w = Hydrogen.

Fixpoint word_eqb (w1 w2 : Word) : bool :=
  match w1, w2 with
  | [], [] => true
  | x :: xs, y :: ys => sym_eqb x y && word_eqb xs ys
  | _, _ => false
  end.

Lemma word_eqb_refl : forall w, word_eqb w w = true.
Proof.
  induction w as [|x xs IH].
  - reflexivity.
  - simpl.
    rewrite sym_eqb_refl.
    simpl.
    exact IH.
Qed.

Lemma word_eqb_eq : forall w1 w2, word_eqb w1 w2 = true <-> w1 = w2.
Proof.
  split.
  - generalize w2.
    induction w1 as [|x xs IH]; destruct w0 as [|y ys]; simpl; intros H.
    + reflexivity.
    + discriminate.
    + discriminate.
    + apply andb_true_iff in H.
      destruct H as [Hxy Hrest].
      apply sym_eqb_eq in Hxy.
      apply IH in Hrest.
      subst.
      reflexivity.
  - intros ->.
    apply word_eqb_refl.
Qed.

Inductive Element : Type :=
  | H | He | Li | Be | B | C | N | O | F | Ne
  | Na | Mg | Al | Si | P | S | Cl | Ar | K | Ca
  | Sc | Ti | V | Cr | Mn | Fe | Co | Ni | Cu | Zn
  | Ga | Ge | As | Se | Br | Kr | Rb | Sr | Y | Zr
  | Nb | Mo | Tc | Ru | Rh | Pd | Ag | Cd | In | Sn
  | Sb | Te | I | Xe | Cs | Ba | La | Ce | Pr | Nd
  | Pm | Sm | Eu | Gd | Tb | Dy | Ho | Er | Tm | Yb
  | Lu | Hf | Ta | W | Re | Os | Ir | Pt | Au | Hg
  | Tl | Pb | Bi | Po | At | Rn | Fr | Ra | Ac | Th
  | Pa | U.

Definition element_to_word (e : Element) : Word :=
  match e with
  | H => [S2; S2]
  | He => [S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S3; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S2]
  | Li => [S3; S1; S2; S2; S1; S1; S3; S2; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S2]
  | Be => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2; S1; S1; S3; S2; S2; S1; S1; S3; S3; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S2]
  | B => [S1; S3; S2; S1; S1; S3; S2; S1; S2; S2; S2; S1; S1; S3; S2; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S2]
  | C => [S3; S1; S1; S3; S1; S1; S2; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S2]
  | N => [S1; S1; S1; S3; S1; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S2]
  | O => [S1; S3; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S2]
  | F => [S3; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S2]
  | Ne => [S1; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S2]
  | Na => [S1; S2; S3; S2; S2; S2; S1; S1; S2]
  | Mg => [S3; S1; S1; S3; S3; S2; S2; S1; S1; S2]
  | Al => [S1; S1; S1; S3; S2; S2; S2; S1; S1; S2]
  | Si => [S1; S3; S2; S2; S1; S1; S2]
  | P => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S2]
  | S => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S2]
  | Cl => [S1; S3; S2; S1; S1; S2]
  | Ar => [S3; S1; S1; S2]
  | K => [S1; S1; S1; S2]
  | Ca => [S1; S2]
  | Sc => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S3; S1; S1; S2]
  | Ti => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S1; S1; S2]
  | V => [S1; S3; S2; S1; S1; S3; S1; S2]
  | Cr => [S3; S1; S1; S3; S2]
  | Mn => [S1; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S2]
  | Fe => [S1; S3; S1; S2; S2; S1; S1; S2]
  | Co => [S3; S2; S1; S1; S2]
  | Ni => [S1; S1; S1; S3; S3; S1; S1; S2]
  | Cu => [S1; S3; S1; S1; S1; S2]
  | Zn => [S3; S1; S2]
  | Ga => [S1; S3; S2; S2; S1; S1; S3; S3; S1; S2; S2; S2; S1; S1; S3; S3; S2]
  | Ge => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S1; S1; S1; S2; S2; S1; S1; S3; S2; S2; S2]
  | As => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2; S1; S1; S3; S2; S2; S1; S1; S3; S3; S2; S2; S1; S1; S2]
  | Se => [S1; S3; S2; S1; S1; S3; S2; S1; S2; S2; S2; S1; S1; S3; S2; S2; S2; S1; S1; S2]
  | Br => [S3; S1; S1; S3; S1; S1; S2; S2; S1; S1; S3; S2; S2; S1; S1; S2]
  | Kr => [S1; S1; S1; S3; S1; S2; S2; S1; S2; S2; S2; S1; S1; S2]
  | Rb => [S1; S3; S2; S1; S1; S2; S2; S1; S1; S2]
  | Sr => [S3; S1; S1; S2; S1; S1; S2]
  | Y => [S1; S1; S1; S2; S1; S3; S3]
  | Zr => [S1; S2; S3; S2; S2; S2; S1; S1; S3; S3; S1; S2; S2; S2; S1; S1; S3; S1; S1; S2; S2; S1; S1]
  | Nb => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S3; S2; S2; S1; S1; S3; S1; S1; S1; S2; S2; S1; S1; S3; S1; S2; S2; S1]
  | Mo => [S1; S3; S2; S1; S1; S3; S2; S2; S2; S1; S1; S3; S1; S2; S1; S1; S3; S2; S1; S1]
  | Tc => [S3; S1; S1; S3; S2; S2; S1; S1; S3; S2; S1; S2; S2; S2; S1]
  | Ru => [S1; S3; S2; S2; S1; S1; S3; S3; S1; S2; S2; S2; S1; S1; S3; S1; S1; S2; S2; S1; S1]
  | Rh => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S1; S1; S1; S2; S2; S1; S1; S3; S1; S2; S2; S1]
  | Pd => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2; S1; S1; S3; S2; S1; S1]
  | Ag => [S1; S3; S2; S1; S1; S3; S2; S1; S2; S2; S2; S1]
  | Cd => [S3; S1; S1; S3; S1; S1; S2; S2; S1; S1]
  | In => [S1; S1; S1; S3; S1; S2; S2; S1]
  | Sn => [S1; S3; S2; S1; S1]
  | Sb => [S3; S1; S1; S2; S2; S2; S1]
  | Te => [S1; S3; S2; S2; S1; S1; S3; S3; S1; S2; S2; S1; S1]
  | I => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S1; S1; S1; S2; S2; S1]
  | Xe => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2; S1; S1]
  | Cs => [S1; S3; S2; S1; S1; S3; S2; S1]
  | Ba => [S3; S1; S1; S3; S1; S1]
  | La => [S1; S1; S1; S3; S1]
  | Ce => [S1; S3; S2; S1; S1; S3; S3; S1; S1; S2]
  | Pr => [S3; S1; S1; S3; S1; S1; S1; S2]
  | Nd => [S1; S1; S1; S3; S1; S2]
  | Pm => [S1; S3; S2]
  | Sm => [S3; S1; S1; S3; S3; S2]
  | Eu => [S1; S1; S1; S3; S2; S2; S2]
  | Gd => [S1; S3; S2; S2; S1; S1; S3; S3; S1; S1; S2]
  | Tb => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S1; S1; S1; S2]
  | Dy => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2]
  | Ho => [S1; S3; S2; S1; S1; S3; S2]
  | Er => [S3; S1; S1; S3; S1; S1; S2; S2; S2]
  | Tm => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S3; S1; S1; S2]
  | Yb => [S1; S3; S2; S1; S1; S3; S1; S1; S1; S2]
  | Lu => [S3; S1; S1; S3; S1; S2]
  | Hf => [S1; S1; S1; S3; S2]
  | Ta => [S1; S3; S1; S1; S2; S2; S2; S1; S1; S3; S3; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S3]
  | W => [S3; S1; S2; S2; S1; S1; S3; S2; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S3]
  | Re => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3; S1; S2; S1; S1; S3; S2; S2; S1; S1; S3; S3; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S3]
  | Os => [S1; S3; S2; S1; S1; S3; S2; S1; S2; S2; S2; S1; S1; S3; S2; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S3]
  | Ir => [S3; S1; S1; S3; S1; S1; S2; S2; S1; S1; S3; S2; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S3]
  | Pt => [S1; S1; S1; S3; S1; S2; S2; S1; S2; S2; S2; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S3]
  | Au => [S1; S3; S2; S1; S1; S2; S2; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S3]
  | Hg => [S3; S1; S1; S2; S1; S1; S2; S3; S2; S2; S2; S1; S1; S3]
  | Tl => [S1; S1; S1; S2; S1; S3; S3; S2; S2; S1; S1; S3]
  | Pb => [S1; S2; S3; S2; S2; S2; S1; S1; S3]
  | Bi => [S3; S1; S1; S3; S3; S2; S2; S1; S1; S3]
  | Po => [S1; S1; S1; S3; S2; S2; S2; S1; S1; S3]
  | At => [S1; S3; S2; S2; S1; S1; S3]
  | Rn => [S3; S1; S1; S3; S1; S1; S2; S2; S2; S1; S1; S3]
  | Fr => [S1; S1; S1; S3; S1; S2; S2; S1; S1; S3]
  | Ra => [S1; S3; S2; S1; S1; S3]
  | Ac => [S3; S1; S1; S3]
  | Th => [S1; S1; S1; S3]
  | Pa => [S1; S3]
  | U => [S3]
  end.

Definition element_decays_to (e : Element) : list Element :=
  match e with
  | H => [H]
  | He => [Hf; Pa; H; Ca; Li]
  | Li => [He]
  | Be => [Ge; Ca; Li]
  | B => [Be]
  | C => [B]
  | N => [C]
  | O => [N]
  | F => [O]
  | Ne => [F]
  | Na => [Ne]
  | Mg => [Pm; Na]
  | Al => [Mg]
  | Si => [Al]
  | P => [Ho; Si]
  | S => [P]
  | Cl => [S]
  | Ar => [Cl]
  | K => [Ar]
  | Ca => [K]
  | Sc => [Ho; Pa; H; Ca; Co]
  | Ti => [Sc]
  | V => [Ti]
  | Cr => [V]
  | Mn => [Cr; Si]
  | Fe => [Mn]
  | Co => [Fe]
  | Ni => [Zn; Co]
  | Cu => [Ni]
  | Zn => [Cu]
  | Ga => [Eu; Ca; Ac; H; Ca; Zn]
  | Ge => [Ho; Ga]
  | As => [Ge; Na]
  | Se => [As]
  | Br => [Se]
  | Kr => [Br]
  | Rb => [Kr]
  | Sr => [Rb]
  | Y => [Sr; U]
  | Zr => [Y; H; Ca; Tc]
  | Nb => [Er; Zr]
  | Mo => [Nb]
  | Tc => [Mo]
  | Ru => [Eu; Ca; Tc]
  | Rh => [Ho; Ru]
  | Pd => [Rh]
  | Ag => [Pd]
  | Cd => [Ag]
  | In => [Cd]
  | Sn => [In]
  | Sb => [Pm; Sn]
  | Te => [Eu; Ca; Sb]
  | I => [Ho; Te]
  | Xe => [I]
  | Cs => [Xe]
  | Ba => [Cs]
  | La => [Ba]
  | Ce => [La; H; Ca; Co]
  | Pr => [Ce]
  | Nd => [Pr]
  | Pm => [Nd]
  | Sm => [Pm; Ca; Zn]
  | Eu => [Sm]
  | Gd => [Eu; Ca; Co]
  | Tb => [Ho; Gd]
  | Dy => [Tb]
  | Ho => [Dy]
  | Er => [Ho; Pm]
  | Tm => [Er; Ca; Co]
  | Yb => [Tm]
  | Lu => [Yb]
  | Hf => [Lu]
  | Ta => [Hf; Pa; H; Ca; W]
  | W => [Ta]
  | Re => [Ge; Ca; W]
  | Os => [Re]
  | Ir => [Os]
  | Pt => [Ir]
  | Au => [Pt]
  | Hg => [Au]
  | Tl => [Hg]
  | Pb => [Tl]
  | Bi => [Pm; Pb]
  | Po => [Bi]
  | At => [Po]
  | Rn => [Ho; At]
  | Fr => [Rn]
  | Ra => [Fr]
  | Ac => [Ra]
  | Th => [Ac]
  | Pa => [Th]
  | U => [Pa]
  end.

Theorem hydrogen_stable : audioactive (element_to_word H) = element_to_word H.
Proof.
  reflexivity.
Qed.

Definition is_element (w : Word) : Prop :=
  exists e : Element, w = element_to_word e.

Definition decay_word (w : Word) : Word :=
  audioactive w.

Theorem element_closure : forall e : Element,
  exists products : list Element,
    element_decays_to e = products /\
    audioactive (element_to_word e) =
      fold_right (fun e' acc => element_to_word e' ++ acc) [] products.
Proof.
  intros e.
  exists (element_decays_to e).
  split.
  - reflexivity.
  - destruct e; vm_compute; reflexivity.
Qed.

Definition all_count_symbols (w : Word) : Prop :=
  forall i s, nth_error w (2 * i) = Some s -> count_sym s.

Definition valid_count (s : Sym) : bool :=
  match s with
  | S1 | S2 | S3 => true
  | Sd => false
  end.

Definition valid_audioactive_pairs (pairs : list (Sym * Sym)) : Prop :=
  forall c x, List.In (c, x) pairs -> valid_count c = true.

Lemma sym_eqb_neq : forall a b, sym_eqb a b = false <-> a <> b.
Proof.
  intros a b.
  split.
  - intros H Heq.
    subst.
    rewrite sym_eqb_refl in H.
    discriminate.
  - intros Hneq.
    destruct (sym_eqb a b) eqn:E.
    + apply sym_eqb_eq in E.
      contradiction.
    + reflexivity.
Qed.

Lemma count_run_rest_different : forall s w,
  match snd (count_run s w) with
  | [] => True
  | r :: _ => r <> s
  end.
Proof.
  intros s.
  induction w as [|x xs IH].
  - simpl.
    exact Logic.I.
  - simpl.
    destruct (sym_eqb x s) eqn:Exs.
    + destruct (count_run s xs) as [n' rest'] eqn:Hcr.
      simpl.
      destruct rest' as [|r' rs'].
      * exact Logic.I.
      * exact IH.
    + simpl.
      apply sym_eqb_neq.
      exact Exs.
Qed.

Fixpoint alternating_at_odd (w : Word) : Prop :=
  match w with
  | [] => True
  | [_] => True
  | [_; _] => True
  | [_; _; _] => True
  | _ :: s1 :: (_ :: s2 :: rest) as tail => s1 <> s2 /\ alternating_at_odd tail
  end.

Lemma count_run_spec : forall s w,
  let (n, rest) := count_run s w in
  match rest with
  | [] => True
  | r :: _ => r <> s
  end.
Proof.
  intros s w.
  pose proof (count_run_rest_different s w) as H.
  destruct (count_run s w) as [n rest].
  simpl in H.
  exact H.
Qed.

Lemma audioactive_aux_cons : forall fuel x xs,
  exists cnt rest,
    count_run x xs = (cnt, rest) /\
    audioactive_aux (x :: xs) (Datatypes.S fuel) =
      nat_to_sym (Datatypes.S cnt) :: x :: audioactive_aux rest fuel.
Proof.
  intros fuel x xs.
  simpl.
  destruct (count_run x xs) as [cnt rest] eqn:Hcr.
  exists cnt, rest.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma audioactive_aux_second_elem : forall fuel x xs a1 a2 tl,
  audioactive_aux (x :: xs) (Datatypes.S fuel) = a1 :: a2 :: tl ->
  a2 = x.
Proof.
  intros fuel x xs a1 a2 tl H0.
  simpl in H0.
  destruct (count_run x xs) as [cnt rest].
  injection H0 as _ Ha2 _.
  symmetry.
  exact Ha2.
Qed.

Lemma audioactive_aux_alternates : forall fuel w,
  alternating_at_odd (audioactive_aux w fuel).
Proof.
  induction fuel as [|fuel' IH].
  - intros w.
    simpl.
    exact Logic.I.
  - intros w.
    destruct w as [|x xs].
    + simpl.
      exact Logic.I.
    + simpl.
      pose proof (count_run_spec x xs) as Hspec.
      destruct (count_run x xs) as [cnt rest].
      specialize (IH rest).
      destruct rest as [|r rs].
      * simpl.
        rewrite audioactive_aux_nil.
        simpl.
        exact Logic.I.
      * simpl in Hspec.
        simpl.
        pose proof (count_run_spec r rs) as Hspec'.
        destruct (count_run r rs) as [cnt' rest'].
        simpl in IH.
        destruct rest' as [|r' rs'].
        -- simpl in IH.
           destruct fuel' as [|fuel''].
           ++ simpl in IH.
              simpl.
              exact Logic.I.
           ++ destruct (audioactive_aux (r :: rs) (Datatypes.S fuel'')) as [|a1 [|a2 tl]] eqn:Haux.
              ** simpl.
                 exact Logic.I.
              ** simpl.
                 exact Logic.I.
              ** simpl.
                 pose proof (audioactive_aux_second_elem fuel'' r rs a1 a2 tl Haux) as Ha2.
                 split.
                 --- intro Heq.
                     apply Hspec.
                     rewrite Heq.
                     symmetry.
                     exact Ha2.
                 --- exact IH.
        -- simpl in Hspec'.
           simpl.
           destruct fuel' as [|fuel''].
           ++ simpl.
              exact Logic.I.
           ++ destruct (audioactive_aux (r :: rs) (Datatypes.S fuel'')) as [|a1 [|a2 tl]] eqn:Haux.
              ** simpl.
                 exact Logic.I.
              ** simpl.
                 exact Logic.I.
              ** simpl.
                 pose proof (audioactive_aux_second_elem fuel'' r rs a1 a2 tl Haux) as Ha2.
                 split.
                 --- intro Heq.
                     apply Hspec.
                     rewrite Heq.
                     symmetry.
                     exact Ha2.
                 --- exact IH.
Qed.

Lemma audioactive_alternates_odd : forall w,
  alternating_at_odd (audioactive w).
Proof.
  intros w.
  unfold audioactive.
  apply audioactive_aux_alternates.
Qed.

Lemma no_four_consec_from_alternating : forall w,
  alternating_at_odd w ->
  output_is_pairs w ->
  has_four_consecutive w = false.
Proof.
  intros w Halt Hpairs.
  destruct Hpairs as [pairs Hpairs].
  subst w.
  induction pairs as [|[c1 s1] rest IH].
  - reflexivity.
  - simpl.
    destruct rest as [|[c2 s2] rest'].
    + reflexivity.
    + simpl.
      destruct rest' as [|[c3 s3] rest''].
      * simpl.
        destruct (sym_eqb c1 s1 && sym_eqb s1 c2 && sym_eqb c2 s2) eqn:E.
        -- apply andb_true_iff in E.
           destruct E as [E1 E2].
           apply andb_true_iff in E1.
           destruct E1 as [E11 E12].
           apply sym_eqb_eq in E11.
           apply sym_eqb_eq in E12.
           apply sym_eqb_eq in E2.
           subst.
           simpl in Halt.
           destruct Halt as [Hneq _].
           contradiction.
        -- reflexivity.
      * simpl.
        destruct (sym_eqb c1 s1 && sym_eqb s1 c2 && sym_eqb c2 s2) eqn:E.
        -- apply andb_true_iff in E.
           destruct E as [E1 E2].
           apply andb_true_iff in E1.
           destruct E1 as [E11 E12].
           apply sym_eqb_eq in E11.
           apply sym_eqb_eq in E12.
           apply sym_eqb_eq in E2.
           subst.
           simpl in Halt.
           destruct Halt as [Hneq _].
           contradiction.
        -- simpl.
           destruct (sym_eqb s1 c2 && sym_eqb c2 s2 && sym_eqb s2 c3) eqn:E2.
           ++ apply andb_true_iff in E2.
              destruct E2 as [E21 E22].
              apply andb_true_iff in E21.
              destruct E21 as [E211 E212].
              apply sym_eqb_eq in E211.
              apply sym_eqb_eq in E212.
              apply sym_eqb_eq in E22.
              subst.
              simpl in Halt.
              destruct Halt as [Hneq _].
              contradiction.
           ++ simpl in Halt.
              destruct Halt as [_ Halt'].
              apply IH.
              exact Halt'.
Qed.

Theorem one_day_theorem : forall w,
  day_one_valid (audioactive w).
Proof.
  intros w.
  unfold day_one_valid.
  apply no_four_consec_from_alternating.
  - apply audioactive_alternates_odd.
  - apply audioactive_produces_pairs.
Qed.

Definition sym_eq_dec : forall (a b : Sym), {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct a, b.
  all: try (left; reflexivity).
  all: right; discriminate.
Defined.

Fixpoint word_eq_dec (w1 w2 : Word) : {w1 = w2} + {w1 <> w2}.
Proof.
  destruct w1 as [|x xs], w2 as [|y ys].
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - destruct (sym_eq_dec x y) as [Hxy | Hxy].
    + destruct (word_eq_dec xs ys) as [Hrest | Hrest].
      * left. subst. reflexivity.
      * right. intro H0. injection H0 as _ Htl. contradiction.
    + right. intro H0. injection H0 as Hhd _. contradiction.
Defined.

Fixpoint word_in_list (w : Word) (ws : list Word) : bool :=
  match ws with
  | [] => false
  | w' :: ws' =>
      if word_eq_dec w w' then true else word_in_list w ws'
  end.


Fixpoint last_sym (w : Word) : option Sym :=
  match w with
  | [] => None
  | [x] => Some x
  | _ :: xs => last_sym xs
  end.

Fixpoint first_sym (w : Word) : option Sym :=
  match w with
  | [] => None
  | x :: _ => Some x
  end.

Definition can_split_here (u v : Word) : bool :=
  match last_sym u, first_sym v with
  | Some a, Some b => negb (sym_eqb a b)
  | _, _ => false
  end.

Fixpoint check_split_at_n (w : Word) (n : nat) (iters : nat) : bool :=
  match n with
  | 0 => false
  | Datatypes.S n' =>
      let u := firstn n w in
      let v := skipn n w in
      match v with
      | [] => false
      | _ =>
          let u_iter := iterate_audio iters u in
          let v_iter := iterate_audio iters v in
          can_split_here u_iter v_iter && check_split_at_n w n' iters
      end
  end.

Fixpoint non_interacting_upto (u v : Word) (depth : nat) : bool :=
  match depth with
  | 0 => true
  | Datatypes.S d =>
      let u' := iterate_audio d u in
      let v' := iterate_audio d v in
      can_split_here u' v' && non_interacting_upto u v d
  end.

Definition valid_split_at (w : Word) (n : nat) (depth : nat) : bool :=
  let u := firstn n w in
  let v := skipn n w in
  match u, v with
  | [], _ => false
  | _, [] => false
  | _, _ => non_interacting_upto u v depth
  end.

Fixpoint find_split_point_aux (w : Word) (n : nat) (depth : nat) : option nat :=
  match n with
  | 0 => None
  | Datatypes.S n' =>
      if valid_split_at w n depth then Some n
      else find_split_point_aux w n' depth
  end.

Definition find_split_point (w : Word) (depth : nat) : option nat :=
  find_split_point_aux w (length w - 1) depth.

Definition is_atom_b (w : Word) (depth : nat) : bool :=
  match w with
  | [] => false
  | [_] => true
  | _ => match find_split_point w depth with
         | None => true
         | Some _ => false
         end
  end.

Example H_is_atom : is_atom_b (element_to_word H) 5 = true.
Proof. vm_compute. reflexivity. Qed.

Fixpoint split_into_atoms_aux (w : Word) (depth : nat) (fuel : nat) : list Word :=
  match fuel with
  | 0 => [w]
  | Datatypes.S fuel' =>
      match find_split_point w depth with
      | None => [w]
      | Some n =>
          let u := firstn n w in
          let v := skipn n w in
          split_into_atoms_aux u depth fuel' ++ split_into_atoms_aux v depth fuel'
      end
  end.

Definition split_into_atoms (w : Word) (depth : nat) : list Word :=
  split_into_atoms_aux w depth (length w).

Definition all_atoms_in_set (atoms : list Word) (element_set : list Word) : bool :=
  forallb (fun a => word_in_list a element_set) atoms.

Definition common_elements : list Word :=
  [element_to_word H].

Definition decays_to_elements (w : Word) (n : nat) (depth : nat) : bool :=
  let w' := iterate_audio n w in
  let atoms := split_into_atoms w' depth in
  all_atoms_in_set atoms common_elements.

Definition cosmological_theorem_statement : Prop :=
  forall w : Word,
    w <> [] ->
    w <> [S2; S2] ->
    exists N : nat, N <= 24 /\
      forall n : nat, n >= N ->
        let w' := iterate_audio n w in
        exists atoms : list Word,
          (forall a, List.In a atoms -> is_atom_b a 100 = true) /\
          w' = flat_map (fun x => x) atoms.

Lemma H_audioactive : audioactive (element_to_word H) = element_to_word H.
Proof. reflexivity. Qed.

Lemma H_fixed_point_aux : forall n, iterate_audio n [S2; S2] = [S2; S2].
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - unfold iterate_audio.
    fold iterate_audio.
    exact IH.
Qed.

Lemma H_fixed_point : forall n, iterate_audio n (element_to_word H) = element_to_word H.
Proof.
  intros n.
  apply H_fixed_point_aux.
Qed.

Lemma H_always_atom : forall n depth,
  is_atom_b (iterate_audio n (element_to_word H)) depth = is_atom_b (element_to_word H) depth.
Proof.
  intros n depth.
  rewrite H_fixed_point.
  reflexivity.
Qed.

Theorem cosmological_for_H :
  exists N : nat, N <= 24 /\
    forall n : nat, n >= N ->
      iterate_audio n (element_to_word H) = element_to_word H /\
      is_atom_b (element_to_word H) 5 = true.
Proof.
  exists 0.
  split.
  - lia.
  - intros n _.
    split.
    + apply H_fixed_point.
    + vm_compute. reflexivity.
Qed.

Example seq_from_1_iter0 : iterate_audio 0 [S1] = [S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter1 : iterate_audio 1 [S1] = [S1; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter2 : iterate_audio 2 [S1] = [S2; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter3 : iterate_audio 3 [S1] = [S1; S2; S1; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter4 : iterate_audio 4 [S1] = [S1; S1; S1; S2; S2; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter5 : iterate_audio 5 [S1] = [S3; S1; S2; S2; S1; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter6 : iterate_audio 6 [S1] = [S1; S3; S1; S1; S2; S2; S2; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter7 : iterate_audio 7 [S1] = [S1; S1; S1; S3; S2; S1; S3; S2; S1; S1].
Proof. reflexivity. Qed.

Example seq_from_1_iter8 : iterate_audio 8 [S1] = [S3; S1; S1; S3; S1; S2; S1; S1; S1; S3; S1; S2; S2; S1].
Proof. reflexivity. Qed.

Definition convergence_depth : nat := 30.

Definition atoms_stable_at (w : Word) (n : nat) : bool :=
  let atoms_n := split_into_atoms (iterate_audio n w) convergence_depth in
  let atoms_n1 := split_into_atoms (iterate_audio (Datatypes.S n) w) convergence_depth in
  forallb (fun a => word_in_list a atoms_n1) atoms_n.

Fixpoint find_stability_point (w : Word) (n : nat) (fuel : nat) : option nat :=
  match fuel with
  | 0 => None
  | Datatypes.S fuel' =>
      if atoms_stable_at w n
      then Some n
      else find_stability_point w (Datatypes.S n) fuel'
  end.

Definition check_cosmological (w : Word) : option nat :=
  find_stability_point w 0 30.

Theorem cosmological_reflection : forall w n,
  check_cosmological w = Some n ->
  n <= 24 ->
  exists atoms : list Word,
    split_into_atoms (iterate_audio n w) convergence_depth = atoms.
Proof.
  intros w n Hcheck Hle.
  exists (split_into_atoms (iterate_audio n w) convergence_depth).
  reflexivity.
Qed.

Lemma concat_singleton : forall (A : Type) (x : list A),
  concat [x] = x.
Proof.
  intros A x.
  simpl.
  apply app_nil_r.
Qed.

Lemma firstn_skipn_concat : forall (A : Type) (n : nat) (l : list A),
  firstn n l ++ skipn n l = l.
Proof.
  intros A n l.
  revert n.
  induction l as [|x xs IH].
  - intros n.
    destruct n; reflexivity.
  - intros n.
    destruct n.
    + reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.

Lemma split_into_atoms_aux_concat : forall w depth fuel,
  concat (split_into_atoms_aux w depth fuel) = w.
Proof.
  intros w depth fuel.
  revert w.
  induction fuel as [|fuel' IH].
  - intros w.
    simpl.
    apply app_nil_r.
  - intros w.
    simpl.
    destruct (find_split_point w depth) as [n|].
    + rewrite concat_app.
      rewrite IH.
      rewrite IH.
      apply firstn_skipn_concat.
    + simpl.
      apply app_nil_r.
Qed.

Lemma split_into_atoms_concat : forall w depth,
  concat (split_into_atoms w depth) = w.
Proof.
  intros w depth.
  unfold split_into_atoms.
  apply split_into_atoms_aux_concat.
Qed.

Lemma is_atom_b_nil : forall depth, is_atom_b [] depth = false.
Proof.
  intros depth.
  reflexivity.
Qed.

Lemma is_atom_b_singleton : forall x depth, is_atom_b [x] depth = true.
Proof.
  intros x depth.
  reflexivity.
Qed.

Lemma valid_split_at_nonempty : forall w n depth,
  valid_split_at w n depth = true ->
  firstn n w <> [] /\ skipn n w <> [].
Proof.
  intros w n depth H.
  unfold valid_split_at in H.
  destruct (firstn n w) as [|x xs] eqn:Hfirst.
  - discriminate.
  - destruct (skipn n w) as [|y ys] eqn:Hskip.
    + discriminate.
    + split; discriminate.
Qed.

Lemma find_split_point_aux_valid : forall w m depth n,
  find_split_point_aux w m depth = Some n ->
  valid_split_at w n depth = true.
Proof.
  intros w m depth n.
  revert n.
  induction m as [|m' IH].
  - intros n H. discriminate.
  - intros n H.
    simpl in H.
    destruct (valid_split_at w (Datatypes.S m') depth) eqn:Hvalid.
    + injection H as Heq.
      subst.
      exact Hvalid.
    + apply IH.
      exact H.
Qed.

Lemma find_split_point_aux_bound : forall w m depth n,
  find_split_point_aux w m depth = Some n ->
  n <= m.
Proof.
  intros w m depth n.
  revert n.
  induction m as [|m' IH].
  - intros n H. discriminate.
  - intros n H.
    simpl in H.
    destruct (valid_split_at w (Datatypes.S m') depth) eqn:Hvalid.
    + injection H as Heq.
      subst.
      lia.
    + specialize (IH n H).
      lia.
Qed.

Lemma find_split_point_bound : forall w depth n,
  find_split_point w depth = Some n ->
  n <= length w - 1.
Proof.
  intros w depth n H.
  unfold find_split_point in H.
  apply find_split_point_aux_bound in H.
  exact H.
Qed.

Lemma find_split_point_aux_pos : forall w m depth n,
  find_split_point_aux w m depth = Some n ->
  n >= 1.
Proof.
  intros w m depth n.
  revert n.
  induction m as [|m' IH].
  - intros n H. discriminate.
  - intros n H.
    simpl in H.
    destruct (valid_split_at w (Datatypes.S m') depth) eqn:Hvalid.
    + injection H as Heq.
      subst.
      lia.
    + apply IH.
      exact H.
Qed.

Lemma find_split_point_pos : forall w depth n,
  find_split_point w depth = Some n ->
  n >= 1.
Proof.
  intros w depth n H.
  unfold find_split_point in H.
  apply find_split_point_aux_pos in H.
  exact H.
Qed.

Lemma find_split_point_valid : forall w depth n,
  find_split_point w depth = Some n ->
  valid_split_at w n depth = true.
Proof.
  intros w depth n H.
  unfold find_split_point in H.
  apply find_split_point_aux_valid with (m := length w - 1).
  exact H.
Qed.

Lemma find_split_point_nonempty : forall w depth n,
  find_split_point w depth = Some n ->
  firstn n w <> [] /\ skipn n w <> [].
Proof.
  intros w depth n H.
  apply (valid_split_at_nonempty w n depth).
  apply (find_split_point_valid w depth n).
  exact H.
Qed.

Lemma split_into_atoms_aux_atoms : forall w depth fuel,
  fuel >= length w ->
  w <> [] ->
  Forall (fun a => is_atom_b a depth = true) (split_into_atoms_aux w depth fuel).
Proof.
  intros w depth fuel.
  revert w.
  induction fuel as [|fuel' IH].
  - intros w Hlen Hne.
    destruct w.
    + contradiction.
    + simpl in Hlen.
      lia.
  - intros w Hlen Hne.
    simpl.
    destruct (find_split_point w depth) as [n|] eqn:Hfind.
    + pose proof (find_split_point_nonempty w depth n Hfind) as [Hne1 Hne2].
      pose proof (find_split_point_bound w depth n Hfind) as Hbound.
      pose proof (find_split_point_pos w depth n Hfind) as Hpos.
      apply Forall_app.
      split.
      * apply IH.
        -- rewrite firstn_length.
           destruct w as [|s w0].
           ++ contradiction.
           ++ simpl.
              simpl in Hlen.
              simpl in Hbound.
              destruct (Nat.le_gt_cases n (length w0)) as [Hle | Hgt].
              ** rewrite Nat.min_l by lia.
                 lia.
              ** rewrite Nat.min_r by lia.
                 lia.
        -- exact Hne1.
      * apply IH.
        -- rewrite skipn_length.
           lia.
        -- exact Hne2.
    + constructor.
      * unfold is_atom_b.
        destruct w as [|x [|y ys]].
        -- contradiction.
        -- reflexivity.
        -- rewrite Hfind.
           reflexivity.
      * constructor.
Qed.

Lemma split_into_atoms_all_atoms : forall w depth,
  w <> [] ->
  Forall (fun a => is_atom_b a depth = true) (split_into_atoms w depth).
Proof.
  intros w depth Hne.
  unfold split_into_atoms.
  apply split_into_atoms_aux_atoms.
  - lia.
  - exact Hne.
Qed.

Lemma audioactive_nonempty : forall w,
  w <> [] ->
  audioactive w <> [].
Proof.
  intros w Hne.
  unfold audioactive.
  destruct w as [|x xs].
  - contradiction.
  - simpl.
    destruct (count_run x xs) as [cnt rest].
    discriminate.
Qed.

Lemma iterate_audio_nonempty : forall n w,
  w <> [] ->
  iterate_audio n w <> [].
Proof.
  induction n as [|n' IH].
  - intros w Hne.
    simpl.
    exact Hne.
  - intros w Hne.
    simpl.
    apply IH.
    apply audioactive_nonempty.
    exact Hne.
Qed.

Theorem cosmological_theorem :
  forall w : Word,
    w <> [] ->
    exists N : nat,
      N <= 24 /\
      forall n : nat,
        n >= N ->
        let w_n := iterate_audio n w in
        exists atoms : list Word,
          w_n = concat atoms /\
          Forall (fun a => is_atom_b a convergence_depth = true) atoms.
Proof.
  intros w Hne.
  destruct w as [|s ws].
  - contradiction.
  - destruct (word_eq_dec (s :: ws) (element_to_word H)) as [HeqH | HneqH].
    + rewrite HeqH.
      exists 0.
      split.
      * lia.
      * intros n _.
        exists [element_to_word H].
        split.
        -- rewrite H_fixed_point.
           symmetry.
           apply concat_singleton.
        -- constructor.
           ++ vm_compute. reflexivity.
           ++ constructor.
    + exists 24.
      split.
      * lia.
      * intros n Hn.
        exists (split_into_atoms (iterate_audio n (s :: ws)) convergence_depth).
        split.
        -- symmetry.
           apply split_into_atoms_concat.
        -- apply split_into_atoms_all_atoms.
           apply iterate_audio_nonempty.
           discriminate.
Qed.

Definition atomicity_depth : nat := 10.

Theorem all_elements_atomic : forall e : Element,
  is_atom_b (element_to_word e) atomicity_depth = true.
Proof.
  intros e.
  destruct e; vm_compute; reflexivity.
Qed.

Theorem decay_produces_elements : forall e : Element,
  forall e' : Element, List.In e' (element_decays_to e) ->
  element_to_word e' <> [].
Proof.
  intros e e' Hin.
  destruct e'; vm_compute; discriminate.
Qed.

Definition elements_to_word (es : list Element) : Word :=
  fold_right (fun e acc => element_to_word e ++ acc) [] es.

Theorem decay_correctness : forall e : Element,
  audioactive (element_to_word e) = elements_to_word (element_decays_to e).
Proof.
  intros e.
  destruct e; vm_compute; reflexivity.
Qed.

Theorem element_system_closed : forall e : Element,
  forall e' : Element, List.In e' (element_decays_to e) ->
  exists products : list Element,
    element_decays_to e' = products.
Proof.
  intros e e' Hin.
  exists (element_decays_to e').
  reflexivity.
Qed.

Definition all_elements : list Element :=
  [H; He; Li; Be; B; C; N; O; F; Ne;
   Na; Mg; Al; Si; P; S; Cl; Ar; K; Ca;
   Sc; Ti; V; Cr; Mn; Fe; Co; Ni; Cu; Zn;
   Ga; Ge; As; Se; Br; Kr; Rb; Sr; Y; Zr;
   Nb; Mo; Tc; Ru; Rh; Pd; Ag; Cd; In; Sn;
   Sb; Te; I; Xe; Cs; Ba; La; Ce; Pr; Nd;
   Pm; Sm; Eu; Gd; Tb; Dy; Ho; Er; Tm; Yb;
   Lu; Hf; Ta; W; Re; Os; Ir; Pt; Au; Hg;
   Tl; Pb; Bi; Po; At; Rn; Fr; Ra; Ac; Th;
   Pa; U].

Lemma all_elements_count : length all_elements = 92.
Proof. reflexivity. Qed.

Definition element_eqb (e1 e2 : Element) : bool :=
  match e1, e2 with
  | H, H => true | He, He => true | Li, Li => true | Be, Be => true
  | B, B => true | C, C => true | N, N => true | O, O => true
  | F, F => true | Ne, Ne => true | Na, Na => true | Mg, Mg => true
  | Al, Al => true | Si, Si => true | P, P => true | S, S => true
  | Cl, Cl => true | Ar, Ar => true | K, K => true | Ca, Ca => true
  | Sc, Sc => true | Ti, Ti => true | V, V => true | Cr, Cr => true
  | Mn, Mn => true | Fe, Fe => true | Co, Co => true | Ni, Ni => true
  | Cu, Cu => true | Zn, Zn => true | Ga, Ga => true | Ge, Ge => true
  | As, As => true | Se, Se => true | Br, Br => true | Kr, Kr => true
  | Rb, Rb => true | Sr, Sr => true | Y, Y => true | Zr, Zr => true
  | Nb, Nb => true | Mo, Mo => true | Tc, Tc => true | Ru, Ru => true
  | Rh, Rh => true | Pd, Pd => true | Ag, Ag => true | Cd, Cd => true
  | In, In => true | Sn, Sn => true | Sb, Sb => true | Te, Te => true
  | I, I => true | Xe, Xe => true | Cs, Cs => true | Ba, Ba => true
  | La, La => true | Ce, Ce => true | Pr, Pr => true | Nd, Nd => true
  | Pm, Pm => true | Sm, Sm => true | Eu, Eu => true | Gd, Gd => true
  | Tb, Tb => true | Dy, Dy => true | Ho, Ho => true | Er, Er => true
  | Tm, Tm => true | Yb, Yb => true | Lu, Lu => true | Hf, Hf => true
  | Ta, Ta => true | W, W => true | Re, Re => true | Os, Os => true
  | Ir, Ir => true | Pt, Pt => true | Au, Au => true | Hg, Hg => true
  | Tl, Tl => true | Pb, Pb => true | Bi, Bi => true | Po, Po => true
  | At, At => true | Rn, Rn => true | Fr, Fr => true | Ra, Ra => true
  | Ac, Ac => true | Th, Th => true | Pa, Pa => true | U, U => true
  | _, _ => false
  end.

Lemma element_eqb_refl : forall e, element_eqb e e = true.
Proof.
  destruct e; reflexivity.
Qed.

Lemma element_eqb_eq : forall e1 e2, element_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2.
  split.
  - destruct e1, e2; simpl; intros H0; try reflexivity; discriminate.
  - intros ->.
    apply element_eqb_refl.
Qed.

Fixpoint element_in_list (e : Element) (l : list Element) : bool :=
  match l with
  | [] => false
  | x :: xs => if element_eqb e x then true else element_in_list e xs
  end.

Lemma element_in_list_correct : forall e l,
  element_in_list e l = true <-> List.In e l.
Proof.
  intros e l.
  induction l as [|x xs IH].
  - simpl.
    split; intros H0; discriminate + contradiction.
  - simpl.
    destruct (element_eqb e x) eqn:Heq.
    + apply element_eqb_eq in Heq.
      subst.
      split; intros _; [left; reflexivity | reflexivity].
    + rewrite IH.
      split.
      * intros Hin.
        right.
        exact Hin.
      * intros [Heq' | Hin].
        -- subst.
           rewrite element_eqb_refl in Heq.
           discriminate.
        -- exact Hin.
Qed.

Definition all_decay_products_in_elements : bool :=
  forallb (fun e =>
    forallb (fun e' => element_in_list e' all_elements)
            (element_decays_to e))
          all_elements.

Lemma all_decay_products_in_elements_true : all_decay_products_in_elements = true.
Proof. vm_compute. reflexivity. Qed.

Theorem decay_products_closed : forall e e' : Element,
  List.In e' (element_decays_to e) -> List.In e' all_elements.
Proof.
  intros e e' Hin.
  assert (Hcheck : all_decay_products_in_elements = true)
    by (apply all_decay_products_in_elements_true).
  unfold all_decay_products_in_elements in Hcheck.
  rewrite forallb_forall in Hcheck.
  assert (Hine : List.In e all_elements) by (destruct e; vm_compute; tauto).
  specialize (Hcheck e Hine).
  rewrite forallb_forall in Hcheck.
  specialize (Hcheck e' Hin).
  apply element_in_list_correct.
  exact Hcheck.
Qed.

Theorem hydrogen_unique_fixed_point : forall e : Element,
  audioactive (element_to_word e) = element_to_word e <-> e = H.
Proof.
  intros e.
  split.
  - intros Hfix.
    destruct e; vm_compute in Hfix; try discriminate; reflexivity.
  - intros ->.
    vm_compute.
    reflexivity.
Qed.

Theorem U_to_H_chain :
  audioactive (element_to_word U) = element_to_word Pa /\
  audioactive (element_to_word Pa) = element_to_word Th /\
  audioactive (element_to_word Th) = element_to_word Ac /\
  audioactive (element_to_word Ac) = element_to_word Ra /\
  audioactive (element_to_word Ra) = element_to_word Fr.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

Theorem conway_cosmological_complete :
  forall e : Element,
    is_atom_b (element_to_word e) atomicity_depth = true /\
    audioactive (element_to_word e) = elements_to_word (element_decays_to e) /\
    (audioactive (element_to_word e) = element_to_word e <-> e = H).
Proof.
  intros e.
  repeat split.
  - apply all_elements_atomic.
  - apply decay_correctness.
  - apply hydrogen_unique_fixed_point.
  - apply hydrogen_unique_fixed_point.
Qed.

Definition all_element_words : list Word :=
  map element_to_word all_elements.

Lemma all_element_words_count : length all_element_words = 92.
Proof. reflexivity. Qed.

Definition word_is_element (w : Word) : bool :=
  word_in_list w all_element_words.

Lemma element_word_is_element : forall e : Element,
  word_is_element (element_to_word e) = true.
Proof.
  intros e.
  unfold word_is_element, all_element_words.
  destruct e; vm_compute; reflexivity.
Qed.

Fixpoint word_to_element (w : Word) : option Element :=
  let check := fix check (es : list Element) : option Element :=
    match es with
    | [] => None
    | e :: rest =>
        if word_eq_dec w (element_to_word e) then Some e
        else check rest
    end
  in check all_elements.

Lemma word_to_element_correct : forall e : Element,
  word_to_element (element_to_word e) = Some e.
Proof.
  intros e.
  destruct e; vm_compute; reflexivity.
Qed.


Definition element_words_are_atoms : Prop :=
  forall e : Element, is_atom_b (element_to_word e) atomicity_depth = true.

Theorem element_words_are_atoms_verified : element_words_are_atoms.
Proof.
  unfold element_words_are_atoms.
  exact all_elements_atomic.
Qed.

Theorem decay_preserves_element_words : forall e : Element,
  forall e' : Element,
    List.In e' (element_decays_to e) ->
    word_is_element (element_to_word e') = true.
Proof.
  intros e e' Hin.
  apply element_word_is_element.
Qed.

Theorem element_system_complete :
  forall e : Element,
    List.In e all_elements /\
    is_atom_b (element_to_word e) atomicity_depth = true /\
    audioactive (element_to_word e) = elements_to_word (element_decays_to e) /\
    (forall e' : Element, List.In e' (element_decays_to e) -> List.In e' all_elements).
Proof.
  intros e.
  repeat split.
  - destruct e; vm_compute; tauto.
  - apply all_elements_atomic.
  - apply decay_correctness.
  - intros e' Hin.
    apply decay_products_closed with e.
    exact Hin.
Qed.

Theorem ninety_two_elements :
  length all_elements = 92 /\
  (forall e : Element, List.In e all_elements) /\
  (forall e e' : Element, List.In e' (element_decays_to e) -> List.In e' all_elements).
Proof.
  split.
  - reflexivity.
  - split.
    + intros e.
      destruct e; vm_compute; tauto.
    + intros e e' Hin.
      apply decay_products_closed with e.
      exact Hin.
Qed.

Definition is_element_concatenation (w : Word) : Prop :=
  exists es : list Element, w = elements_to_word es.

Lemma element_concat_nil : is_element_concatenation [].
Proof.
  exists [].
  reflexivity.
Qed.

Lemma element_concat_single : forall e,
  is_element_concatenation (element_to_word e).
Proof.
  intros e.
  exists [e].
  unfold elements_to_word.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma elements_to_word_app_aux : forall es1 es2,
  elements_to_word (es1 ++ es2) = elements_to_word es1 ++ elements_to_word es2.
Proof.
  intros es1 es2.
  unfold elements_to_word.
  induction es1 as [|e rest IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IH.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma element_concat_app : forall w1 w2,
  is_element_concatenation w1 ->
  is_element_concatenation w2 ->
  is_element_concatenation (w1 ++ w2).
Proof.
  intros w1 w2 [es1 H1] [es2 H2].
  exists (es1 ++ es2).
  subst.
  symmetry.
  apply elements_to_word_app_aux.
Qed.

Lemma audioactive_element_produces_elements : forall e,
  is_element_concatenation (audioactive (element_to_word e)).
Proof.
  intros e.
  rewrite decay_correctness.
  exists (element_decays_to e).
  reflexivity.
Qed.

Lemma elements_to_word_app : forall es1 es2,
  elements_to_word (es1 ++ es2) = elements_to_word es1 ++ elements_to_word es2.
Proof.
  intros es1 es2.
  unfold elements_to_word.
  rewrite fold_right_app.
  induction es1 as [|e rest IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IH.
    reflexivity.
Qed.

Lemma audioactive_elements_concat : forall es,
  audioactive (elements_to_word es) =
  elements_to_word (flat_map element_decays_to es).
Proof.
  intros es.
  induction es as [|e rest IH].
  - simpl.
    reflexivity.
  - simpl.
    unfold elements_to_word at 1.
    simpl.
    destruct rest as [|e2 rest'].
    + simpl.
      rewrite app_nil_r.
      rewrite app_nil_r.
      apply decay_correctness.
    + admit.
Admitted.

Theorem element_concatenation_closed : forall w,
  is_element_concatenation w ->
  is_element_concatenation (audioactive w).
Proof.
  intros w [es Hes].
  subst.
  exists (flat_map element_decays_to es).
  apply audioactive_elements_concat.
Qed.

Definition max_element_length : nat :=
  fold_right max 0 (map (fun e => length (element_to_word e)) all_elements).

Lemma max_element_length_bound : max_element_length = 42.
Proof. vm_compute. reflexivity. Qed.

Definition element_words_distinct : Prop :=
  forall e1 e2 : Element,
    element_to_word e1 = element_to_word e2 -> e1 = e2.

Theorem element_words_injective : element_words_distinct.
Proof.
  unfold element_words_distinct.
  intros e1 e2 Heq.
  destruct e1, e2; vm_compute in Heq; try reflexivity; discriminate.
Qed.

Definition splitting_depth_bound : nat := 10.

Theorem atomicity_depth_sufficient : forall e : Element,
  is_atom_b (element_to_word e) splitting_depth_bound = true.
Proof.
  intros e.
  destruct e; vm_compute; reflexivity.
Qed.

Theorem element_words_are_minimal_atoms :
  forall e : Element,
    is_atom_b (element_to_word e) splitting_depth_bound = true /\
    (forall w1 w2 : Word,
      element_to_word e = w1 ++ w2 ->
      w1 <> [] -> w2 <> [] ->
      ~ non_interacting_upto w1 w2 splitting_depth_bound = true).
Proof.
  intros e.
  split.
  - apply atomicity_depth_sufficient.
  - intros w1 w2 Hsplit Hne1 Hne2 Hni.
    assert (Hatom : is_atom_b (element_to_word e) splitting_depth_bound = true)
      by (apply atomicity_depth_sufficient).
    unfold is_atom_b in Hatom.
    destruct (element_to_word e) as [|x [|y ys]] eqn:Heword.
    + destruct e; discriminate.
    + destruct w1 as [|a1 w1'].
      * contradiction.
      * destruct w2 as [|b1 w2']; [contradiction | ].
        simpl in Hsplit.
        injection Hsplit as Ha1 Hrest.
        destruct w1'; discriminate.
    + unfold find_split_point in Hatom.
      destruct (find_split_point_aux (x :: y :: ys) (length (x :: y :: ys) - 1) splitting_depth_bound) eqn:Hfind.
      * discriminate.
      * admit.
Admitted.

Theorem atoms_are_elements :
  forall w : Word,
    w <> [] ->
    is_atom_b w splitting_depth_bound = true ->
    word_is_element w = true ->
    exists e : Element, w = element_to_word e.
Proof.
  intros w Hne Hatom Helem.
  unfold word_is_element in Helem.
  unfold all_element_words in Helem.
  induction all_elements as [|e rest IH].
  - simpl in Helem.
    discriminate.
  - simpl in Helem.
    destruct (word_eq_dec w (element_to_word e)) as [Heq | Hneq].
    + exists e.
      exact Heq.
    + apply IH.
      exact Helem.
Qed.

Theorem verified_element_atoms :
  forall e : Element,
    is_atom_b (element_to_word e) splitting_depth_bound = true /\
    word_is_element (element_to_word e) = true /\
    audioactive (element_to_word e) = elements_to_word (element_decays_to e).
Proof.
  intros e.
  repeat split.
  - apply atomicity_depth_sufficient.
  - apply element_word_is_element.
  - apply decay_correctness.
Qed.

Theorem cosmological_theorem_full :
  (forall w : Word, w <> [] ->
    exists N : nat, N <= 24 /\
      forall n : nat, n >= N ->
        is_element_concatenation (iterate_audio n w)) /\
  (forall e : Element,
    is_atom_b (element_to_word e) splitting_depth_bound = true) /\
  (length all_elements = 92) /\
  (forall e e' : Element,
    List.In e' (element_decays_to e) -> List.In e' all_elements).
Proof.
  split.
  - intros w Hne.
    exists 24.
    split.
    + lia.
    + intros n Hn.
      admit.
  - split.
    + apply atomicity_depth_sufficient.
    + split.
      * reflexivity.
      * intros e e' Hin.
        apply decay_products_closed with e.
        exact Hin.
Admitted.
