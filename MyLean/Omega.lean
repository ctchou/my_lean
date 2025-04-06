/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Order.Filter.ATTopBot.Basic

open Sum Filter Function

section Sequence

def AppendInf {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun i ↦ if h : i < xl.length then xl[i] else xs (i - xl.length)

def InfOcc {X : Type*} (xs : ℕ → X) : Set X :=
  { s : X | ∃ᶠ i in atTop, xs i = s }

end Sequence

section Automaton

class Automaton (A : Type*) (S : Type*) where
  init : Set S
  next : S → A → Set S

class DetAutomaton (A : Type*) (S : Type*) extends Automaton A S where
  det_init : init.ncard = 1
  det_next : ∀ s a, (next s a).ncard = 1

variable {A : Type*} {S : Type*}

def FinRun (M : Automaton A S) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : Fin n, ss (i + 1) ∈ M.next (ss i) (as i)

def InfRun (M : Automaton A S) (as : ℕ → A) (ss : ℕ → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : ℕ, ss (i + 1) ∈ M.next (ss i) (as i)

def FinAccept (M : Automaton A S) (acc : Set S) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → S, FinRun M n as ss ∧ ss n ∈ acc

def BuchiAccept (M : Automaton A S) (acc : Set S) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ InfOcc ss ∩ acc ≠ ∅

def MullerAccept (M : Automaton A S) (accSet : Set (Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∃ acc ∈ accSet, InfOcc ss = acc

def RabinAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∃ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ ∧ InfOcc ss ∩ pair.2 = ∅

def StreettAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfRun M as ss ∧ ∀ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ → InfOcc ss ∩ pair.2 ≠ ∅

def RegLangOf (M : Automaton A S) (acc : Set S) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn as }

def OmegaRegLangOf (M : Automaton A S) (acc : Set S) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end Automaton

section RegLangUnion

variable {A : Type*} {S0 S1 : Type*}

def AutomatonUnion (M0 : Automaton A S0) (M1 : Automaton A S1) : Automaton A (S0 ⊕ S1) where
  init := inl '' (M0.init) ∪ inr '' (M1.init)
  next := fun s a ↦
    match s with
    | inl s0 => inl '' (M0.next s0 a)
    | inr s1 => inr '' (M1.next s1 a)

variable (M0 : Automaton A S0) (M1 : Automaton A S1)

lemma automaton_union_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (S0 ⊕ S1)) :
    FinRun (AutomatonUnion M0 M1) n as ss ↔
      (∃ ss0, FinRun M0 n as ss0 ∧ ss = inl ∘ ss0) ∨
      (∃ ss1, FinRun M1 n as ss1 ∧ ss = inr ∘ ss1) :=
  sorry

lemma automaton_union_inf_run (as : ℕ → A) (ss : ℕ → (S0 ⊕ S1)) :
    InfRun (AutomatonUnion M0 M1) as ss ↔
      (∃ ss0, InfRun M0 as ss0 ∧ ss = inl ∘ ss0) ∨
      (∃ ss1, InfRun M1 as ss1 ∧ ss = inr ∘ ss1) := by
  constructor
  · sorry
  · rintro (⟨ss0, h_run, h_ss⟩ | ⟨ss1, h_run, h_ss⟩) <;> rw [h_ss]
    constructor
    · constructor
      · simp [Automaton.init, AutomatonUnion]
        exact h_run.1
      · intro i
        simp [Automaton.next, AutomatonUnion]
        exact h_run.2 i
    · sorry

variable (acc0 : Set S0) (acc1 : Set S1)

theorem reg_lang_union :
    ∃ S, ∃ M : Automaton A S, ∃ acc, RegLangOf M acc = RegLangOf M0 acc0 ∪ RegLangOf M1 acc1 :=
  sorry

theorem omega_reg_lang_union :
    ∃ S, ∃ M : Automaton A S, ∃ acc, OmegaRegLangOf M acc = OmegaRegLangOf M0 acc0 ∪ OmegaRegLangOf M1 acc1 :=
  sorry

end RegLangUnion
