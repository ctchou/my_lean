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
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.Filter.ATTopBot.Basic

open BigOperators Function Filter Set Sum Sigma

section Sequence

def AppendInf {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun i ↦ if h : i < xl.length then xl[i] else xs (i - xl.length)

def InfOcc {X : Type*} (xs : ℕ → X) : Set X :=
  { s : X | ∃ᶠ i in atTop, xs i = s }

end Sequence

section Automaton

class Automaton (A : Type*) where
  State : Type*
  init : Set State
  next : State → A → Set State

class DetAutomaton (A : Type*) extends Automaton A where
  det_init : init.ncard = 1
  det_next : ∀ s a, (next s a).ncard = 1

variable {A : Type*}

def FinRun (M : Automaton A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧
  ∀ k : Fin n, ss (k + 1) ∈ M.next (ss k) (as k)

def InfRun (M : Automaton A) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧
  ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)

def FinAccept (M : Automaton A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, FinRun M n as ss ∧ ss n ∈ acc

def BuchiAccept (M : Automaton A) (acc : Set M.State) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ InfOcc ss ∩ acc ≠ ∅

def MullerAccept (M : Automaton A) (accSet : Set (Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ acc ∈ accSet, InfOcc ss = acc

def RabinAccept (M : Automaton A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ ∧ InfOcc ss ∩ pair.2 = ∅

def StreettAccept (M : Automaton A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∀ pair ∈ accPairs, InfOcc ss ∩ pair.1 ≠ ∅ → InfOcc ss ∩ pair.2 ≠ ∅

def RegLangOf (M : Automaton A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn as }

def OmegaRegLangOf (M : Automaton A) (acc : Set M.State) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end Automaton

section RegLangUnion

variable {A I : Type*}

def AutomatonSigma (M : I → Automaton A) : Automaton A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable (M : I → Automaton A)

theorem automaton_sigma_inf_run (as : ℕ → A) (ss : ℕ → Σ i : I, (M i).State) :
    InfRun (AutomatonSigma M) as ss ↔ ∃ i ss_i, InfRun (M i) as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    simp [AutomatonSigma, Automaton.init] at h_init
    rcases h_init with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss : ∀ k, ∃ s_k, ss k = Sigma.mk i s_k := by
      sorry
    sorry
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomatonSigma]
    constructor
    · simp [Automaton.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automaton.next]
      exact h_run.2 k

def AutomatonSum (M0 : Automaton A) (M1 : Automaton A) : Automaton A where
  State := M0.State ⊕ M1.State
  init := inl '' (M0.init) ∪ inr '' (M1.init)
  next := fun s a ↦
    match s with
    | inl s0 => inl '' (M0.next s0 a)
    | inr s1 => inr '' (M1.next s1 a)

variable (M0 : Automaton A) (M1 : Automaton A)

theorem automaton_sum_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (M0.State ⊕ M1.State)) :
    FinRun (AutomatonSum M0 M1) n as ss ↔
      (∃ ss0, FinRun M0 n as ss0 ∧ ss = inl ∘ ss0) ∨
      (∃ ss1, FinRun M1 n as ss1 ∧ ss = inr ∘ ss1) :=
  sorry

theorem automaton_sum_inf_run (as : ℕ → A) (ss : ℕ → (M0.State ⊕ M1.State)) :
    InfRun (AutomatonSum M0 M1) as ss ↔
      (∃ ss0, InfRun M0 as ss0 ∧ ss = inl ∘ ss0) ∨
      (∃ ss1, InfRun M1 as ss1 ∧ ss = inr ∘ ss1) := by
  constructor
  · rintro ⟨h_init, h_next⟩
    simp [Automaton.init, AutomatonSum] at h_init
    rcases h_init with ⟨s0, h_s0_init, h_s0_ss⟩ | ⟨s1, h_s1_init, h_s1_ss⟩
    · left
      have h_run : ∀ i, ∃ si : M0.State, ss i = inl si := by
        intro i ; induction' i with i h_i
        · use s0 ; rw [h_s0_ss]
        rcases h_i with ⟨si, h_si⟩
        have h_next_i := h_next i
        simp [Automaton.next, AutomatonSum, h_si] at h_next_i
        rcases h_next_i with ⟨si', h_si'⟩
        use si'
        rw [h_si'.2]
      choose ss0 h_ss using h_run
      use ss0
      constructor
      · constructor
        · have h_s0 : ss0 0 = s0 := by
            apply inl_injective
            rw [h_s0_ss, ← h_ss 0]
          simp [h_s0] ; assumption
        · intro i
          have h_next_i := h_next i
          simp [h_ss, Automaton.next, AutomatonSum] at h_next_i
          assumption
      · ext i ; simp [h_ss]
    · right
      have h_run : ∀ i, ∃ si : M1.State, ss i = inr si := by
        intro i ; induction' i with i h_i
        · use s1 ; rw [h_s1_ss]
        rcases h_i with ⟨si, h_si⟩
        have h_next_i := h_next i
        simp [Automaton.next, AutomatonSum, h_si] at h_next_i
        rcases h_next_i with ⟨si', h_si'⟩
        use si'
        rw [h_si'.2]
      choose ss1 h_ss using h_run
      use ss1
      constructor
      · constructor
        · have h_s1 : ss1 0 = s1 := by
            apply inr_injective
            rw [h_s1_ss, ← h_ss 0]
          simp [h_s1] ; assumption
        · intro i
          have h_next_i := h_next i
          simp [h_ss, Automaton.next, AutomatonSum] at h_next_i
          assumption
      · ext i ; simp [h_ss]
  · rintro (⟨ss0, h_run, h_ss⟩ | ⟨ss1, h_run, h_ss⟩)
    repeat {
      rw [h_ss]
      constructor
      · simp [Automaton.init, AutomatonSum]
        exact h_run.1
      · intro i
        simp [Automaton.next, AutomatonSum]
        exact h_run.2 i
    }

variable (acc0 : Set M0.State) (acc1 : Set M1.State)

theorem reg_lang_union :
    ∃ M : Automaton A, ∃ acc, RegLangOf M acc = RegLangOf M0 acc0 ∪ RegLangOf M1 acc1 :=
  sorry

theorem omega_reg_lang_union :
    ∃ M : Automaton A, ∃ acc, OmegaRegLangOf M acc = OmegaRegLangOf M0 acc0 ∪ OmegaRegLangOf M1 acc1 :=
  sorry

end RegLangUnion
