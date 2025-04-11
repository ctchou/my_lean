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
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.Filter.ATTopBot.Basic

open BigOperators Function Filter Set Sigma

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

section AutomatonSum

variable {A I : Type*}

def AutomatonSum (M : I → Automaton A) : Automaton A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable (M : I → Automaton A)

theorem automaton_sigma_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → Σ i : I, (M i).State) :
    FinRun (AutomatonSum M) n as ss ↔ ∃ i ss_i, FinRun (M i) n as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomatonSum, Automaton.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k : Fin (n + 1), ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k using Fin.induction with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomatonSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automaton.init] at h_init
        simp [AutomatonSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rw [h_eq] at h_s'
        assumption
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomatonSum] at h_next_k
        simp ; assumption
    · ext k <;> rw [h_ss_i k] <;> simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomatonSum]
    constructor
    · simp [Automaton.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automaton.next]
      have h_k := h_run.2 k
      simp at h_k
      exact h_k

theorem automaton_sigma_inf_run (as : ℕ → A) (ss : ℕ → Σ i : I, (M i).State) :
    InfRun (AutomatonSum M) as ss ↔ ∃ i ss_i, InfRun (M i) as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomatonSum, Automaton.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomatonSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automaton.init] at h_init
        simp [AutomatonSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rw [h_eq] at h_s'
        assumption
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomatonSum] at h_next_k
        assumption
    · ext k <;> rw [h_ss_i k] <;> simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomatonSum]
    constructor
    · simp [Automaton.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automaton.next]
      exact h_run.2 k

end AutomatonSum

section RegLangUnion

universe u v w

variable {A I : Type u} (M : I → Automaton.{u, v} A)
variable (acc : (i : I) → Set ((M i).State))

theorem reg_lang_union :
    ∃ M' : Automaton.{u, max u v} A, ∃ acc' : Set (M'.State),
    RegLangOf M' acc' = ⋃ i : I, RegLangOf (M i) (acc i) := by
  use (AutomatonSum M)
  use { s | ∃ i : I, ∃ si ∈ acc i, s = Sigma.mk i si }
  ext al ; simp [RegLangOf, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automaton_sigma_fin_run M n as ss).mp h_run
    use i, n, as
    constructor
    · use ss_i
      constructor
      · assumption
      obtain ⟨i', si', h_si', h_last⟩ := h_acc
      simp [h_ss_i] at h_last
      rw [Sigma.mk.inj_iff] at h_last
      obtain ⟨rfl, h_si'_eq⟩ := h_last
      rw [heq_eq_eq] at h_si'_eq
      rw [h_si'_eq] ; assumption
    · assumption
  · rintro ⟨i, n, as, ⟨ss_i, h_run, h_last⟩, h_al⟩
    use n, as
    constructor
    · use ((Sigma.mk i) ∘ ss_i)
      constructor
      · apply (automaton_sigma_fin_run M n as ((Sigma.mk i) ∘ ss_i)).mpr
        use i, ss_i
      · use i, ss_i (Fin.last n)
        simp ; assumption
    · assumption

theorem omega_reg_lang_union [h : Fintype I] :
    ∃ M' : Automaton.{u, max u v} A, ∃ acc' : Set (M'.State),
    OmegaRegLangOf M' acc' = ⋃ i : I, OmegaRegLangOf (M i) (acc i) := by
  use (AutomatonSum M)
  use { s | ∃ i : I, ∃ si ∈ acc i, s = Sigma.mk i si }
  ext as ; simp [OmegaRegLangOf, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automaton_sigma_inf_run M as ss).mp h_run
    use i, ss_i
    constructor
    · assumption
    · sorry
  · rintro ⟨i, ss_i, h_run_i, h_inf_i⟩
    use ((Sigma.mk i) ∘ ss_i)
    constructor
    · apply (automaton_sigma_inf_run M as ((Sigma.mk i) ∘ ss_i)).mpr
      use i, ss_i
    · sorry

end RegLangUnion
