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
  { x : X | ∃ᶠ i in atTop, xs i = x }

theorem inf_occ_index {X : Type*} {xs : ℕ → X} {x : X}
    (h : x ∈ InfOcc xs) : ∃ k, xs k = x := by
  exact Frequently.exists h

theorem inf_occ_map {X Y : Type*} {xs : ℕ → X} {x : X} {f : X → Y}
    (h : x ∈ InfOcc xs) : f x ∈ InfOcc (f ∘ xs) := by
  let p k := xs k = x
  let q k := (f ∘ xs) k = f x
  have hpq : ∀ k, p k → q k := by
    simp [p, q] ; intro k h_p ; rw [h_p]
  exact Frequently.mono h hpq

theorem inf_occ_map_rev {X Y : Type*} {xs : ℕ → X} {x : X} (f : X → Y)
    (hi : f.Injective) (h : f x ∈ InfOcc (f ∘ xs)) : (x ∈ InfOcc xs) := by
  let p k := (f ∘ xs) k = f x
  let q k := xs k = x
  have hpq : ∀ k, p k → q k := by
    simp [p, q] ; intro k h_p ; exact hi h_p
  exact Frequently.mono h hpq

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

def AcceptedLang (M : Automaton A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn as }

def AcceptedOmegaLang (M : Automaton A) (acc : Set M.State) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end Automaton

section AutomatonSum

variable {I A : Type*}

def AutomatonSum (M : I → Automaton A) : Automaton A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable (M : I → Automaton A)

theorem automaton_sum_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (AutomatonSum M).State) :
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
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomatonSum] at h_next_k
        simpa
    · ext k ; rw [h_ss_i k] ; simp
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

theorem automaton_sum_inf_run (as : ℕ → A) (ss : ℕ → (AutomatonSum M).State) :
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
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomatonSum] at h_next_k
        assumption
    · ext k ; rw [h_ss_i k] ; simp
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

section AcceptedLangUnion

universe u v w

variable {I : Type u} {A : Type v} (M : I → Automaton.{v, w} A)
variable (acc : (i : I) → Set ((M i).State))

theorem accepted_lang_union :
    ∃ M' : Automaton.{v, max u w} A, ∃ acc' : Set (M'.State),
    AcceptedLang M' acc' = ⋃ i : I, AcceptedLang (M i) (acc i) := by
  use (AutomatonSum M), (⋃ i : I, Sigma.mk i '' acc i)
  ext al ; simp [AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automaton_sum_fin_run M n as ss).mp h_run
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
      simpa [← h_si'_eq]
    · assumption
  · rintro ⟨i, n, as, ⟨ss_i, h_run, h_last⟩, h_al⟩
    use n, as
    constructor
    · use ((Sigma.mk i) ∘ ss_i)
      constructor
      · apply (automaton_sum_fin_run M n as ((Sigma.mk i) ∘ ss_i)).mpr
        use i, ss_i
      · use i, ss_i (Fin.last n)
        simpa
    · assumption

theorem accepted_omega_lang_union :
    ∃ M' : Automaton.{v, max u w} A, ∃ acc' : Set (M'.State),
    AcceptedOmegaLang M' acc' = ⋃ i : I, AcceptedOmegaLang (M i) (acc i) := by
  use (AutomatonSum M), (⋃ i : I, Sigma.mk i '' acc i)
  ext as ; simp [AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (automaton_sum_inf_run M as ss).mp h_run
    use i, ss_i
    constructor
    · assumption
    · obtain ⟨s, h_s⟩ := nonempty_iff_ne_empty.mpr h_inf
      simp [h_ss_i] at h_s
      obtain ⟨h_s_inf, i', si', h_si'_acc, h_si'_s⟩ := h_s
      have ⟨k, h_k⟩ := inf_occ_index h_s_inf
      simp [← h_k] at h_si'_s
      rw [Sigma.mk.inj_iff] at h_si'_s
      obtain ⟨rfl, h_si'_eq⟩ := h_si'_s
      rw [heq_eq_eq] at h_si'_eq
      apply nonempty_iff_ne_empty.mp
      use si' ; simp
      constructor
      · rw [← h_k, comp_apply, ← h_si'_eq] at h_s_inf
        apply inf_occ_map_rev (Sigma.mk i') sigma_mk_injective
        assumption
      . assumption
  · rintro ⟨i, ss_i, h_run_i, h_inf_i⟩
    use ((Sigma.mk i) ∘ ss_i)
    constructor
    · apply (automaton_sum_inf_run M as ((Sigma.mk i) ∘ ss_i)).mpr
      use i, ss_i
    · obtain ⟨si, h_si_inf, h_si_acc⟩ := nonempty_iff_ne_empty.mpr h_inf_i
      apply nonempty_iff_ne_empty.mp
      use ⟨i, si⟩ ; simp
      constructor
      · apply inf_occ_map ; assumption
      · use i, si

end  AcceptedLangUnion

section AutomatonProd

variable {I A : Type*}

def AutomatonProd (M : I → Automaton A) : Automaton A where
  State := Π i : I, (M i).State
  init := { s | ∀ i : I, (s i) ∈ (M i).init }
  next := fun s a ↦ { s' | ∀ i : I, (s' i) ∈ (M i).next (s i) a }

variable (M : I → Automaton A)

theorem automaton_prod_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (AutomatonProd M).State) :
    FinRun (AutomatonProd M) n as ss ↔ ∀ i, FinRun (M i) n as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ;  exact (h_all i).2 k

theorem automaton_prod_inf_run (as : ℕ → A) (ss : ℕ → (AutomatonProd M).State) :
    InfRun (AutomatonProd M) as ss ↔ ∀ i, InfRun (M i) as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ; exact (h_all i).2 k

end AutomatonProd

section AcceptedLangInter

universe u v w

variable {I : Type u} {A : Type v} (M : I → Automaton.{v, w} A)
variable (acc : (i : I) → Set ((M i).State))

theorem accepted_lang_inter :
    ∃ M' : Automaton.{v, max u w} A, ∃ acc' : Set (M'.State),
    AcceptedLang M' acc' = ⋂ i : I, AcceptedLang (M i) (acc i) := by
  use (AutomatonProd M), { s | ∀ i, (s i) ∈ (acc i) }
  ext al ; simp [AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ i
    use n, as ; simp [h_al]
    use (fun k ↦ ss k i)
    constructor
    · exact (automaton_prod_fin_run M n as ss).mp h_run i
    · exact h_acc i
  · intro h_all
    have h_all' : ∀ i, ∃ ss_i, FinRun (M i) al.length (fun k ↦ al[k]) ss_i ∧ ss_i (Fin.last al.length) ∈ acc i := by
      intro i
      obtain ⟨n, as, ⟨ss_i, h_run_i, h_acc_i⟩, h_al⟩ := h_all i
      have h_n : n = al.length := by rw [h_al, List.length_ofFn]
      obtain rfl := h_n
      use ss_i
      constructor
      · have h_as : (fun k ↦ al[k]) = as := by
          ext k
          calc al[k] = (List.ofFn as)[k] := by congr
                   _ = as k := by simp
        rw [h_as] ; assumption
      · assumption
    use al.length, (fun k ↦ al[k])
    simp
    choose ss_i h_ss_i using h_all'
    use (fun k i ↦ ss_i i k)
    constructor
    · apply (automaton_prod_fin_run M al.length (fun k ↦ al[k]) (fun k i ↦ ss_i i k)).mpr
      intro i
      exact (h_ss_i i).1
    · intro i
      exact (h_ss_i i).2

end AcceptedLangInter

section AutomatonHist

variable {A H : Type*}

def AutomatonHist (M : Automaton A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : Automaton A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }

variable (M : Automaton A) (hist_init : Set H) (hist_next : M.State × H → A → Set H)

theorem automaton_hist_inf_run_proj (as : ℕ → A) (ss : ℕ → M.State × H) :
    InfRun (AutomatonHist M hist_init hist_next) as ss → InfRun M as (Prod.fst ∘ ss) := by
  intro h ; constructor
  · have h' := h.1
    simp [AutomatonHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp [AutomatonHist] at h'
    exact h'.1

private def gen_hist (as : ℕ → A) (ss : ℕ → M.State) (hs0 : H) (hs' : M.State × H → A -> H) : ℕ → H
  | 0 => hs0
  | k + 1 => hs' (ss k, gen_hist as ss hs0 hs' k) (as k)

theorem automaton_hist_inf_run_exists (as : ℕ → A) (ss : ℕ → M.State)
    (h_init : Nonempty hist_init) (h_next : ∀ s a, (hist_next s a).Nonempty) :
    InfRun M as ss → ∃ hs : ℕ → H, InfRun (AutomatonHist M hist_init hist_next) as (fun k ↦ (ss k, hs k)) := by
  intro h
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := gen_hist M as ss hs0 hs'
  use hs ; constructor
  · simp [AutomatonHist, gen_hist, h.1, hs]
    exact h_hs0
  · intro k
    simp [AutomatonHist, gen_hist, hs, h.2 k]
    apply h_hs'

end AutomatonHist
