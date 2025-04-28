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

universe u v w

section Sequence

def AppendInf {X : Type*} (xl : List X) (xs : ℕ → X) : ℕ → X :=
  fun k ↦ if h : k < xl.length then xl[k] else xs (k - xl.length)

def Step {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → xs (k + 1) ∈ q

def LeadsTo {X : Type*} (xs : ℕ → X) (p q : Set X) : Prop :=
  ∀ k, xs k ∈ p → ∃ k' ≥ k, xs k' ∈ q

variable {X : Type*} {xs : ℕ → X}

theorem leads_to_step {p q : Set X}
    (h : Step xs p q) : LeadsTo xs p q := by
  intro k h_p
  use (k + 1) ; constructor
  · omega
  · exact h k h_p

theorem leads_to_trans {p q r : Set X}
    (h1 : LeadsTo xs p q) (h2 : LeadsTo xs q r) : LeadsTo xs p r := by
  intro k h_p
  obtain ⟨k', h_k', h_q⟩ := h1 k h_p
  obtain ⟨k'', h_k'', h_r⟩ := h2 k' h_q
  use k'' ; constructor
  · omega
  · assumption

theorem leads_to_cases {p q r s : Set X}
    (h1 : LeadsTo xs (p ∩ q) r) (h2 : LeadsTo xs (p ∩ qᶜ) s) : LeadsTo xs p (r ∪ s) := by
  intro k h_p
  rcases Classical.em (xs k ∈ q) with h_q | h_not_q
  · let h_pq : xs k ∈ p ∩ q := by tauto
    obtain ⟨k', h_k', h_r⟩ := h1 k h_pq
    use k' ; simp [h_k', h_r]
  . let h_pq : xs k ∈ p ∩ qᶜ := by tauto
    obtain ⟨k', h_k', h_s⟩ := h2 k h_pq
    use k' ; simp [h_k', h_s]

theorem leads_to_until_frequently_1 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∉ p) : LeadsTo xs p q := by
  intro k h_p
  by_contra! h_q
  have h_p' : ∀ k' ≥ k, xs k' ∈ p := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · assumption
    have h_pq_n : xs (k + n) ∈ p ∩ qᶜ := by
      have h_q_n := h_q (k + n) (by omega)
      simp [h_q_n]
      exact h_ind (k + n) (rfl)
    exact h1 (k + n) h_pq_n
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_not_p⟩ := h2 k
  have := h_p' k' h_k'
  contradiction

theorem leads_to_until_frequently_2 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∈ q) : LeadsTo xs p (p ∩ q) := by
  intro k h_p
  by_contra! h_not_pq
  have h_p_not_q : ∀ k' ≥ k, xs k' ∈ p ∩ qᶜ := by
    intro k' h_k'
    simp [le_iff_exists_add] at h_k'
    obtain ⟨n, h_k'⟩ := h_k'
    revert k' h_k'
    induction' n with n h_ind <;> intro k' h_k' <;> simp [h_k']
    · have h_not_pq' := h_not_pq k (by omega)
      tauto
    have h_n := h_ind (k + n) (rfl)
    have h_n_p := h1 (k + n) h_n
    have h_n_q := h_not_pq (k + n + 1) (by omega)
    simp [h_n_p] at h_n_q
    simp [← add_assoc] ; tauto
  rw [frequently_atTop] at h2
  obtain ⟨k', h_k', h_q'⟩ := h2 k
  have := (h_p_not_q k' h_k').2
  contradiction

theorem frequently_leads_to_frequently {p q : Set X}
    (h1 : ∃ᶠ k in atTop, xs k ∈ p) (h2 : LeadsTo xs p q) : ∃ᶠ k in atTop, xs k ∈ q := by
  rw [frequently_atTop] at h1 ⊢
  intro k0
  obtain ⟨k1, h_k1, h_k1_p⟩ := h1 k0
  obtain ⟨k2, h_k2, h_k2_q⟩ := h2 k1 h_k1_p
  use k2 ; constructor
  · omega
  · assumption

end Sequence

section Automata

class Automata (A : Type*) where
  State : Type*
  init : Set State
  next : State → A → Set State

variable {A : Type*}

def IsFinite (M : Automata A) : Prop := Finite A ∧ Finite M.State

def Deterministic (M : Automata A) : Prop :=
  M.init.ncard = 1 ∧ ∀ s a, (M.next s a).ncard = 1

def FinRun (M : Automata A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss (k + 1) ∈ M.next (ss k) (as k)

def InfRun (M : Automata A) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)

def FinAccept (M : Automata A) (acc : Set M.State) (n : ℕ) (as : Fin n → A) :=
  ∃ ss : Fin (n + 1) → M.State, FinRun M n as ss ∧ ss n ∈ acc

def BuchiAccept (M : Automata A) (acc : Set M.State) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ᶠ k in atTop, ss k ∈ acc

def MullerAccept (M : Automata A) (accSet : Set (Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ acc ∈ accSet, ∀ s, s ∈ acc ↔ (∃ᶠ k in atTop, ss k = s)

def RabinAccept (M : Automata A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∃ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) ∧ (∀ᶠ k in atTop, ss k ∉ pair.2)

def StreettAccept (M : Automata A) (accPairs : Set (Set M.State × Set M.State)) (as : ℕ → A) :=
  ∃ ss : ℕ → M.State, InfRun M as ss ∧ ∀ pair ∈ accPairs, (∃ᶠ k in atTop, ss k ∈ pair.1) → (∃ᶠ k in atTop, ss k ∈ pair.2)

def AcceptedLang (M : Automata A) (acc : Set M.State) : Set (List A) :=
  { al | ∃ n as, FinAccept M acc n as ∧ al = List.ofFn as }

def AcceptedOmegaLang (M : Automata A) (acc : Set M.State) : Set (ℕ → A) :=
  { as | BuchiAccept M acc as }

end Automata

section AutomataSum

variable {I A : Type*}

def AutomataSum (M : I → Automata A) : Automata A where
  State := Σ i : I, (M i).State
  init := ⋃ i : I, Sigma.mk i '' (M i).init
  next := fun ⟨i, s⟩ a ↦ Sigma.mk i '' (M i).next s a

variable (M : I → Automata A)

theorem Automata_sum_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (AutomataSum M).State) :
    FinRun (AutomataSum M) n as ss ↔ ∃ i ss_i, FinRun (M i) n as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomataSum, Automata.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k : Fin (n + 1), ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k using Fin.induction with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomataSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automata.init] at h_init
        simp [AutomataSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomataSum] at h_next_k
        simpa
    · ext k ; rw [h_ss_i k] ; simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomataSum]
    constructor
    · simp [Automata.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automata.next]
      have h_k := h_run.2 k
      simp at h_k
      exact h_k

theorem Automata_sum_inf_run (as : ℕ → A) (ss : ℕ → (AutomataSum M).State) :
    InfRun (AutomataSum M) as ss ↔ ∃ i ss_i, InfRun (M i) as ss_i ∧ ss = (Sigma.mk i) ∘ ss_i := by
  constructor
  · rintro ⟨h_init, h_next⟩
    have := h_init
    simp [AutomataSum, Automata.init] at this
    rcases this with ⟨i, s0, h_s0_init, h_s0_ss⟩
    have h_ss_exists : ∀ k, ∃ sk : (M i).State, ss k = Sigma.mk i sk := by
      intro k ; induction' k with k h_k
      · use s0 ; rw [h_s0_ss]
      rcases h_k with ⟨sk, h_sk⟩
      have h_next_k := h_next k
      simp [AutomataSum, h_sk] at h_next_k
      rcases h_next_k with ⟨sk', h_sk'⟩
      use sk' ; simp [h_sk'.2]
    choose ss_i h_ss_i using h_ss_exists
    use i, ss_i
    constructor
    · constructor
      · rw [h_ss_i 0, Automata.init] at h_init
        simp [AutomataSum] at h_init
        obtain ⟨i, s', h_s', rfl, h_eq⟩ := h_init
        rw [heq_eq_eq] at h_eq
        rwa [h_eq] at h_s'
      · intro k
        have h_next_k := h_next k
        rw [h_ss_i k, h_ss_i (k + 1)] at h_next_k
        simp [AutomataSum] at h_next_k
        assumption
    · ext k ; rw [h_ss_i k] ; simp
  · rintro ⟨i, ss_i, h_run, h_ss⟩
    simp [h_ss, AutomataSum]
    constructor
    · simp [Automata.init]
      use i, (ss_i 0)
      simp ; exact h_run.1
    · intro k
      simp [Automata.next]
      exact h_run.2 k

end AutomataSum

section AcceptedLangUnion

variable {I A : Type*} (M : I → Automata A) (acc : (i : I) → Set ((M i).State))

def AutomataSum_Acc : Set (AutomataSum M).State := ⋃ i : I, Sigma.mk i '' acc i

theorem accepted_lang_union :
    AcceptedLang (AutomataSum M) (AutomataSum_Acc M acc) = ⋃ i : I, AcceptedLang (M i) (acc i) := by
  ext al ; simp [AutomataSum_Acc, AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (Automata_sum_fin_run M n as ss).mp h_run
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
      · apply (Automata_sum_fin_run M n as ((Sigma.mk i) ∘ ss_i)).mpr
        use i, ss_i
      · use i, ss_i (Fin.last n)
        simpa
    · assumption

theorem accepted_omega_lang_union :
    AcceptedOmegaLang (AutomataSum M) (AutomataSum_Acc M acc) = ⋃ i : I, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AutomataSum_Acc, AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨i, ss_i, h_run_i, h_ss_i⟩ := (Automata_sum_inf_run M as ss).mp h_run
    use i, ss_i
    constructor
    · assumption
    · let p k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ss k
      let q k := ss_i k ∈ acc i
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        rintro k ⟨i', si', h_si'_acc, h_si'_ss⟩
        simp [h_ss_i] at h_si'_ss
        rw [Sigma.mk.inj_iff] at h_si'_ss
        obtain ⟨rfl, h_si'_eq⟩ := h_si'_ss
        rw [heq_eq_eq] at h_si'_eq
        simpa [q, ← h_si'_eq]
      exact Frequently.mono h_p h_pq
  · rintro ⟨i, ss_i, h_run_i, h_inf_i⟩
    use ((Sigma.mk i) ∘ ss_i)
    constructor
    · apply (Automata_sum_inf_run M as ((Sigma.mk i) ∘ ss_i)).mpr
      use i, ss_i
    · let p k := ss_i k ∈ acc i
      let q k := ∃ i', ∃ si' ∈ acc i', ⟨i', si'⟩ = ((Sigma.mk i ∘ ss_i) k : (AutomataSum M).State)
      have h_p : ∃ᶠ k in atTop, p k := by assumption
      have h_pq : ∀ k, p k → q k := by
        simp [p, q] ; intro k h
        use i, (ss_i k)
      exact Frequently.mono h_p h_pq

end  AcceptedLangUnion

section AutomataProd

variable {I A : Type*}

def AutomataProd (M : I → Automata A) : Automata A where
  State := Π i : I, (M i).State
  init := { s | ∀ i : I, (s i) ∈ (M i).init }
  next := fun s a ↦ { s' | ∀ i : I, (s' i) ∈ (M i).next (s i) a }

variable (M : I → Automata A)

theorem Automata_prod_fin_run (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → (AutomataProd M).State) :
    FinRun (AutomataProd M) n as ss ↔ ∀ i, FinRun (M i) n as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ;  exact (h_all i).2 k

theorem Automata_prod_inf_run (as : ℕ → A) (ss : ℕ → (AutomataProd M).State) :
    InfRun (AutomataProd M) as ss ↔ ∀ i, InfRun (M i) as (fun k ↦ ss k i) := by
  constructor
  · rintro ⟨h_init, h_next⟩ i
    constructor
    · apply h_init
    · intro k ; apply h_next
  · intro h_all
    constructor
    · intro i ; exact (h_all i).1
    · intro k i ; exact (h_all i).2 k

end AutomataProd

section AcceptedLangInter

variable {I A : Type*} (M : I → Automata A) (acc : (i : I) → Set ((M i).State))

def AutomataProd_Acc : Set (AutomataProd M).State := { s | ∀ i, (s i) ∈ (acc i) }

theorem accepted_lang_inter :
    AcceptedLang (AutomataProd M) (AutomataProd_Acc M acc) = ⋂ i : I, AcceptedLang (M i) (acc i) := by
  ext al ; simp [AcceptedLang, FinAccept]
  constructor
  · rintro ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ i
    use n, as ; simp [h_al]
    use (fun k ↦ ss k i)
    constructor
    · exact (Automata_prod_fin_run M n as ss).mp h_run i
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
    · apply (Automata_prod_fin_run M al.length (fun k ↦ al[k]) (fun k i ↦ ss_i i k)).mpr
      intro i
      exact (h_ss_i i).1
    · intro i
      exact (h_ss_i i).2

end AcceptedLangInter

section AutomataHist

variable {A H : Type*}

def AutomataHist (M : Automata A) (hist_init : Set H) (hist_next : M.State × H → A → Set H) : Automata A where
  State := M.State × H
  init := { s | s.1 ∈ M.init ∧ s.2 ∈ hist_init }
  next := fun s a ↦ { s' | s'.1 ∈ M.next s.1 a ∧ s'.2 ∈ hist_next s a }

variable (M : Automata A) (hist_init : Set H) (hist_next : M.State × H → A → Set H)

theorem Automata_hist_inf_run_proj {as : ℕ → A} {ss : ℕ → M.State × H}
    (h : InfRun (AutomataHist M hist_init hist_next) as ss) : InfRun M as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp [AutomataHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp [AutomataHist] at h'
    exact h'.1

private def _MakeHist (as : ℕ → A) (ss : ℕ → M.State) (hs0 : H) (hs' : M.State × H → A -> H) : ℕ → H
  | 0 => hs0
  | k + 1 => hs' (ss k, _MakeHist as ss hs0 hs' k) (as k)

theorem Automata_hist_inf_run_exists {as : ℕ → A} {ss : ℕ → M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : InfRun M as ss) : ∃ hs : ℕ → H, InfRun (AutomataHist M hist_init hist_next) as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := _MakeHist M as ss hs0 hs'
  use hs ; constructor
  · simp [AutomataHist, _MakeHist, h.1, hs]
    exact h_hs0
  · intro k
    simp [AutomataHist, _MakeHist, hs, h.2 k]
    apply h_hs'

end AutomataHist

section AcceptedOmegaLangInter2

open Classical

variable {A : Type*} (M : Fin 2 → Automata A) (acc : (i : Fin 2) → Set ((M i).State))

def AutomataOmegaInter2_HistInit : Set (Fin 2) := {0}

def AutomataOmegaInter2_HistNext : (AutomataProd M).State × Fin 2 → A → Set (Fin 2) :=
  fun s _ ↦
    if s.1 0 ∈ acc 0 ∧ s.2 = 0 then {1} else
    if s.1 1 ∈ acc 1 ∧ s.2 = 1 then {0} else {s.2}

def AutomataOmegaInter2 : Automata A :=
  AutomataHist (AutomataProd M) AutomataOmegaInter2_HistInit (AutomataOmegaInter2_HistNext M acc)

def AutomataOmegaInter2_Acc : Set (AutomataOmegaInter2 M acc).State :=
  { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }

private lemma Automata_inter2_lemma1 {as : ℕ → A} {ss : ℕ → (AutomataOmegaInter2 M acc).State}
    (h_run : InfRun (AutomataOmegaInter2 M acc) as ss) :
      (∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 }) ↔
      (∃ᶠ k in atTop, ss k ∈ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }) := by
  constructor <;> intro h_inf
  · suffices h_lt : LeadsTo ss {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} by
      exact frequently_leads_to_frequently h_inf h_lt
    have h_lt1 : LeadsTo ss {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} {s | s.2 = 1} := by
      apply leads_to_step ; simp [Step]
      intro k h_acc h_hist
      have h_step := (h_run.2 k).2
      simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
      assumption
    have h_lt2 : LeadsTo ss {s | s.2 = 1} {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} := by
      apply leads_to_until_frequently_1
      · simp [Step]
        intro k h_hist h_acc
        rw [imp_not_comm] at h_acc
        have h_acc := h_acc h_hist
        have h_step := (h_run.2 k).2
        simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
        assumption
      · let p k := ss k ∈ {s | s.1 0 ∈ acc 0 ∧ s.2 = 0}
        let q k := ss k ∉ {s | s.2 = 1}
        have h_imp : ∀ k, p k → q k := by
          intro k ; simp [p, q]
          intro _ h ; simp [h]
        exact Frequently.mono h_inf h_imp
    exact leads_to_trans h_lt1 h_lt2
  · suffices h_lt : LeadsTo ss {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} by
      exact frequently_leads_to_frequently h_inf h_lt
    have h_lt1 : LeadsTo ss {s | s.1 1 ∈ acc 1 ∧ s.2 = 1} {s | s.2 = 0} := by
      apply leads_to_step ; simp [Step]
      intro k h_acc h_hist
      have h_step := (h_run.2 k).2
      simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
      assumption
    have h_lt2 : LeadsTo ss {s | s.2 = 0} {s | s.1 0 ∈ acc 0 ∧ s.2 = 0} := by
      apply leads_to_until_frequently_1
      · simp [Step]
        intro k h_hist h_acc
        rw [imp_not_comm] at h_acc
        have h_acc := h_acc h_hist
        have h_step := (h_run.2 k).2
        simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
        assumption
      · let p k := ss k ∈ {s | s.1 1 ∈ acc 1 ∧ s.2 = 1}
        let q k := ss k ∉ {s | s.2 = 0}
        have h_imp : ∀ k, p k → q k := by
          intro k ; simp [p, q]
          intro _ h ; simp [h]
        exact Frequently.mono h_inf h_imp
    exact leads_to_trans h_lt1 h_lt2

private lemma Automata_inter2_lemma2 {as : ℕ → A} {ss : ℕ → (AutomataOmegaInter2 M acc).State}
    (h_run : InfRun (AutomataOmegaInter2 M acc) as ss)
    (h_inf0 : ∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 })
    (h_inf1 : ∃ᶠ k in atTop, ss k ∈ { s | s.1 1 ∈ acc 1 }) :
      ∃ᶠ k in atTop, ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 } ∪ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 } := by
  have h_true : ∃ᶠ k in atTop, ss k ∈ univ := by simp [atTop_neBot]
  apply frequently_leads_to_frequently h_true
  apply leads_to_cases (p := univ) (q := {s | s.2 = 0}) <;> simp [univ_inter]
  · have h_inter : {s : (AutomataOmegaInter2 M acc).State | s.1 0 ∈ acc 0 ∧ s.2 = 0} = {s | s.2 = 0} ∩ {s | s.1 0 ∈ acc 0} := by
      ext s ; simp ; tauto
    rw [h_inter]
    apply leads_to_until_frequently_2 (h2 := h_inf0)
    simp [Step]
    intro k h_hist h_acc
    have h_step := (h_run.2 k).2
    simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
    assumption
  · have h_inter : {s : (AutomataOmegaInter2 M acc).State | s.1 1 ∈ acc 1 ∧ s.2 = 1} = {s | s.2 = 1} ∩ {s | s.1 1 ∈ acc 1} := by
      ext s ; simp ; tauto
    have h_compl : {s : (AutomataOmegaInter2 M acc).State | s.2 = 0}ᶜ = {s | s.2 = 1} := by
      ext s ; simp
      constructor
      · exact Fin.eq_one_of_neq_zero s.2
      . intro h ; simp [h]
    rw [h_inter, h_compl]
    apply leads_to_until_frequently_2 (h2 := h_inf1)
    simp [Step]
    intro k h_hist h_acc
    have h_step := (h_run.2 k).2
    simp [AutomataOmegaInter2_HistNext, h_acc, h_hist] at h_step
    assumption

theorem accepted_omega_lang_inter2 :
    AcceptedOmegaLang (AutomataOmegaInter2 M acc) (AutomataOmegaInter2_Acc M acc) = ⋂ i : Fin 2, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩ i
    have h_run1 := Automata_hist_inf_run_proj (AutomataProd M) AutomataOmegaInter2_HistInit (AutomataOmegaInter2_HistNext M acc) h_run
    have h_run' := (Automata_prod_inf_run M as (Prod.fst ∘ ss)).mp h_run1 i
    use (fun k ↦ (Prod.fst ∘ ss) k i) ; constructor
    · assumption
    let p0 k := ss k ∈ { s | s.1 0 ∈ acc 0 ∧ s.2 = 0 }
    let p1 k := ss k ∈ { s | s.1 1 ∈ acc 1 ∧ s.2 = 1 }
    have h_inf_or : ∃ᶠ k in atTop, p0 k ∨ p1 k := by exact h_inf
    rw [frequently_or_distrib] at h_inf_or
    let p0' k := (Prod.fst ∘ ss) k 0 ∈ acc 0
    let p1' k := (Prod.fst ∘ ss) k 1 ∈ acc 1
    have h_p0_p0' : ∀ k, p0 k → p0' k := by intro k ; simp [p0, p0'] ; tauto
    have h_p1_p1' : ∀ k, p1 k → p1' k := by intro k ; simp [p1, p1'] ; tauto
    revert i ; rw [Fin.forall_fin_two]
    constructor <;> intro h_run_i
    · rcases h_inf_or with h_inf0 | h_inf1
      · exact Frequently.mono h_inf0 h_p0_p0'
      · rw [← Automata_inter2_lemma1 M acc h_run] at h_inf1
        exact Frequently.mono h_inf1 h_p0_p0'
    · rcases h_inf_or with h_inf0 | h_inf1
      · rw [Automata_inter2_lemma1 M acc h_run] at h_inf0
        exact Frequently.mono h_inf0 h_p1_p1'
      · exact Frequently.mono h_inf1 h_p1_p1'
  · intro h_all
    choose ss h_ss using h_all
    let ss' := fun k i ↦ ss i k
    have h_ss' : ∀ i, InfRun (M i) as (fun k ↦ ss' k i) := by intro i ; exact (h_ss i).1
    have h_run' := (Automata_prod_inf_run M as ss').mpr h_ss'
    have h_hist_init : AutomataOmegaInter2_HistInit.Nonempty := by simp [AutomataOmegaInter2_HistInit]
    have h_hist_next : ∀ s a, (AutomataOmegaInter2_HistNext M acc s a).Nonempty := by
      intro s a ; simp only [AutomataOmegaInter2_HistNext]
      rcases Classical.em (s.1 0 ∈ acc 0 ∧ s.2 = 0) with cond1 | cond1 <;> simp [cond1]
      rcases Classical.em (s.1 1 ∈ acc 1 ∧ s.2 = 1) with cond2 | cond2 <;> simp [cond2]
    have h_runh := Automata_hist_inf_run_exists (AutomataProd M) AutomataOmegaInter2_HistInit (AutomataOmegaInter2_HistNext M acc)
      h_hist_init h_hist_next h_run'
    obtain ⟨hs, h_run⟩ := h_runh
    use (fun k ↦ (ss' k, hs k))
    constructor
    · assumption
    have h_inf0 : ∃ᶠ k in atTop, ss' k ∈ { s | s 0 ∈ acc 0 } := by simp [ss', (h_ss 0).2]
    have h_inf1 : ∃ᶠ k in atTop, ss' k ∈ { s | s 1 ∈ acc 1 } := by simp [ss', (h_ss 1).2]
    exact Automata_inter2_lemma2 M acc h_run h_inf0 h_inf1

end AcceptedOmegaLangInter2
