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

def InfOcc {X : Type*} (xs : ℕ → X) : Set X :=
  { x : X | ∃ᶠ k in atTop, xs k = x }

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

theorem inf_occ_inter_nonempty {X : Type*} (xs : ℕ → X) (s : Set X) :
    InfOcc xs ∩ s ≠ ∅ ↔ ∃ᶠ k in atTop, xs k ∈ s := by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x, h_inf, h_s⟩
    simp [InfOcc] at h_inf
    let p k := xs k = x
    let q k := xs k ∈ s
    have h_p : ∃ᶠ k in atTop, p k := by assumption
    have h_imp : ∀ k, p k → q k := by simp [p, q] ; intro k h ; simpa [h]
    exact Frequently.mono h_p h_imp
  . sorry

end Sequence

section Automaton

class Automaton (A : Type*) where
  State : Type*
  init : Set State
  next : State → A → Set State

variable {A : Type*}

def IsFinite (M : Automaton A) : Prop := Finite A ∧ Finite M.State

def Deterministic (M : Automaton A) : Prop :=
  M.init.ncard = 1 ∧ ∀ s a, (M.next s a).ncard = 1

def FinRun (M : Automaton A) (n : ℕ) (as : Fin n → A) (ss : Fin (n + 1) → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : Fin n, ss (k + 1) ∈ M.next (ss k) (as k)

def InfRun (M : Automaton A) (as : ℕ → A) (ss : ℕ → M.State) :=
  ss 0 ∈ M.init ∧ ∀ k : ℕ, ss (k + 1) ∈ M.next (ss k) (as k)

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

variable {I A : Type*} (M : I → Automaton A) (acc : (i : I) → Set ((M i).State))

def AutomatonSum_Acc : Set (AutomatonSum M).State := ⋃ i : I, Sigma.mk i '' acc i

theorem accepted_lang_union :
    AcceptedLang (AutomatonSum M) (AutomatonSum_Acc M acc) = ⋃ i : I, AcceptedLang (M i) (acc i) := by
  ext al ; simp [AutomatonSum_Acc, AcceptedLang, FinAccept]
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
    AcceptedOmegaLang (AutomatonSum M) (AutomatonSum_Acc M acc) = ⋃ i : I, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AutomatonSum_Acc, AcceptedOmegaLang, BuchiAccept]
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

variable {I A : Type*} (M : I → Automaton A) (acc : (i : I) → Set ((M i).State))

def AutomatonProd_Acc : Set (AutomatonProd M).State := { s | ∀ i, (s i) ∈ (acc i) }

theorem accepted_lang_inter :
    AcceptedLang (AutomatonProd M) (AutomatonProd_Acc M acc) = ⋂ i : I, AcceptedLang (M i) (acc i) := by
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

theorem automaton_hist_inf_run_proj {as : ℕ → A} {ss : ℕ → M.State × H}
    (h : InfRun (AutomatonHist M hist_init hist_next) as ss) : InfRun M as (Prod.fst ∘ ss) := by
  constructor
  · have h' := h.1
    simp [AutomatonHist] at h'
    exact h'.1
  · intro k
    have h' := h.2 k
    simp [AutomatonHist] at h'
    exact h'.1

private def _MakeHist (as : ℕ → A) (ss : ℕ → M.State) (hs0 : H) (hs' : M.State × H → A -> H) : ℕ → H
  | 0 => hs0
  | k + 1 => hs' (ss k, _MakeHist as ss hs0 hs' k) (as k)

theorem automaton_hist_inf_run_exists {as : ℕ → A} {ss : ℕ → M.State}
    (h_init : hist_init.Nonempty) (h_next : ∀ s a, (hist_next s a).Nonempty)
    (h : InfRun M as ss) : ∃ hs : ℕ → H, InfRun (AutomatonHist M hist_init hist_next) as (fun k ↦ (ss k, hs k)) := by
  obtain ⟨hs0, h_hs0⟩ := h_init
  choose hs' h_hs' using h_next
  let hs := _MakeHist M as ss hs0 hs'
  use hs ; constructor
  · simp [AutomatonHist, _MakeHist, h.1, hs]
    exact h_hs0
  · intro k
    simp [AutomatonHist, _MakeHist, hs, h.2 k]
    apply h_hs'

end AutomatonHist

section AcceptedOmegaLangInter2

open Classical

variable {A : Type*} (M : Fin 2 → Automaton A) (acc : (i : Fin 2) → Set ((M i).State))

def AutomatonInter2_HistInit : Set (Fin 2) := {1}

def AutomatonInter2_HistNext : (AutomatonProd M).State × Fin 2 → A → Set (Fin 2) :=
  fun (s, h) _ ↦
    if s 0 ∈ acc 0 ∧ h = 0 then {1} else
    if s 1 ∈ acc 1 ∧ h = 1 then {0} else {h}

def AutomatonInter2 : Automaton A :=
  AutomatonHist (AutomatonProd M) AutomatonInter2_HistInit (AutomatonInter2_HistNext M acc)

def AutomatonInter2_Acc : Set (AutomatonInter2 M acc).State :=
  { (s, h) | (s 0 ∈ acc 0 ∧ h = 0) ∨ (s 1 ∈ acc 1 ∧ h = 1) }

private lemma automaton_inter2_inf_occ {as : ℕ → A} {ss : ℕ → (AutomatonInter2 M acc).State}
    (h_inf : InfRun (AutomatonInter2 M acc) as ss) :
    (InfOcc (fun k ↦ (Prod.fst ∘ ss) k 0)) ∩ (acc 0) ≠ ∅ ↔ (InfOcc (fun k ↦ (Prod.fst ∘ ss) k 1)) ∩ (acc 1) ≠ ∅ := by
  sorry

theorem accepted_omega_lang_inter2 :
    AcceptedOmegaLang (AutomatonInter2 M acc) (AutomatonInter2_Acc M acc) = ⋂ i : Fin 2, AcceptedOmegaLang (M i) (acc i) := by
  ext as ; simp [AcceptedOmegaLang, BuchiAccept]
  constructor
  · rintro ⟨ss, h_run, h_inf⟩ i
    have h_run1 := automaton_hist_inf_run_proj (AutomatonProd M) AutomatonInter2_HistInit (AutomatonInter2_HistNext M acc) h_run
    have h_run2 := (automaton_prod_inf_run M as (Prod.fst ∘ ss)).mp h_run1 i
    use (fun k ↦ (Prod.fst ∘ ss) k i) ; constructor
    · assumption
    /-
    case h.right
    A : Type u_1
    M : Fin 2 → Automaton A
    acc : (i : Fin 2) → Set (Automaton.State A)
    as : ℕ → A
    ss : ℕ → Automaton.State A
    h_run : InfRun (AutomatonInter2 M acc) as ss
    h_inf : ¬InfOcc ss ∩ AutomatonInter2_Acc M acc = ∅
    i : Fin 2
    h_run1 : InfRun (AutomatonProd M) as (Prod.fst ∘ ss)
    h_run2 : InfRun (M i) as fun k ↦ (Prod.fst ∘ ss) k i
    ⊢ ¬(InfOcc fun k ↦ (Prod.fst ∘ ss) k i) ∩ acc i = ∅
    -/
    sorry
  · intro h_all
    choose ss h_ss using h_all
    let ss2 := fun k i ↦ ss i k
    have h_ss2 : ∀ i, InfRun (M i) as (fun k ↦ ss2 k i) := by intro i ; exact (h_ss i).1
    have h_run2 := (automaton_prod_inf_run M as ss2).mpr h_ss2
    have h_hist_init : AutomatonInter2_HistInit.Nonempty := by simp [AutomatonInter2_HistInit]
    have h_hist_next : ∀ s a, (AutomatonInter2_HistNext M acc s a).Nonempty := by
      intro s a ; simp only [AutomatonInter2_HistNext]
      rcases Classical.em (s.1 0 ∈ acc 0 ∧ s.2 = 0) with cond1 | cond1 <;> simp [cond1]
      rcases Classical.em (s.1 1 ∈ acc 1 ∧ s.2 = 1) with cond2 | cond2 <;> simp [cond2]
    have h_runh := automaton_hist_inf_run_exists (AutomatonProd M) AutomatonInter2_HistInit (AutomatonInter2_HistNext M acc)
      h_hist_init h_hist_next h_run2
    obtain ⟨hs, h_run⟩ := h_runh
    use (fun k ↦ (ss2 k, hs k))
    constructor
    · assumption
    /-
    case h.right
    A : Type u_1
    M : Fin 2 → Automaton A
    acc : (i : Fin 2) → Set (Automaton.State A)
    as : ℕ → A
    ss : (i : Fin 2) → ℕ → Automaton.State A
    h_ss : ∀ (i : Fin 2), InfRun (M i) as (ss i) ∧ ¬InfOcc (ss i) ∩ acc i = ∅
    ss2 : ℕ → (i : Fin 2) → Automaton.State A := fun k i ↦ ss i k
    h_ss2 : ∀ (i : Fin 2), InfRun (M i) as fun k ↦ ss2 k i
    h_run2 : InfRun (AutomatonProd M) as ss2
    h_hist_init : AutomatonInter2_HistInit.Nonempty
    h_hist_next : ∀ (s : Automaton.State A × Fin 2) (a : A), (AutomatonInter2_HistNext M acc s a).Nonempty
    hs : ℕ → Fin 2
    h_run : InfRun (AutomatonHist (AutomatonProd M) AutomatonInter2_HistInit (AutomatonInter2_HistNext M acc)) as fun k ↦
      (ss2 k, hs k)
    ⊢ ¬(InfOcc fun k ↦ (ss2 k, hs k)) ∩ AutomatonInter2_Acc M acc = ∅
    -/
    sorry

end AcceptedOmegaLangInter2
