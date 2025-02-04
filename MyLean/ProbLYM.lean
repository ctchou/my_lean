/-
Copyright (c) 2024-present Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option linter.unusedSectionVars false

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators Fintype Finset Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

variable (α : Type*) [Fintype α] [DecidableEq α]

abbrev PreNumbering := α → Fin (card α + 1)

def initSeg (n : ℕ) : Finset (Fin (card α + 1)) := { i | i < n }

def setNumbering (s : Finset α) : Finset (PreNumbering α) :=
  { f | BijOn f s (initSeg α s.card) ∧ ∀ a ∈ sᶜ, (f a : ℕ) = 0 }

lemma set_numbering_empty : setNumbering α ∅ = {fun _ ↦ 0} := by
  apply Finset.ext ; intro f
  simp [setNumbering, initSeg]
  constructor <;> intro h
  · ext a ; simp [h]
  · intro a ; simp [h]

def setNumberingLast (s : Finset α) (a : α) : Finset (PreNumbering α) :=
  { f ∈ setNumbering α s | f a = s.card - 1 }

--  { f ∈ setNumbering α s | ∃ f' ∈ setNumbering α (s \ {a}), f = appendNumbering α f' (s \ {a}) a }

lemma set_numbering_last_card {s : Finset α} :
    ∀ a ∈ s, (setNumberingLast α s a).card = (setNumbering α (s \ {a})).card := by
  sorry

lemma set_numbering_last_disj {s : Finset α} {n : ℕ} (h : s.card = n + 1) :
    ∀ a ∈ s, ∀ a' ∈ s, a ≠ a' → Disjoint (setNumberingLast α s a) (setNumberingLast α s a') := by
  intro a h_as a' h_a's h_aa'
  apply Finset.disjoint_left.mpr
  intro f h_fa h_fa'
  simp [setNumberingLast, setNumbering, h] at h_fa h_fa'
  rcases h_fa with ⟨⟨h_fs, _⟩, h_fn⟩
  rcases h_fa' with ⟨_, h_fn'⟩
  rw [← h_fn'] at h_fn
  have := (InjOn.eq_iff (BijOn.injOn h_fs) h_as h_a's ).mp h_fn
  contradiction

example (s : Finset α) (n : ℕ) (h : s.card = n + 1) : ↑n < Fin.last (Fintype.card α) := by
  have h1 := Finset.card_le_univ s
  simp [h] at h1
  have h2 : n % (Fintype.card α + 1) = n := by
    apply Nat.mod_eq_of_lt
    linarith
  apply Fin.lt_def.mpr
  simp [Fin.val_last, h2]
  linarith

lemma set_numbering_union {s : Finset α} {n : ℕ} (h : s.card = n + 1) :
    setNumbering α s = (s.biUnion (setNumberingLast α s)) := by
  apply Finset.ext ; intro f
  simp [setNumberingLast]
  constructor
  · intro h_fs
    have h_surj : SurjOn f s (initSeg α s.card) := by
      simp [setNumbering] at h_fs
      exact BijOn.surjOn h_fs.1
    rw [SurjOn] at h_surj
    have h_iseg : ↑(s.card - 1) ∈ (initSeg α s.card) := by
      simp [initSeg, h, Fin.val_last]
      have h1 := Finset.card_le_univ s
      simp [h] at h1
      have h2 : n % (Fintype.card α + 1) = n := by
        apply Nat.mod_eq_of_lt
        linarith
      apply Fin.lt_def.mpr
      simp [Fin.val_last, h2]
      linarith
    have h_last := h_surj h_iseg
    simp at h_last
    rcases h_last with ⟨a, h_as, h_fa⟩
    use a
    simp [h_as, h_fs, h_fa, h]
  · rintro ⟨a, h_as, h_fs, _⟩
    exact h_fs

theorem set_numbering_card (s : Finset α) :
    (setNumbering α s).card = s.card.factorial := by
  generalize h : s.card = n
  induction' n with n ih generalizing s
  · rw [Finset.card_eq_zero] at h
    simp [h]
    apply Finset.card_eq_one.mpr
    use (fun _ ↦ 0)
    exact set_numbering_empty α
  have ih' : ∀ a ∈ s, (setNumbering α (s \ {a})).card = n.factorial := by
    intro a h_mem
    have h_diff := Finset.card_sdiff (Finset.singleton_subset_iff.mpr h_mem)
    simp [h] at h_diff
    exact ih (s \ {a}) h_diff
  simp [set_numbering_union α h, card_biUnion (set_numbering_last_disj α h),
        Finset.sum_congr (rfl : s = s) (set_numbering_last_card α),
        Finset.sum_congr (rfl : s = s) ih',
        Finset.sum_const n.factorial, h, Nat.factorial_succ]

-- def appendNumbering (f : PreNumbering α) (s : Finset α) (a : α) : PreNumbering α :=
--   fun a' ↦ if a' ∈ s then f a' else
--            if a' = a then s.card else 0

-- lemma append_numbering_closure {f : PreNumbering α} {s : Finset α} {a : α}
--     (hf : f ∈ setNumbering α s) (ha : ¬ a ∈ s) : appendNumbering α f s a ∈ setNumbering α (s ∪ {a}) := by
--   simp [setNumbering]
--   constructor
--   · have : initSeg α (s ∪ {a}) = insert s.card (initSeg α s) := by
--       sorry

--     sorry
--   . intro a' h_a's h_a'a
--     simp [appendNumbering, h_a's, h_a'a]

/-- **************************************************************************************************** -/

def Numbering := α ≃ Fin (card α)

instance : Fintype (Numbering α) := Equiv.instFintype

theorem numbering_card : card (Numbering α) = (card α).factorial := by
  exact Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

def setPrefix (s : Finset α) : Finset (Numbering α) :=
  { p : Numbering α | ∀ a : α, a ∈ s ↔ p.toFun a < s.card }

theorem set_prefix_subset {s t : Finset α} {p : Numbering α} (h_s : p ∈ setPrefix α s) (h_t : p ∈ setPrefix α t)
    (h_st : s.card ≤ t.card) : s ⊆ t := by
  intro a h_as
  simp [setPrefix] at h_s h_t
  exact (h_t a).mpr (lt_of_le_of_lt' h_st ((h_s a).mp h_as))

theorem set_prefix_card (s : Finset α) :
    (setPrefix α s).card = s.card.factorial * (card α - s.card).factorial := by
  sorry

instance : MeasurableSpace (Numbering α) := ⊤
instance : MeasurableSingletonClass (Numbering α) := ⟨fun _ => trivial⟩

lemma set_prefix_count (s : Finset α) :
    count (setPrefix α s).toSet = ↑(s.card.factorial * (card α - s.card).factorial) := by
  rw [← set_prefix_card α s, count_apply_finset]

lemma aux_1 {k m n : ℕ} (hn : 0 < n) (heq : k * m = n) :
    (↑ m : ENNReal) / (↑ n : ENNReal) = 1 / (↑ k : ENNReal) := by
  -- The following proof is due to Aaron Liu.
  subst heq
  have hm : m ≠ 0 := by rintro rfl ; simp at hn
  have hk : k ≠ 0 := by rintro rfl ; simp at hn
  refine (ENNReal.toReal_eq_toReal ?_ ?_).mp ?_
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hm, hk] at h
  · intro h
    apply_fun ENNReal.toReal at h
    simp [hk] at h
  · field_simp
    ring

theorem set_prefix_prob (s : Finset α) :
    uniformOn Set.univ (setPrefix α s).toSet = 1 / (card α).choose s.card := by
  rw [uniformOn_univ, set_prefix_count, numbering_card]
  apply aux_1 (Nat.factorial_pos (card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

theorem set_prefix_disj {s t : Finset α} (h_st : ¬ s ⊆ t) (h_ts : ¬ t ⊆ s) :
    Disjoint (setPrefix α s).toSet (setPrefix α t).toSet := by
  refine Set.disjoint_iff.mpr ?_
  intro p
  simp only [mem_inter_iff, Finset.mem_coe, mem_empty_iff_false, imp_false, not_and]
  intro h_s h_t
  rcases Nat.le_total s.card t.card with h_st' | h_ts'
  · exact h_st (set_prefix_subset α h_s h_t h_st')
  · exact h_ts (set_prefix_subset α h_t h_s h_ts')

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s in 𝓐, ((1 : ℝ) / (card α).choose s.card) ≤ 1 := by
  sorry

end
