
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators Finset Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

variable (α : Type*) [Fintype α] [DecidableEq α]

def Numbering := α ≃ Fin (Fintype.card α)

instance : Fintype (Numbering α) := Equiv.instFintype

theorem card_numbering : Fintype.card (Numbering α) = (Fintype.card α).factorial := by
  exact Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

def hasSetPrefix (s : Finset α) : Finset (Numbering α) :=
  { p : Numbering α | ∀ a : α, a ∈ s ↔ p.toFun a < s.card }
--  { p : Numbering α | ∀ a : α, a ∈ s ↔ p.toFun a ∈ { i : Fin (Fintype.card α) | i < s.card } }

theorem set_prefix_subset {s t : Finset α} {p : Numbering α} (h_s : p ∈ hasSetPrefix α s) (h_t : p ∈ hasSetPrefix α t)
    (h_st : s.card ≤ t.card) : s ⊆ t := by
  intro a h_as
  simp [hasSetPrefix] at h_s h_t
  exact (h_t a).mpr (lt_of_le_of_lt' h_st ((h_s a).mp h_as))

theorem card_set_prefix (s : Finset α) :
    (hasSetPrefix α s).card = s.card.factorial * (Fintype.card α - s.card).factorial := by
--    Fintype.card { p : Numbering α // p ∈ hasSetPrefix α s } = s.card.factorial * (Fintype.card α - s.card).factorial := by
  sorry

instance : MeasurableSpace (Numbering α) := ⊤
instance : MeasurableSingletonClass (Numbering α) := ⟨fun _ => trivial⟩

lemma count_set_prefix (s : Finset α) :
    count (hasSetPrefix α s).toSet = ↑(s.card.factorial * (Fintype.card α - s.card).factorial) := by
  rw [← card_set_prefix α s, count_apply_finset]

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

theorem prob_set_prefix (s : Finset α) :
    uniformOn Set.univ (hasSetPrefix α s).toSet = 1 / (Fintype.card α).choose s.card := by
  rw [uniformOn_univ, count_set_prefix, card_numbering]
  apply aux_1 (Nat.factorial_pos (Fintype.card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

theorem disj_set_prefix {s t : Finset α} (h_st : ¬ s ⊆ t) (h_ts : ¬ t ⊆ s) :
    Disjoint (hasSetPrefix α s).toSet (hasSetPrefix α t).toSet := by
  refine Set.disjoint_iff.mpr ?_
  intro p
  simp only [mem_inter_iff, mem_coe, mem_empty_iff_false, imp_false, not_and]
  intro h_s h_t
  rcases Nat.le_total s.card t.card with h_st' | h_ts'
  · exact h_st (set_prefix_subset α h_s h_t h_st')
  · exact h_ts (set_prefix_subset α h_t h_s h_ts')

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s in 𝓐, ((1 : ℝ) / (Fintype.card α).choose s.card) ≤ 1 := by
  sorry
