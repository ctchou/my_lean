
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

open BigOperators Fintype Set MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

variable (α : Type*) [Fintype α] [DecidableEq α]

def initSeg (n : ℕ) : Finset (Fin (card α + 1)) := { i | i < n }

def setNumbering (s : Finset α) : Finset (α → Fin (card α + 1)) :=
  { f | BijOn f s (initSeg α s.card) ∧ ∀ a ∈ sᶜ, (f a : ℕ) = 0 }

lemma set_numbering_empty : setNumbering α ∅ = {fun _ ↦ 0} := by
  apply Finset.ext
  intro f
  simp [setNumbering, initSeg]
  constructor <;> intro h
  · ext a
    simp [h]
  · intro a
    simp [h]

def subSetNumbering (s : Finset α) (a : α) : Finset (α → Fin (card α + 1)) :=
  { f | ∃ f' ∈ setNumbering α (s \ {a}), EqOn f f' (s \ {a}) ∧ f a = s.card - 1 ∧ ∀ a ∈ sᶜ, (f a : ℕ) = 0 }

--  (setNumbering α (s \ {a})).biUnion (fun f' ↦ { f | EqOn f f' (s \ {a}) ∧ f a = s.card - 1 ∧ ∀ a ∈ sᶜ, (f a : ℕ) = 0 })

-- lemma set_numbering_succ (s : Finset α) {n : ℕ} (h : s.card = n + 1) :
--     setNumbering α s =

theorem set_numbering_card (s : Finset α) :
    (setNumbering α s).card = s.card.factorial := by
  generalize h : s.card = n
  induction' n with n ih generalizing s
  · rw [Finset.card_eq_zero] at h
    simp [h]
    apply Finset.card_eq_one.mpr
    use (fun _ ↦ 0)
    exact set_numbering_empty α
  /-
  case succ
  α : Type u_1
  inst✝¹ : Fintype α
  inst✝ : DecidableEq α
  n : ℕ
  ih : ∀ (s : Finset α), s.card = n → (setNumbering α s).card = n.factorial
  s : Finset α
  h : s.card = n + 1
  ⊢ (setNumbering α s).card = (n + 1).factorial
  -/

  sorry

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
