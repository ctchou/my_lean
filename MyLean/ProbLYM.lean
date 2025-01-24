
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped ENNReal

noncomputable section

variable (α : Type*) [Fintype α] [DecidableEq α]

def Perm := α ≃ Fin (Fintype.card α)

instance : Fintype (Perm α) := Equiv.instFintype

theorem num_perms_all : Fintype.card (Perm α) = (Fintype.card α).factorial := by
  refine Fintype.card_equiv (Fintype.equivFinOfCardEq rfl)

def hasSetPrefix (s : Finset α) : Finset (Perm α) :=
  { p : Perm α | ∀ a ∈ s, p.toFun a ≤ s.card }

theorem num_perms_set_prefix (s : Finset α) :
    (hasSetPrefix α s).card = s.card.factorial * (Fintype.card α - s.card).factorial := by
--    Fintype.card { p : Perm α // p ∈ hasSetPrefix α s } = s.card.factorial * (Fintype.card α - s.card).factorial := by
  sorry

instance : MeasurableSpace (Perm α) := ⊤
instance : MeasurableSingletonClass (Perm α) := ⟨fun _ => trivial⟩

theorem count_perms_set_prefix (s : Finset α) :
    count (hasSetPrefix α s).toSet = ↑(s.card.factorial * (Fintype.card α - s.card).factorial) := by
  rw [← num_perms_set_prefix α s, count_apply_finset]

/-- The following proof is due to Aaron Liu. -/
lemma aux_1 {k m n : ℕ} (hn : 0 < n) (heq : k * m = n) :
    (↑ m : ENNReal) / (↑ n : ENNReal) = 1 / (↑ k : ENNReal) := by
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
  rw [uniformOn_univ, count_perms_set_prefix, num_perms_all]
  apply aux_1 (Nat.factorial_pos (Fintype.card α))
  rw [← mul_assoc]
  exact Nat.choose_mul_factorial_mul_factorial (Finset.card_le_univ s)

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s in 𝓐, (1 / (Fintype.card α).choose s.card) ≤ 1 := by
  sorry

end
