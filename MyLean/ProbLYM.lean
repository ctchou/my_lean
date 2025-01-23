
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Probability.UniformOn

--set_option diagnostics true
--set_option diagnostics.threshold 10

open BigOperators Set ProbabilityTheory MeasureTheory
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
    count (hasSetPrefix α s).toSet = s.card.factorial * (Fintype.card α - s.card).factorial := by
  sorry

theorem prob_set_prefix (s : Finset α) :
    uniformOn Set.univ (hasSetPrefix α s).toSet = 1 / (Fintype.card α).choose s.card :=
  sorry

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s in 𝓐, (1 / (Fintype.card α).choose s.card) ≤ 1 := by
  sorry

end
