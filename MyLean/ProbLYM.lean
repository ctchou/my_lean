
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
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

variable {α : Type*} [Fintype α] [DecidableEq α]

def Perm α := {l : List α // l.Nodup ∧ ∀ a, a ∈ l}

instance fintype_perm : Fintype (Perm α) := by
  sorry

theorem num_perms_all : Fintype.card (Perm α) = (Fintype.card α).factorial := by
  sorry

def hasSetPrefix (s : Finset α) : Finset (Perm α) :=
  {l : Perm α | (List.take s.card l.val).toFinset = s}

theorem num_perms_set_prefix (s : Finset α) :
    (hasSetPrefix s).card = s.card.factorial * (Fintype.card α - s.card).factorial := by
  sorry

--def Perm α := {l : List α // l.length = Fintype.card α ∧ ∀ a, a ∈ l}

instance measurableSpace_perm : MeasurableSpace (Perm α) := ⊤

theorem count_perms_set_prefix (s : Finset α) :
    Measure.count (hasSetPrefix s).toSet = s.card.factorial * (Fintype.card α - s.card).factorial := by
  sorry

theorem prob_set_prefix (s : Finset α) :
    uniformOn Set.univ (hasSetPrefix s).toSet = 1 / (Fintype.card α).choose s.card :=
  sorry

variable (𝓐 : Finset (Finset α))

theorem LYM_inequality (h𝓐 : IsAntichain (· ⊆ ·) (𝓐 : Set (Finset α))) :
    ∑ s in 𝓐, (1 / (Fintype.card α).choose s.card) ≤ 1 := by
  sorry

end
