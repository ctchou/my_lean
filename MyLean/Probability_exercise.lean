
-- This file is copied from https://github.com/PatrickMassot/GlimpseOfLean/pull/13

import Mathlib.Probability.Notation
import Mathlib.Data.ENNReal.Operations

lemma ENNReal.mul_self_eq_self_iff (a : ENNReal) : a * a = a ↔ a = 0 ∨ a = 1 ∨ a = ⊤ := by
  by_cases h : a = 0
  · simp [h]
  by_cases h' : a = ⊤
  · simp [h']
  simp only [h, h', or_false, false_or]
  constructor
  · intro h''
    nth_rw 3 [← one_mul a] at h''
    exact (ENNReal.mul_eq_mul_right h h').mp h''
  · intro h''
    simp [h'']

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
noncomputable section
open scoped ENNReal
/-

# Probability measures, independent sets

We introduce a probability space and events (measurable sets) on that space. We then define
independence of events and conditional probability, and prove results relating those two notions.

Mathlib has a (different) definition for independence of sets and also has a conditional measure
given a set. Here we practice instead on simple new definitions to apply the tactics introduced in
the previous files.
-/

/- We open namespaces. The effect is that after that command, we can call lemmas in those namespaces
without their namespace prefix: for example, we can write `inter_comm` instead of `Set.inter_comm`.
Hover over `open` if you want to learn more. -/
open MeasureTheory ProbabilityTheory Set

/- We define a measure space `Ω`: the `MeasureSpace Ω` variable states that `Ω` is a measurable
space on which there is a canonical measure `volume`, with notation `ℙ`.
We then state that `ℙ` is a probability measure. That is, `ℙ univ = 1`, where `univ : Set Ω` is the
universal set in `Ω` (the set that contains all `x : Ω`). -/
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- `A, B` will denote sets in `Ω`.
variable {A B : Set Ω}

/- One can take the measure of a set `A`: `ℙ A : ℝ≥0∞`.
`ℝ≥0∞`, or `ENNReal`, is the type of extended non-negative real numbers, which contain `∞`.
Measures can in general take infinite values, but since our `ℙ` is a probability measure,
it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top`
or `measure_lt_top` to prove that `ℙ A ≠ ∞` or `ℙ A < ∞`.

Hint: use `#check measure_ne_top` to see what that lemma does.

The operations on `ENNReal` are not as nicely behaved as on `ℝ`: `ENNReal` is not a ring and
subtraction truncates to zero for example. If you find that lemma `lemma_name` used to transform
an equation does not apply to `ENNReal`, try to find a lemma named something like
`ENNReal.lemma_name_of_something` and use that instead. -/

/-
⊢ ∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : Measure α) [inst : IsFiniteMeasure μ] (s : Set α), μ s ≠ ⊤
-/
#check measure_ne_top
/-
⊢ ∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : Measure α) [inst : IsFiniteMeasure μ] (s : Set α), μ s < ⊤
-/
#check measure_lt_top

/-- Two sets `A, B` are independent for the ambient probability measure `ℙ` if
`ℙ (A ∩ B) = ℙ A * ℙ B`. -/
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

/-- If `A` is independent of `B`, then `B` is independent of `A`. -/
lemma IndepSet.symm : IndepSet A B → IndepSet B A := by {
--  sorry
  unfold IndepSet
  intro h
  rw [inter_comm, mul_comm]
  assumption
}

/- Many lemmas in measure theory require sets to be measurable (`MeasurableSet A`).
If you are presented with a goal like `⊢ MeasurableSet (A ∩ B)`, try the `measurability` tactic.
That tactic produces measurability proofs. -/

-- Hints: `compl_eq_univ_diff`, `measure_diff`, `inter_univ`, `measure_compl`, `ENNReal.mul_sub`

/-
MeasureTheory.measure_compl.{u_1} {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {s : Set α}
  (h₁ : MeasurableSet s) (h_fin : μ s ≠ ⊤) : μ sᶜ = μ univ - μ s
-/
#check measure_compl
/-
⊢ ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {s₁ s₂ : Set α},
  s₂ ⊆ s₁ → NullMeasurableSet s₂ μ → μ s₂ ≠ ⊤ → μ (s₁ \ s₂) = μ s₁ - μ s₂
-/
#check measure_diff

lemma IndepSet.compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by {
--  sorry
  unfold IndepSet
  intro h0
  have h1 : A ∩ Bᶜ = A \ (A ∩ B) := by ext x ; simp
  have h2 : ℙ (A \ (A ∩ B)) = ℙ A - ℙ (A ∩ B) := by
    refine measure_diff inter_subset_left ?_ (measure_ne_top ℙ (A ∩ B))
    apply MeasurableSet.nullMeasurableSet
    exact MeasurableSet.inter hA hB
  have h3 : ℙ Bᶜ = 1 - ℙ B := by
    exact prob_compl_eq_one_sub hB
  have h4 : ℙ A * (1 - ℙ B) = ℙ A * 1 - ℙ A * ℙ B := by
    apply ENNReal.mul_sub
    intro ; intro
    exact measure_ne_top ℙ A
  rw [h1, h2, h3, h0, h4, mul_one]
}

-- Use what you have proved so far
lemma IndepSet.compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B) :
    IndepSet Aᶜ B := by {
--  sorry
  apply IndepSet.symm
  apply IndepSet.compl_right hB hA
  exact IndepSet.symm h
}

-- Hint: `ENNReal.mul_self_eq_self_iff`

/-
⊢ ∀ (a : ℝ≥0∞), a * a = a ↔ a = 0 ∨ a = 1 ∨ a = ⊤
-/
#check ENNReal.mul_self_eq_self_iff

lemma indep_self (h : IndepSet A A) : ℙ A = 0 ∨ ℙ A = 1 := by {
--  sorry
  rw [IndepSet, inter_self] at h
  rcases (ENNReal.mul_self_eq_self_iff (ℙ A)).mp h.symm with h1 | h2 | h3
  . simp [h1]
  . simp [h2]
  . have := measure_ne_top ℙ A
    contradiction
}

/-

### Conditional probability

-/

/-- The probability of set `A` conditioned on `B`. -/
def condProb (A B : Set Ω) : ENNReal := ℙ (A ∩ B) / ℙ B

/- We define a notation for `condProb A B` that makes it look more like paper math. -/
notation3 "ℙ("A"|"B")" => condProb A B

/- Now that we have defined `condProb`, we want to use it, but Lean knows nothing about it.
We could start every proof with `rw [condProb]`, but it is more convenient to write lemmas about the
properties of `condProb` first and then use those. -/

-- Hint : `measure_inter_null_of_null_left`
@[simp] -- this makes the lemma usable by `simp`
lemma condProb_zero_left (A B : Set Ω) (hA : ℙ A = 0) : ℙ(A|B) = 0 := by {
  sorry
}

@[simp]
lemma condProb_zero_right (A B : Set Ω) (hB : ℙ B = 0) : ℙ(A|B) = 0 := by {
  sorry
}

/- What other basic lemmas could be useful? Are there other "special" sets for which `condProb`
takes known values? -/

-- Your lemma(s) here

/- The next statement is a `theorem` and not a `lemma`, because we think it is important.
There is no functional difference between those two keywords. -/

/-- **Bayes Theorem** -/
theorem bayesTheorem (hA : ℙ A ≠ 0) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by {
  sorry
}

-- Did you really need all those hypotheses?

theorem bayesTheorem' (A B : Set Ω) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by {
  sorry
}

lemma condProb_of_indepSet (h : IndepSet B A) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A := by {
  sorry
}
