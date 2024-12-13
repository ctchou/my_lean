
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Batteries.Tactic.Instances

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option warningAsError false

open Set Filter Real MeasureTheory

noncomputable section

theorem ShiftPreservesMeasurable {s : Set ℝ} (h : MeasurableSet s) (c : ℝ) : MeasurableSet (image (fun x ↦ x + c) s) := by
  apply (MeasurableEmbedding.measurableSet_image ?_).mpr h
  exact measurableEmbedding_addRight c

theorem ShiftPreservesVolume (s : Set ℝ) (c : ℝ) : volume (image (fun x ↦ x + c) s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

theorem VolumeOfCountableUnion [Countable ι] {f : ι → Set ℝ}
    (hdis : Pairwise (Disjoint on f)) (hmea : ∀ (i : ι), MeasurableSet (f i)) :
    volume (⋃ i, f i) = ∑' i, volume (f i) :=
  measure_iUnion hdis hmea

theorem VolumeMono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

instance vSetoid : Setoid { x : ℝ // x ∈ Icc 0 1 } where
  r := fun x y ↦ (↑ x : ℝ) - (↑ y) ∈ range ((↑) : ℚ → ℝ)
  iseqv := {
    refl := by
      intro x
      simp only [sub_self, mem_range, Rat.cast_eq_zero, exists_eq]
    symm := by
      intro x y
      simp only [mem_range]
      rintro ⟨t, h⟩
      use (-t)
      simp [h]
    trans := by
      intro x y z
      simp only [mem_range]
      rintro ⟨t1, h1⟩
      rintro ⟨t2, h2⟩
      use (t1 + t2)
      simp [h1, h2]
  }

def vT : Type := Quotient vSetoid

theorem vSurj : ∀ t : vT, ∃ x : { x : ℝ // x ∈ Icc 0 1 }, ⟦x⟧ = t := by
  intro t
  have ⟨x, eq⟩ := Quotient.mk_surjective t
  use x, eq

def vRep : vT → { x : ℝ // x ∈ Icc 0 1 } :=
  fun t ↦ Classical.choose (vSurj t)

theorem vRepSpec : ∀ t : vT, ⟦vRep t⟧ = t :=
  fun t ↦ Classical.choose_spec (vSurj t)

def VitaliSet : Set ℝ := { x : ℝ | ∃ t : vT, ↑(vRep t) = x }

def vVitaliSet (c : ℝ) : Set ℝ := image (fun x ↦ x + c) VitaliSet

def vI : Type := { i : ℝ // i ∈ Icc (-1) 1 ∩ range ((↑) : ℚ → ℝ) }



end

/- ================================================================================================= -/

noncomputable section

#check Classical.choose
#check Classical.choose_spec

example : MeasurableSpace ℝ := by infer_instance

#check (volume : Measure ℝ)

/- ================================================================================================= -/

variable {α : Type*} [MeasurableSpace α]

example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

variable {ι : Type*} [Encodable ι]

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h

variable {μ : Measure α}

example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl

/- ================================================================================================= -/

end
