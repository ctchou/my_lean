
import Mathlib.Data.Set.Card
import Mathlib.Data.Sigma.Basic

universe u v w

class C where
  T : Type*
  s : Set T

variable (I : Type*) (F : I → C) (foo : (i : I) → Set ((F i).T)) in
#check (⋃ i : I, Sigma.mk i '' (foo i))

def C_sigma {I : Type*} (F : I → C) : C where
  T := Σ i : I, (F i).T
  s := ⋃ i : I, Sigma.mk i '' (F i).s

example (I : Type u) (F : I → C.{u}) :
    ∃ G : C.{u}, G = G := by
  use (C_sigma F)
  sorry

example (I : Type*) (F : I → C) (i : I) (x : (F i).T)
    (h : ⟨i, x⟩ ∈ ⋃ i, Sigma.mk i '' (F i).s) : x ∈ (F i).s := by
  simp only [Set.mem_iUnion, Set.mem_image, Sigma.mk.injEq] at h -- from simp?
  obtain ⟨i, x, hx, rfl, h⟩ := h
  rw [heq_eq_eq] at h
  cases h
  assumption

example (I : Type*) (F : I → C) (i : I) (x : (F i).T)
    (h : ⟨i, x⟩ ∈ Set.univ.sigma (fun i ↦ (F i).s)) : x ∈ (F i).s := by
  simp [Set.mk_sigma_iff] at h
  assumption

variable (I : Type*) (F : I → C)
#check Σ i : I, (F i).T
#check (i : I) × (F i).T

variable (x : Σ i : I, (F i).T)
#check (x : (i : I) × (F i).T)

variable (x : (i : I) × (F i).T)
#check (x : Σ i : I, (F i).T)

variable (i : I) (x : (F i).T)
#check (Set.univ.sigma (fun i ↦ (F i).s))
