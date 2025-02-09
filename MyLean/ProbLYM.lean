/-
Copyright (c) 2024-present Ching-Tsun Chou and Chris Wong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou and Chris Wong
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

section

@[reducible]
def Numbering (α : Type*) [Fintype α] := α ≃ Fin (card α)

@[reducible]
def NumberingOn (s : Finset α) := {x // x ∈ s} ≃ Fin s.card

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsPrefix (s : Finset α) (f : Numbering α) :=
  ∀ x, x ∈ s ↔ f x < s.card

def is_prefix_equiv {s : Finset α} : {f // IsPrefix s f} ≃ NumberingOn s × NumberingOn sᶜ where
  toFun := fun ⟨f, hf⟩ ↦
    ({
      toFun := fun ⟨x, hx⟩ ↦ ⟨f x, by rwa [← hf x]⟩
      invFun := fun ⟨n, hn⟩ ↦ ⟨f.symm ⟨n, by have := s.card_le_univ; omega⟩, by rw [hf]; simpa⟩
      left_inv := by rintro ⟨x, hx⟩; simp
      right_inv := by rintro ⟨n, hn⟩; simp
    },
    {
      toFun := fun ⟨x, hx⟩ ↦ ⟨f x - s.card, by
        rw [s.mem_compl, hf] at hx
        rw [s.card_compl]
        exact Nat.sub_lt_sub_right (by omega) (by omega)
      ⟩
      invFun := fun ⟨n, hn⟩ ↦ ⟨f.symm ⟨n + s.card, by rw [s.card_compl] at hn; omega⟩, by rw [s.mem_compl, hf]; simp⟩
      left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl, hf, not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      right_inv := by rintro ⟨n, hn⟩; simp
    })
  invFun := fun (g, g') ↦ ⟨
    {
      toFun := fun x ↦
        if hx : x ∈ s then
          g ⟨x, hx⟩ |>.castLE s.card_le_univ
        else
          g' ⟨x, by simpa⟩ |>.addNat s.card |>.cast (by simp)
      invFun := fun ⟨n, hn⟩ ↦
        if hn' : n < s.card then
          g.symm ⟨n, hn'⟩
        else
          g'.symm ⟨n - s.card, by rw [s.card_compl]; omega⟩
      left_inv := by intro x; by_cases hx : x ∈ s <;> simp [hx]
      right_inv := by
        rintro ⟨n, hn⟩
        by_cases hn' : n < s.card
        · simp [hn']
        · simp [hn']
          split_ifs
          · rename_i h
            have : ∀ x, ↑(g'.symm x) ∉ s := by
              intro x
              simp only [← Finset.mem_compl, Finset.coe_mem]
            exact this _ h |>.elim
          · simp [Nat.sub_add_cancel (not_lt.mp hn')]
    },
    by
      intro x
      constructor
      · intro hx
        simp [hx]
      · by_cases hx : x ∈ s <;> simp [hx]
  ⟩
  left_inv := by
    rintro ⟨f, hf⟩
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · rw [hf, not_lt] at hx
      simp [hx]
  right_inv := by
    rintro ⟨g, g'⟩
    simp
    constructor
    · ext x
      simp
    · ext x
      rcases x with ⟨x, hx⟩
      rw [Finset.mem_compl] at hx
      simp [hx]

theorem is_prefix_card {s : Finset α} {f : Numbering α} {hf : IsPrefix s f} :
    card (NumberingOn s × NumberingOn sᶜ) = s.card.factorial * (card α - s.card).factorial := by
  have (hn, hn') := is_prefix_equiv ⟨f, hf⟩
  simp only [NumberingOn, Fintype.card_prod]
  rw [Fintype.card_equiv hn, Fintype.card_equiv hn']
  simp

end
