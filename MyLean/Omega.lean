/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic

section Automaton

class Automaton (α : Type*) (σ : Type*) [Fintype α] [Fintype σ] where
  init : Finset σ
  next : σ → α → Finset σ

class DeterministicAutomaton (α : Type*) (σ : Type*) [Fintype α] [Fintype σ] extends Automaton α σ where
  det_init : init.card = 1
  det_next : ∀ s a, (next s a).card = 1

variable {α : Type*} {σ : Type*} [Fintype α] [Fintype σ] [Inhabited α] [Inhabited σ]

def FiniteRun (A : Automaton α σ) (al : List α) (sl : List σ) :=
  sl.length = al.length + 1 ∧
  sl[0]! ∈ A.init ∧
  ∀ i < al.length, sl[i + 1]! ∈ A.next sl[i]! al[i]!

def InfiniteRun (A : Automaton α σ) (as : ℕ → α) (ss : ℕ → σ) :=
  ss 0 ∈ A.init ∧
  ∀ i : ℕ, ss (i + 1) ∈ A.next (ss i) (as i)

def FiniteAccept (A : Automaton α σ) (acc : Finset σ) (al : List α) :=
  ∃ sl : List σ, FiniteRun A al sl ∧ sl.getLast! ∈ acc

end Automaton
