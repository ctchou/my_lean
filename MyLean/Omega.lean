/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Basic
import Mathlib.Order.Filter.ATTopBot.Basic

open Filter

section Automaton

class Automaton (A : Type*) (S : Type*) where
  init : Set S
  next : S → A → Set S

class DeterministicAutomaton (A : Type*) (S : Type*) extends Automaton A S where
  det_init : init.ncard = 1
  det_next : ∀ s a, (next s a).ncard = 1

def InfiniteOcc {S : Type*} (ss : ℕ → S) : Set S :=
  { s : S | ∃ᶠ i in atTop, ss i = s }

variable {A : Type*} {S : Type*} [Inhabited A] [Inhabited S]

def FiniteRun (M : Automaton A S) (al : List A) (sl : List S) :=
  sl.length = al.length + 1 ∧
  sl[0]! ∈ M.init ∧
  ∀ i < al.length, sl[i + 1]! ∈ M.next sl[i]! al[i]!

def InfiniteRun (M : Automaton A S) (as : ℕ → A) (ss : ℕ → S) :=
  ss 0 ∈ M.init ∧
  ∀ i : ℕ, ss (i + 1) ∈ M.next (ss i) (as i)

def FiniteAccept (M : Automaton A S) (acc : Set S) (al : List A) :=
  ∃ sl : List S, FiniteRun M al sl ∧ sl.getLast! ∈ acc

def BuchiAccept (M : Automaton A S) (acc : Set S) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ InfiniteOcc ss ∩ acc ≠ ∅

def MullerAccept (M : Automaton A S) (accSet : Set (Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∃ acc ∈ accSet, InfiniteOcc ss = acc

def RabinAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∃ pair ∈ accPairs, InfiniteOcc ss ∩ pair.1 ≠ ∅ ∧ InfiniteOcc ss ∩ pair.2 = ∅

def StreettAccept (M : Automaton A S) (accPairs : Set (Set S × Set S)) (as : ℕ → A) :=
  ∃ ss : ℕ → S, InfiniteRun M as ss ∧ ∀ pair ∈ accPairs, InfiniteOcc ss ∩ pair.1 ≠ ∅ → InfiniteOcc ss ∩ pair.2 ≠ ∅

end Automaton
