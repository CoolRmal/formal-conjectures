/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.ForMathlib.Combinatorics.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order

/-!
# Sidon sets

This file proves some lemmas related to Sidon sets.

-/

open Function Filter Finset Nat
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

namespace IsSidon

/-- Suppose `A` is a finite set. Then `A` is Sidon iff `(A + A).card = (A.card + 1).choose 2`. -/
theorem isSidon_iff_add_card (A : Finset ℕ) :
    IsSidon A ↔ (A + A).card = (A.card + 1).choose 2 where
  mp hA := by
    have hs := Fintype.card_congr (Sym2.sortEquiv (α := A))
    simp only [Sym2.card, Fintype.card_coe] at hs
    have ha := Fintype.card_coe (α := A × A) {s | s.1 ≤ s.2}
    simp only [mem_filter, mem_univ, true_and] at ha
    have h_card_eq : image (fun (p : A × A) => p.1.1 + p.2.1) {s | s.1 ≤ s.2} = A + A := by
      ext; simp [Finset.mem_add]; grind
    refine Eq.trans ?_ (hs.trans ha).symm
    rw [← h_card_eq, Finset.card_image_of_injOn]
    · intro p hp q hq hf
      have := hA p.1 p.1.2 q.1 q.1.2 p.2 p.2.2 q.2 q.2.2 hf
      simp [← Subtype.coe_le_coe] at hp hq
      grind
  mpr hA := by sorry

/-- Suppose `A` is a finite set. Then `A` is Sidon iff `(A - A).card = 2 * (A.card.choose 2) + 1`.
-/
theorem isSidon_iff_sub_card (A : Finset ℕ) :
    IsSidon A ↔ (A - A).card = 2 * (A.card.choose 2) + 1 where
  mp hA := by
    have : A - A = (A - A \ {0}) ∪ {0} := by sorry
    have h_card_eq : image (fun (p : A × A) => p.1.1 + p.2.1) {s | s.1 ≠ s.2} = A - A \ {0} := by
      sorry
    rw [this, Finset.card_union_eq_card_add_card.2 (by sorry), ← h_card_eq,
      Finset.card_image_of_injOn]
    · congr
      sorry
    · sorry
  mpr hA := by sorry

end IsSidon
