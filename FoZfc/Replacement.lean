/-
Copyright (c) 2025 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import Init.Data.Fin.Basic

import FoZfc.Basic
import FoZfc.Tostring
import FoZfc.FixedSnoc
import FoZfc.BoundedFormulaOps
import FoZfc.Axioms

/-!
# The Replacement Axiom

## Main Definitions

- A `FirstOrder.ZFC.RelByFormula` defines the relation defined by a formula.
- A `FirstOrder.ZFC.intIsFunctFormula` defines a formula for ϕ describes
  a function. A `FirstOrder.ZFC.EntIsFunctFormula` defines ϕ describes
  a function externally.
- A `FirstOrder.ZFC.intIsImage` defines the formula for fv 1 is the image of
  the function defined by ϕ of fv 0.
- A `FirstOrder.ZFC.ModelReplacement` is a class of models of Set Theory
  with the replacement schema.

## Main Statements

- Various "realize" theorems are proved.

-/

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

open ReplaceFV
open ZFC
open FixedSnoc

universe u v

namespace FirstOrder.ZFC

variable {V : Type u}

/-- Make a formula for ϕ describes a function. -/
def intIsFunctFormula {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) : LZFC.BoundedFormula ℕ n :=
  let ϕ' := liftAt 3 n ϕ
  let tsN1 := makeTsN ![bv'' n, bv'' (n+1)]
  let tsN2 := makeTsN ![bv'' n, bv'' (n+2)]
  (∀'∀'∀'(BoundedFormula.replaceFV ϕ' tsN1 ⟹
  BoundedFormula.replaceFV ϕ' tsN2 ⟹ bv'' (n+1) =' bv'' (n+2)))

/-- Find the (k+1)-ary relation defined by a formula. -/
def RelByFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n) {k : ℕ} (xs1 : Fin (k + 1) → V) : Prop :=
  ϕ.Realize (replaceInitialValues s xs1) xs

/-- Dexcribe ϕ describes a function. -/
def ExtIsFunctFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n) : Prop :=
  let R : (Fin 2 → V) → Prop := RelByFormula s xs ϕ
  ∀ (x : V) (y₁ : V) (y₂ : V), (R ![x, y₁] → R ![x, y₂] → y₁ = y₂)

theorem realize_is_funct_formula [ModelSets V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) :
    (intIsFunctFormula ϕ).Realize s xs ↔ ExtIsFunctFormula s xs ϕ := by
  unfold intIsFunctFormula ExtIsFunctFormula RelByFormula
  simp [realize_liftAt']

/-- Make a formula for fv 1 is the image of fv 0 under the relation defined by ϕ. -/
def intIsImage {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
  LZFC.BoundedFormula ℕ n := (∀'(bv'' n ∈' fv (n+1) 1 ⇔
  ∃'((bv'' (n+1)) ∈' fv' 0 ∧' (BoundedFormula.replaceFV (liftAt 2 n ϕ)
  (makeTsN ![bv'' (n+1), bv'' n])))))

/-- Describe b is the image of a under the relation defined by ϕ. -/
def ExtIsImage [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) := ∀ (y : V),
  (y ∈ b ↔ ∃ (x : V), x ∈ a ∧ ϕ.Realize (replaceInitialValues s ![x, y]) xs)

@[simp]
theorem replaceInitialValues_replaceInitialValues {n m : ℕ} {h : n ≤ m}
    {s : ℕ → V} {xs1 : Fin (n + 1) → V} {xs2 : Fin (m + 1) → V} :
    replaceInitialValues (replaceInitialValues s xs1) xs2 =
    replaceInitialValues s xs2 := by
  funext k
  unfold replaceInitialValues
  by_cases h_k_le_m : k < m + 1
  · rw [if_pos h_k_le_m]
    rw [if_pos h_k_le_m]
  · have h_k_gt_n : ¬ (k < n + 1) := by omega
    rw [if_neg h_k_le_m]
    rw [if_neg h_k_gt_n]
    rw [if_neg h_k_le_m]

@[simp]
theorem realize_is_image [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) : (intIsImage ϕ).Realize
    (replaceInitialValues s ![a, b]) xs ↔ ExtIsImage s xs ϕ a b:= by
  unfold intIsImage ExtIsImage
  simp [realize_liftAt']

/-- Model with the Replacement schema. -/
class ModelReplacement (V : Type u) extends ModelSets V where
  replacement_schema : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n), (intIsFunctFormula ϕ ⟹
  ∀'∃'(BoundedFormula.replaceFV (liftAt 2 n (intIsImage ϕ))
  (makeTsN ![bv'' n, bv'' (n+1)]))).Realize s xs

/-- The Replacement described externally. -/
theorem ext_replacement [ModelReplacement V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) :
    ExtIsFunctFormula s xs ϕ → ∀ (a : V), ∃ (b : V),
    ExtIsImage s xs ϕ a b := by
  intro h0 a
  have h_intIsFunctFormula : (intIsFunctFormula ϕ).Realize s xs := by
    apply (realize_is_funct_formula s xs ϕ).mpr h0
  obtain ⟨b, h_b⟩ := realize_ex.mp ((ModelReplacement.replacement_schema
    s xs ϕ) h_intIsFunctFormula a)
  rw [snoc_conv, snoc_conv] at h_b
  use b
  rw [BoundedFormula.realize_replaceFV, realize_liftAt'] at h_b
  · simp at h_b
    exact h_b
  · omega
  · omega

class ModelPR (V : Type u) extends ModelPairing V, ModelReplacement V where

theorem ext_test [ModelPR V] (s : ℕ → V) (xs : Fin 0 → V) (a : V) :
    ∃ (b : V), ExtIsImage s xs intIsSingleton a b := by
  have h1 : ExtIsFunctFormula s xs intIsSingleton := by
    unfold ExtIsFunctFormula
    simp
    intro x y₁ y₂
    unfold RelByFormula
    simp
    apply ext_singleton_unique
  obtain ⟨b, hb⟩ := ext_replacement s xs intIsSingleton h1 a
  use b

theorem int_test [ModelPR V] (s : ℕ → V) (xs : Fin 0 → V) :
    (∀'∃'((intIsImage intIsSingleton).liftAndReplaceFV 2 0 ![bv'' 0, bv'' 1])).Realize s xs := by
  simp
  intro a
  obtain ⟨b, hb⟩ := ext_test s xs a
  use b
  simp [realize_liftAt']
  have h1 : (fixedSnoc (fixedSnoc xs a) b ∘ fun i ↦ i.addNat 2) = xs := by
    funext k
    apply Fin.elim0 k
  rw [h1]
  apply hb

end FirstOrder.ZFC
