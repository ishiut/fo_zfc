/-
Copyright (c) 2025 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import Mathlib.Data.Set.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fin.Tuple.Basic

import FoZfc.FixedSnoc

/-!
# Definitions and theorems about replaceFV and liftAt.

## Main Definitions

- FirstOrder.Language.Term.replaceFV defines the function to replace all
  free variables fv' k with tsN k in a term t.
- FirstOrder.Language.BoundedFormula.replaceFV the function to replace all
  free variables fv' k with tsN k in a bounded formula ϕ.
- FirstOrder.Language.BoundedFormula.makeTsN defines the function on ℕ
  whose value at k is ts k if k < m + 1 and fv' k otherwise.
- FirstOrder.Language.BoundedFormula.replaceInitialValues replace
  the initial part of s : ℕ → V by xs : Fin (n + 1) → V.
- FirstOrder.Language.BoundedFormula.liftAndReplaceFV applies liftAt n' m
  and replace (makeTsN ts) in one call.

## Main Statements

- Various "realize" theorems are proved.
- realize_liftAt' is the version of realize_liftAt in which we assume m ≤ n
  instead of m + n' ≤ n + 1.

## Notations

- The symbols for Or and And, ∨' and ∧', are defined.

-/

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

-- u for universe, v for free variable indexes
universe u v

namespace FirstOrder.Language

variable {V : Type u} {L : Language} {α : Type v}

/-- Or operator in the formula. -/
@[match_pattern]
def BoundedFormula.or {n : ℕ} (ϕ1 ϕ2 : L.BoundedFormula α n) : L.BoundedFormula α n := (∼ϕ1)⟹ϕ2

@[inherit_doc] infix : 63 "∨'" => BoundedFormula.or

/-- And operator in the formula. -/
@[match_pattern]
def BoundedFormula.and {n : ℕ} (ϕ1 ϕ2 : L.BoundedFormula α n) : L.BoundedFormula α n :=  ∼(ϕ1⟹∼ϕ2)

@[inherit_doc] infix : 64 "∧'" => BoundedFormula.and

@[simp]
theorem BoundedFormula.realize_or [L.Structure V] {n : ℕ}
    {ϕ ψ : L.BoundedFormula ℕ n} {s : ℕ → V} {xs : Fin n → V} :
    (ϕ ∨' ψ).Realize s xs ↔ ϕ.Realize s xs ∨ ψ.Realize s xs := by
  rw [BoundedFormula.or]
  simp
  constructor
  · intro h0
    by_cases h1 : ϕ.Realize s xs
    · apply Or.inl h1
    · right
      apply h0 h1
  · intro h0 h1
    apply Or.resolve_left h0 h1

@[simp]
theorem BoundedFormula.realize_and [L.Structure V] {n : ℕ}
    {ϕ ψ : L.BoundedFormula ℕ n} {s : ℕ → V} {xs : Fin n → V} :
    (ϕ ∧' ψ).Realize s xs ↔ ϕ.Realize s xs ∧ ψ.Realize s xs := by
  rw [BoundedFormula.and]
  simp

/- Definitions about the replacement of variables with terms-/

variable {L : Language}

-- fv' k ↦ ts k
-- Others are unchanged
/-- replace all free variables fv' k with tsN k in a term t. -/
def Term.replaceFV {n : ℕ} (t : L.Term (ℕ ⊕ Fin n)) (tsN : ℕ → (L.Term (ℕ ⊕ Fin n))) :=
  match t with
  | Term.var (Sum.inl k) => tsN k
  | Term.var (Sum.inr _) => t
  | Term.func _f _ts => Term.func _f (fun i => Term.replaceFV (_ts i) tsN)

/-- replace all free variables fvN n k with tsN k in a formula ϕ. -/
def BoundedFormula.replaceFV {n : ℕ} (ϕ : L.BoundedFormula ℕ n)
    (tsN : ℕ → L.Term (ℕ ⊕ Fin n)): L.BoundedFormula ℕ n:=
match ϕ with
| BoundedFormula.falsum => BoundedFormula.falsum
| BoundedFormula.equal t₁ t₂ => BoundedFormula.equal (Term.replaceFV t₁ tsN) (Term.replaceFV t₂ tsN)
| BoundedFormula.rel R _ts => BoundedFormula.rel R (fun i => Term.replaceFV (_ts i) tsN)
| BoundedFormula.imp f₁ f₂ => BoundedFormula.imp (BoundedFormula.replaceFV f₁ tsN)
    (BoundedFormula.replaceFV f₂ tsN)
| BoundedFormula.all f => BoundedFormula.all
    (BoundedFormula.replaceFV f (fun k => Term.liftAt 1 n (tsN k)))

/-- Make a function on ℕ whose value at k is ts k if k < m + 1 and
  fv' k otherwise. -/
def BoundedFormula.makeTsN {n m : ℕ} (ts : Fin (m + 1) → L.Term (ℕ ⊕ Fin n)) (k : ℕ) :=
  if k < m + 1 then
    ts (Fin.ofNat (m+1) k)
  else
    Term.var (Sum.inl k)

/-- Replace the initial part of s : ℕ → V by xs : Fin (n + 1) → V. -/
def BoundedFormula.replaceInitialValues {n : ℕ} (s : ℕ → V)
    (xs : Fin (n + 1) → V) (k : ℕ) :=
  if k < n + 1 then
    xs (Fin.ofNat (n+1) k)
  else
    s k

/-- Apply liftAt n' m and replace (makeTsN ts) in one call. -/
@[simp]
def BoundedFormula.liftAndReplaceFV {n l : ℕ} (ϕ : L.BoundedFormula ℕ n)
    (n' m : ℕ) (ts : Fin (l + 1) → L.Term (ℕ ⊕ Fin (n + n'))) :
    L.BoundedFormula ℕ (n+n') := (ϕ.liftAt n' m).replaceFV (makeTsN ts)

namespace ReplaceFV

open FirstOrder.ZFC.FixedSnoc

variable {V : Type u} [L.Structure V]

@[simp]
-- def tail_s (s : ℕ → V) (k : ℕ) := s (k + 1)

theorem Term.realize_replaceFV {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t : L.Term (ℕ ⊕ Fin n)} {tsN : ℕ → L.Term (ℕ ⊕ Fin n)} :
    Term.realize (Sum.elim s xs) (Term.replaceFV t tsN) =
Term.realize (Sum.elim (fun k => Term.realize (Sum.elim s xs) (tsN k)) xs) t := by
  induction' t with i _l _f _ts _ih
  · rcases i with k | k
    · unfold Term.replaceFV
      simp
    · unfold Term.replaceFV
      simp
  · unfold Term.replaceFV
    simp
    apply congr
    · rfl
    · funext i
      apply _ih

@[simp]
theorem Term.realize_liftAt'_one {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {t : L.Term (ℕ ⊕ Fin n)} {a : V} :
    Term.realize (Sum.elim s (Fin.snoc xs a)) (Term.liftAt 1 n t)
    = Term.realize (Sum.elim s xs) t := by
  induction' t with i _l _f _ts _ih
  · rcases i with k | k
    · unfold Term.liftAt
      simp
    · simp
  · simp

-- Make it a different theorem when n = 0
@[simp]
theorem Term.realize_liftAt' {n n' : ℕ} {s : ℕ → V} {xs : Fin n → V}
  {xs1 : Fin (n + n') → V} {t : L.Term (ℕ ⊕ Fin n)} :
  (∀ (k : Fin n), xs1 (k.castAdd n')= xs k) →
  Term.realize (Sum.elim s xs1) (Term.liftAt n' n t)
  = Term.realize (Sum.elim s xs) t := by
  intro h_xs1_restriction_xs
  induction' t with i _l _f _ts _ih
  · rcases i with k | k
    · unfold Term.liftAt
      simp
    · simp
      let k_nat := k.val
      rw [← h_xs1_restriction_xs]
  · simp
    apply congr
    · rfl
    · funext k
      rw [← _ih]
      simp

@[simp]
theorem BoundedFormula.realize_replaceFV {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    {ϕ : L.BoundedFormula ℕ n} {tsN : ℕ → L.Term (ℕ ⊕ Fin n)} :
    (BoundedFormula.replaceFV ϕ tsN).Realize s xs ↔
    ϕ.Realize (fun k => Term.realize (Sum.elim s xs) (tsN k)) xs := by
  induction' ϕ with _n _n t₁ t₂ _n _l _R _ts _n f₁ f₂ ih₁ ih₂ _n f ih
  · unfold BoundedFormula.replaceFV
    exact Eq.to_iff rfl
  · unfold BoundedFormula.replaceFV
    let s1 := fun k ↦ Term.realize (Sum.elim s xs) (tsN k)
    have h_s1 : (fun k ↦ Term.realize (Sum.elim s xs) (tsN k)) = s1 := by rfl
    -- unfold Term.replaceFV
    -- simp
    rw [h_s1]
    have h1 : (equal (Term.replaceFV t₁ tsN) (Term.replaceFV t₂ tsN)).Realize s xs ↔
        Term.realize (Sum.elim s xs) (Term.replaceFV t₁ tsN) =
        Term.realize (Sum.elim s xs) (Term.replaceFV t₂ tsN) := by
      apply realize_bdEqual
    rw [h1]
    have h2 : (equal t₁ t₂).Realize s1 xs ↔ Term.realize (Sum.elim s1 xs) t₁ =
        Term.realize (Sum.elim s1 xs) t₂ := by
      apply realize_bdEqual
    rw [h2]
    rw [Term.realize_replaceFV, Term.realize_replaceFV]
  · unfold BoundedFormula.replaceFV
    have h1 : (rel _R fun i ↦ Term.replaceFV (_ts i) tsN).Realize s xs ↔
        Structure.RelMap _R fun i ↦ Term.realize (Sum.elim s xs) (Term.replaceFV (_ts i) tsN) := by
      apply realize_rel
    rw [h1]
    let s1 := fun k ↦ Term.realize (Sum.elim s xs) (tsN k)
    have h_s1 : (fun k ↦ Term.realize (Sum.elim s xs) (tsN k)) = s1 := by rfl
    rw [h_s1]
    have h2 : (rel _R _ts).Realize s1 xs ↔ Structure.RelMap _R fun i ↦
        Term.realize (Sum.elim s1 xs) (_ts i) := by
      apply realize_rel
    rw [h2]
    have h3 : ∀ i, Term.realize (Sum.elim s xs) (Term.replaceFV (_ts i) tsN) =
        Term.realize (Sum.elim s1 xs) (_ts i) := by
      intro i
      rw [← h_s1, Term.realize_replaceFV]
    have h4 : (fun i ↦ Term.realize (Sum.elim s xs) (Term.replaceFV (_ts i) tsN)) =
        (fun i ↦ Term.realize (Sum.elim s1 xs) (_ts i)) := by
      funext
      apply h3
    rw [h4]
  · unfold BoundedFormula.replaceFV
    simp
    rw [ih₁, ih₂]
  · unfold BoundedFormula.replaceFV
    simp
    apply forall_congr'
    intro a
    rw [ih]
    have h1 : ∀ (k : ℕ), Term.realize (Sum.elim s (fixedSnoc xs a))
        (Term.liftAt 1 _n (tsN k)) = Term.realize (Sum.elim s xs) (tsN k) := by
      intro k
      apply Term.realize_liftAt'_one
    have h2 : (fun k ↦ Term.realize (Sum.elim s (fixedSnoc xs a))
        (Term.liftAt 1 _n (tsN k))) = (fun k ↦ Term.realize (Sum.elim s xs)
        (tsN k)) := by
      funext k
      apply h1
    rw [h2]

theorem realize_liftAt' {n' m : ℕ} {h_n_prime_nezero : n' > 0} {s : ℕ → V} :
    ∀ {n : ℕ} {φ : L.BoundedFormula ℕ n} (xs : Fin (n + n') → V), m ≤ n →
    ((liftAt n' m φ).Realize s xs ↔ φ.Realize s (xs ∘ fun (i : Fin n) =>
    if ↑i < m then Fin.castAdd n' i else i.addNat n')) := by
  intro n φ
  unfold liftAt
  -- rw [liftAt]
  induction' φ with _n _n t₁ t₂ _n l R ts _n f₁ f₂ ih₁ ih₂ _n f ih
  · simp [mapTermRel, Realize]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · intro xs
    intro hmn
    simp only [mapTermRel, Realize, ih₁ xs hmn, ih₂ xs hmn]
  · intro xs
    intro hmn
    unfold mapTermRel
    simp
    apply forall_congr'
    intro a
    have h : NeZero (_n+n') := by
      apply NeZero.of_pos
      omega
    have h_bar_n : _n+1+n'=_n+n'+1 := by omega
    let xs1 (k : Fin (_n+1+n')): V  := (fixedSnoc xs a) (Fin.cast h_bar_n k)
    let ih1 := ih xs1
    have h1 : (mapTermRel (fun x t ↦ Term.liftAt n' m t) (fun x ↦ id)
        (fun x ↦ castLE (liftAt._proof_1 n' x : x + 1 + n' ≤ x + n' + 1)) f).Realize
        s xs1 ↔ (castLE (liftAt._proof_1 n' _n : _n + 1 + n' ≤ _n + n' + 1)
        (mapTermRel (fun x t ↦ Term.liftAt n' m t) (fun x ↦ id)
        (fun x ↦ castLE (liftAt._proof_1 n' x : x + 1 + n' ≤ x + n' + 1)) f)).Realize
        s (fixedSnoc xs a) := by
      rw [realize_castLE_of_eq]
      have h1_1 : (fixedSnoc xs a ∘ Fin.cast ?h) = xs1 := by
        funext k
        unfold xs1
        simp
      rw [h1_1]
      exact h_bar_n
    rw [← h1]
    have h2 : (xs1 ∘ fun (i : Fin (_n+1)) ↦ if ↑i < m then Fin.castAdd n' i
        else i.addNat n') = (fixedSnoc (xs ∘ fun (i : Fin _n) ↦
        if ↑i < m then Fin.castAdd n' i else i.addNat n') a) := by
      funext k
      simp
      by_cases h_k_lt_m : k.val < m
      · rw [if_pos]
        · unfold xs1
          have h2_1 : (Fin.cast h_bar_n (Fin.castAdd n' k)) = (Fin.ofNat (_n+n') k).castSucc := by
            apply Fin.eq_of_val_eq
            simp
            rw [Nat.mod_eq_of_lt]
            omega
          rw [h2_1]
          simp
          have h2_2 : NeZero _n := by
            have h2_2_1 : k.val < _n := by
              omega
            exact NeZero.of_gt h2_2_1
          have h2_3 : fixedSnoc (xs ∘ fun i ↦ if ↑i < m then Fin.castAdd n' i
              else i.addNat n') a k = xs (Fin.ofNat (_n+n') k.val) := by
            have h2_3_1 : k = (Fin.ofNat _n k.val).castSucc := by
              simp
              apply Fin.eq_of_val_eq
              simp
              rw [Nat.mod_eq_of_lt]
              omega
            rw [h2_3_1]
            simp
            rw [if_pos]
            · apply congrArg
              apply Fin.eq_of_val_eq
              simp
              rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              · omega
              · omega
            · rw [Nat.mod_eq_of_lt]
              omega
              omega
          rw [h2_3]
          simp
        · omega
      · by_cases h_k__n : k = _n
        · rw [h_k__n]
          unfold xs1
          rw [if_neg]
          have h2 : (Fin.cast h_bar_n (k.addNat n')) = Fin.last (_n+n') := by
            apply Fin.eq_of_val_eq
            simp
            exact h_k__n
          rw [h2]
          simp
          have h3 : k = Fin.last _n := by
            apply Fin.eq_of_val_eq
            simp
            exact h_k__n
          rw [h3]
          simp
          omega
        · rw [if_neg]
          · unfold xs1
            have h2 : (Fin.cast h_bar_n (k.addNat n')) = (Fin.ofNat (_n + n')
                (k.val+n')).castSucc := by
              apply Fin.eq_of_val_eq
              simp
              rw [Nat.mod_eq_of_lt]
              simp
              omega
            rw [h2]
            have h3 : NeZero _n := by
              have h3_1 : k.val < _n := by
                omega
              exact NeZero.of_gt h3_1
            have h4 : k = (Fin.ofNat _n k.val).castSucc := by
              apply Fin.eq_of_val_eq
              simp
              rw [Nat.mod_eq_of_lt]
              omega
            nth_rw 2 [h4]
            simp
            rw [if_neg]
            · apply congrArg
              apply Fin.eq_of_val_eq
              simp
              rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
              omega
              omega
            · simp
              rw [Nat.mod_eq_of_lt]
              · omega
              · omega
          · omega
    rw [← h2]
    apply ih1
    omega

@[simp]
theorem replaceInitialValues_1_0 {s : ℕ → V} {a : V} :
    replaceInitialValues s ![a] 0 = a := by rfl

@[simp]
theorem replaceInitialValues_2_0 {s : ℕ → V} {a b : V} :
    replaceInitialValues s ![a, b] 0 = a := by rfl

@[simp]
theorem replaceInitialValues_2_1 {s : ℕ → V} {a b : V} :
    replaceInitialValues s ![a, b] 1 = b := by rfl

@[simp]
theorem realize_makeTsN {n m k : ℕ} {ts : Fin (m + 1) → L.Term (ℕ ⊕ Fin n)}
    {h : k < m + 1}: makeTsN ts k = ts (Fin.ofNat (m+1) k) := by
  unfold makeTsN
  simp
  intro h1
  omega
end ReplaceFV
end Language
end FirstOrder
