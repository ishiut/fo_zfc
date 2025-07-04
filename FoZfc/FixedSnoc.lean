/-
Copyright (c) 2025 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import Init.Data.Fin.Basic

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# The version of Fin.snoc for the fixed type.

## Main Definitions

- A `FirstOrder.ZFC.FixedSnoc.fixedSnoc` defines the version of Fin.snoc for the fixed type V.

## Main Statements

- A `FirstOrder.ZFC.FixedSnoc.snoc_conv` proves the relationship between Fin.snoc and fixedSnoc.
- `FirstOrder.ZFC.FixedSnoc.snoc_last` and `FirstOrder.ZFC.FixedSnoc.snoc_init` are
  to compute the values of fixedSnoc

## Implimentation notes

- Many theorems that make simp work better are proved.

-/

universe u

namespace FirstOrder.ZFC.FixedSnoc

variable {V : Type u}

/-- Fin.snoc for the type V. -/
def fixedSnoc {n : ℕ} (xs : Fin n → V) (b : V) :=
    (fun (k : Fin (n + 1)) => if h : k.val < n then xs (Fin.castLT k h) else b)

/-- Fin.snoc = fixedSnoc when applied to V. -/
@[simp]
theorem snoc_conv {n : ℕ} {xs : Fin n → V} {b : V} : Fin.snoc xs b = fixedSnoc xs b:= by
  exact rfl

/-- fixedSnoc xs a n = a when xs : Fin n → V -/
@[simp]
theorem snoc_last {n : ℕ} (xs : Fin n → V) (a : V) : (fixedSnoc xs a) (Fin.last n) = a := by
  rw [← snoc_conv]
  simp

/-- fixedSnoc xs a k.castSucc = xs k when xs : Fin n → V and k : Fin n. -/
@[simp]
theorem snoc_init {V : Type u} {n : ℕ} {xs : Fin n → V} {a : V} {k : Fin n} :
    fixedSnoc xs a k.castSucc = xs k := by
  rw [← snoc_conv]
  simp

/-- Rewrite castAdd by using castAdd with one castSucc. -/
@[simp]
theorem castAdd_to_castSucc {n m : ℕ} {k : Fin n} : k.castAdd (m+1) = (k.castAdd m).castSucc := by
  apply Fin.eq_of_val_eq
  simp

/-- ofNat written by using Fin.last and castAdd. -/
@[simp]
theorem coe_to_cast_add {n n' : ℕ} : Fin.ofNat (n+1+n') n = (Fin.last n).castAdd n' := by
  apply Fin.eq_of_val_eq
  simp
  rw [Nat.mod_eq_of_lt (by omega)]

/-- ofNat n + ofNat m = ofNat (n + m). -/
@[simp]
theorem add_coe_eq_coe_add {n k m : ℕ} [NeZero (n + m)] :
    (Fin.ofNat (n+m) n + Fin.ofNat (n+m) k) = Fin.ofNat (n+m) (n+k) := by
  apply Fin.eq_of_val_eq
  rw [Fin.val_add]
  simp

/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim. -/
@[simp]
theorem sum_fixedSnoc_castSucc {n : ℕ} {s : ℕ → V} {xs : Fin n → V} {a : V} :
    (Sum.elim s (fixedSnoc xs a) ∘ Sum.map id fun (i : Fin n) ↦ i.castSucc) = Sum.elim s xs := by
  funext i
  rcases i with k | k
  · simp
  · simp

/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim. -/
@[simp]
theorem fixedSnoc_castSucc {n : ℕ} {xs : Fin n → V} {a : V} :
    (fixedSnoc xs a ∘ Fin.castSucc) = xs := by
  funext k
  simp

@[simp]
theorem Fintuple_1_0 {a : V} : ![a] 0 = a := by rfl

@[simp]
theorem Fintuple_2_0 {a b : V} : ![a, b] (0 : Fin 2) = a := by rfl

@[simp]
theorem Fintuple_1_0' {a : V} : ![a] (@Nat.cast (Fin 1) (Fin.NatCast.instNatCast 1) 0) = a := by rfl

@[simp]
theorem Fintuple_2_0' {a b : V} :
    ![a, b] (@Nat.cast (Fin 2) (Fin.NatCast.instNatCast 2) 0) = a := by rfl

@[simp]
theorem Fintuple_3_0' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 0) = a := by rfl

@[simp]
theorem Fintuple_3_1' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 1) = b := by rfl

@[simp]
theorem Fintuple_3_2' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 2) = c := by rfl

@[simp]
theorem Fintuple_4_0' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 0) = a := by rfl

@[simp]
theorem Fintuple_4_1' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 1) = b := by rfl

@[simp]
theorem Fintuple_4_2' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 2) = c := by rfl

@[simp]
theorem Fintuple_4_3' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 3) = d := by rfl

@[simp]
theorem FixedSnoc_2_0 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 0 = a := by rfl

@[simp]
theorem FixedSnoc_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 1 = b := by rfl


@[simp]
theorem FixedSnoc_0_2_0 {xs : Fin 0 → V} {a b : V} :
  fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 0 Fin.instOfNat) = a := by
  have h : (@OfNat.ofNat (Fin (0 + 2)) 0 Fin.instOfNat) = (Fin.last 0).castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 1 Fin.instOfNat) = b := by
  have h : (@OfNat.ofNat (Fin (0 + 2)) 1 Fin.instOfNat) = Fin.last 1 := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_last]

@[simp]
theorem FixedSnoc_0_3_0 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 0 Fin.instOfNat) = a := by
  have h : (@OfNat.ofNat (Fin (0 + 3)) 0 Fin.instOfNat) = (Fin.last 0).castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_3_1 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 1 Fin.instOfNat) = b := by
  have h : (@OfNat.ofNat (Fin (0 + 3)) 1 Fin.instOfNat) = (Fin.last 1).castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_3_2 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 2 Fin.instOfNat) = c := by
  have h : (@OfNat.ofNat (Fin (0 + 3)) 2 Fin.instOfNat) = Fin.last 2:= by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_last]

@[simp]
theorem FixedSnoc_0_4_0 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 0 Fin.instOfNat) = a := by
  have h : (@OfNat.ofNat (Fin (0 + 4)) 0 Fin.instOfNat)
      = (Fin.last 0).castSucc.castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_4_1 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
      (@OfNat.ofNat (Fin (0 + 4)) 1 Fin.instOfNat) = b := by
  have h : (@OfNat.ofNat (Fin (0 + 4)) 1 Fin.instOfNat)
      = (Fin.last 1).castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_4_2 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 2 Fin.instOfNat) = c := by
  have h : (@OfNat.ofNat (Fin (0 + 4)) 2 Fin.instOfNat) = (Fin.last 2).castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_init, snoc_last]

@[simp]
theorem FixedSnoc_0_4_3 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 3 Fin.instOfNat) = d := by
  have h : (@OfNat.ofNat (Fin (0 + 4)) 3 Fin.instOfNat) = Fin.last 3:= by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp only [snoc_last]

@[simp]
theorem FixedSnoc_n_2_0 {n : ℕ} {xs : Fin n → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b
    (@Nat.cast (Fin (n + 1 + 1)) (Fin.NatCast.instNatCast (n + 1 + 1)) n) = a := by
  have h : (@Nat.cast (Fin (n + 1 + 1)) (Fin.NatCast.instNatCast (n + 1 + 1)) n)
      = (Fin.last n).castSucc := by
    apply Fin.eq_of_val_eq
    simp
    omega
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_2_1 {n : ℕ} {xs : Fin n → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@Nat.cast (Fin (n + 1 + 1))
    (Fin.NatCast.instNatCast (n + 1 + 1)) (n + 1)) = b:= by
  have h : (@Nat.cast (Fin (n + 1 + 1)) (Fin.NatCast.instNatCast (n + 1 + 1)) (n + 1))
      = Fin.last (n + 1) := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_3_0 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) n) = a := by
  have h : (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) n)
      = (Fin.last n).castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
    omega
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_3_1 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+1)) = b := by
  have h : (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+1))
      = (Fin.last (n+1)).castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_3_2 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+2)) = c := by
  have h : (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+2)) = Fin.last (n+2) := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_4_0 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) n) = a := by
  have h : (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) n)
      = (Fin.last n).castSucc.castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
    omega
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_4_1 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+4)) (n+1)) = b := by
  have h : (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n+2+1+1)) (n+1))
      = (Fin.last (n+1)).castSucc.castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_4_2 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 2)) = c := by
  have h : (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 2))
      = (Fin.last (n+2)).castSucc := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem FixedSnoc_n_4_3 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 3)) = d := by
  have h : (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 3))
      = Fin.last (n+3) := by
    apply Fin.eq_of_val_eq
    simp
  rw [h]
  simp

@[simp]
theorem fixedSnoc_castSucc_2 {n : ℕ} {xs : Fin n → V} {a b : V} :
    (fixedSnoc (fixedSnoc xs a) b ∘ fun (i : Fin n) ↦ i.castSucc.castSucc)
    = xs := by
  funext k
  simp

@[simp]
theorem fixedSnoc_castSucc_3 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c ∘ fun i ↦ i.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp

@[simp]
theorem fixedSnoc_castSucc_4 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    ∘ fun i ↦ i.castSucc.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp

end FixedSnoc
end ZFC
end FirstOrder
