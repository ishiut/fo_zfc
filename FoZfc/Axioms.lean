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

/-!
# Axioms of ZF except Replacement.

## Main Definitions

- IsEmptyset describes an emptyset.
- IsSingleton describes a singleton.
- IsPair describes an unordered pair.
- IsOrderedPair describes an ordered pair.
- IsUnion describes a union.
- IsSeparation describes {x∈(bv n) : ϕ}. The placeholder for ϕ is fv 0.
- A `FirstOrder.ZFC.ModelEmptyset` is a class of models of Set Theory
  with an emptyset.
- A `FirstOrder.ZFC.ModelPairing` is a class of models of Set Theory
  with the pairing axiom.
- A `FirstOrder.ZFC.ModelUnion` is a class of models of Set Theory
  with the pairing axiom.
- A `FirstOrder.ZFC.ModelInfinity` is a class of models of Set Theory
  with the infinity axiom.
- A `FirstOrder.ZFC.ModelComprehension` is a class of models of Set Theory
  with the comprehension schema.

## Main Statements

- Various basic propositions prove from the axioms are proved.
- ext_induction and int_induction prove the mathematical induction
  externally an dinternally.

## Notations

- Definitions that begin with "int" are to make a formula that describe it.
  When it is without prime, use the initial free variables as place holders.
  When it is with prime, accept terms as place holders.
- Definitions that begin with "Ext" are propositions that describe it externally.

-/


-- The version in which replaceFv is done non-recursively

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

open ReplaceFV
open ZFC
open FixedSnoc

universe u v

namespace FirstOrder.ZFC

variable {V : Type u}

-- Lemmas that require LZFC or ModelSets are placed here.

@[simp]
theorem realize_fixedSnoc_makeTsN_1 [ModelSets V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} {x : V} : (fun k ↦ Term.realize
    (Sum.elim s (fixedSnoc xs x)) (makeTsN ![bv'' n] k))
    = replaceInitialValues s ![x] := by
  funext k
  unfold makeTsN
  unfold replaceInitialValues
  by_cases h_k_0 : k = 0
  · rw [h_k_0]
    simp
  · rw [if_neg]
    · simp
      intro h
      contradiction
    · omega

@[simp]
theorem realize_fixedSnoc_makeTsN_2 [ModelSets V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} {t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)} : (fun (k : ℕ) ↦
    Term.realize (Sum.elim s xs) (makeTsN ![t₁, t₂] k)) =
    replaceInitialValues s ![Term.realize (Sum.elim s xs) t₁,
    Term.realize (Sum.elim s xs) t₂] := by
  funext k
  by_cases h_k_lt_2 : k < 2
  · rw [realize_makeTsN]
    · simp
      by_cases h_k_0 : k = 0
      · rw [h_k_0]
        simp
      · have h_k_1 : k = 1 := by omega
        · rw [h_k_1]
          simp
    · omega
  · unfold makeTsN replaceInitialValues
    simp
    rw [if_neg]
    · simp
      omega
    · omega

@[simp]
theorem realize_fixedSnoc_makeTsN_3 [ModelSets V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} {a b c : V} : (fun k ↦
    Term.realize (Sum.elim s (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c))
    (makeTsN ![bv'' n, bv'' (n+1)] k)) = replaceInitialValues s ![a, b] := by
  funext k
  by_cases h_k_lt_2 : k < 2
  · rw [realize_makeTsN]
    · simp
      by_cases h_k_0 : k = 0
      · rw [h_k_0]
        simp
      · have h_k_1 : k = 1 := by omega
        · rw [h_k_1]
          simp
    · omega
  · unfold makeTsN replaceInitialValues
    simp
    rw [if_neg]
    · simp
      omega
    · omega

theorem realize_fixedSnoc_makeTsN [ModelSets V] {n m : ℕ} {s : ℕ → V}
    {xs : Fin n → V} {ts : Fin (m + 1) → LZFC.Term (ℕ ⊕ Fin n)} :
    (fun k ↦ Term.realize (Sum.elim s xs)  (makeTsN ts k)) =
    replaceInitialValues s (fun (i : Fin (m+1)) ↦
    Term.realize (Sum.elim s xs) (makeTsN ts i.val)) := by
  funext k
  unfold makeTsN replaceInitialValues
  simp
  by_cases h_k_le_m : k < m + 1
  · rw [if_pos h_k_le_m]
    rw [if_pos h_k_le_m]
    rw [Nat.mod_eq_of_lt h_k_le_m]
    rw [if_pos h_k_le_m]
  · rw [if_neg h_k_le_m]
    rw [if_neg h_k_le_m]
    simp

@[simp]
theorem Term.realize_fixedSnoc_0 [ModelSets V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} {a b : V} : (fun k ↦ Term.realize (Sum.elim s
    (fixedSnoc (fixedSnoc xs a) b)) (if k = 0 then bv'' n else var (Sum.inl k)))
    = replaceInitialValues s ![a] := by
  funext k
  by_cases h_k_0 : k = 0
  · rw [h_k_0]
    simp
  · rw [if_neg h_k_0]
    unfold replaceInitialValues
    simp
    intro h
    omega

/-- Describe that fv 0 is an emptyset. -/
def intIsEmptyset {n : ℕ} : LZFC.BoundedFormula ℕ n := ∀'(bv'' n ∉' fv' 0)

/-- Describe tht the given term is an emptyset. -/
def intIsEmptyset' {n : ℕ} (t : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := ∀'((bv'' n ∉' fv' 0).replaceFV
  (makeTsN ![t.liftAt 1 n]))

/-- Describe a is an emptyset. -/
def ExtIsEmptyset [ModelSets V] (a : V) := ∀ (x : V), x ∉ a

/-- Model of Set Theory with an emptyset. -/
class ModelEmptyset (V : Type u) extends ModelSets V where
  emptyset_exists : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V),
  (∃'(intIsEmptyset' (bv' 0))).Realize s xs

@[simp]
theorem realize_is_emptyset [ModelEmptyset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (a : V): intIsEmptyset.Realize (replaceInitialValues s
    ![a]) xs ↔ ExtIsEmptyset a := by
  rw [intIsEmptyset, ExtIsEmptyset]
  simp

@[simp]
theorem realize_is_emptyset' [ModelEmptyset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsEmptyset.Realize s xs ↔ ExtIsEmptyset (s 0) := by
  rw [intIsEmptyset, ExtIsEmptyset]
  simp [snoc_conv]

@[simp]
theorem realize_is_emptyset'' [ModelEmptyset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (t : LZFC.Term (ℕ ⊕ Fin n)) :
    (intIsEmptyset' t).Realize s xs ↔ ExtIsEmptyset (t.realize (Sum.elim s xs)) := by
  rw [intIsEmptyset', ExtIsEmptyset]
  simp

/-- The emptyset exists. -/
theorem ext_emptyset_exists [ModelEmptyset V] : ∃ (emp : V), ExtIsEmptyset emp := by
  let s : ℕ → V := default
  obtain ⟨e, h_e⟩ := realize_ex.mp (ModelEmptyset.emptyset_exists s default)
  use e
  simp at h_e
  have h1 : (0 : Fin 1) = Fin.last 0 := by
    rfl
  rw [h1] at h_e
  rw [snoc_last] at h_e
  exact h_e

/-- The emptyset is unique. -/
theorem ext_emptyset_unique [ModelEmptyset V] {a b : V} :
    ExtIsEmptyset a → ExtIsEmptyset b → a = b := by
  intro h_a h_b
  apply ModelSets.extensionality
  intro z
  constructor
  · intro h_za
    absurd h_za
    apply h_a z
  · intro h_zb
    absurd h_zb
    apply h_b z

/-- The emptyset is unique internally. -/
theorem int_emptyset_unique [ModelEmptyset V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}:
(∀'∀'(intIsEmptyset' (bv' 0) ⟹ intIsEmptyset' (bv' 1) ⟹ bv' 0 =' bv' 1)).Realize s xs := by
  apply realize_all.mpr
  intro a
  apply realize_all.mpr
  intro b
  simp [snoc_conv]
  apply ext_emptyset_unique

section Pairing

/-- Describe fv 1 is a singleton of fv 0. -/
def intIsSingleton {n : ℕ} : LZFC.BoundedFormula ℕ n := ∀'(bv'' n ∈' fv' 1⇔ bv'' n =' fv (n+1) 0)
/-- Describe fv 2 is an unordered pair of fv 0 and fv 1. -/
def intIsPair {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  ∀'(bv'' n ∈' fv' 2⇔ bv'' n =' fv' 0 ∨' bv'' n =' fv' 1)

/-- Describe t₂ is a singleton of t₁. -/
def intIsSingleton' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsSingleton.replaceFV (makeTsN ![t₁, t₂])
/-- Describe t₃ is an unordered pair of t₁ and t₂. -/
def intIsPair' {n : ℕ} (t₁ t₂ t₃ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsPair.replaceFV (makeTsN ![t₁, t₂, t₃])

/-- Model with a pairing axiom. -/
class ModelPairing (V : Type u) extends ModelSets V where
  pairing : ∀ (s : ℕ → V), ∀ (xs : Fin 0 → V), (∀' ∀' ∃'
  (intIsPair.liftAndReplaceFV 3 0 ![bv 3 0, bv 3 1, bv 3 2])).Realize s xs

/-- Describe b is a singleton of a. -/
def ExtIsSingleton [ModelPairing V] (a b : V) : Prop := ∀ (x : V), (x ∈ b) ↔ (x = a)

/-- Describe c is an unordered pair of a and b. -/
def ExtIsPair [ModelPairing V] (a b c : V) : Prop := ∀ (x : V), (x ∈ c) ↔ (x = a ∨ x = b)

@[simp]
theorem realize_is_singleton [ModelPairing V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsSingleton.Realize s xs ↔
    ExtIsSingleton (s 0) (s 1) := by
  rw [intIsSingleton, ExtIsSingleton]
  apply forall_congr'
  intro x
  simp

@[simp]
theorem realize_is_singleton' [ModelPairing V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
    (intIsSingleton' t₁ t₂).Realize s xs ↔
    ExtIsSingleton (t₁.realize (Sum.elim s xs)) (t₂.realize (Sum.elim s xs)) := by
  rw [intIsSingleton']
  unfold makeTsN
  simp

@[simp]
theorem realize_is_pair [ModelPairing V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsPair.Realize s xs ↔ ExtIsPair (s 0) (s 1) (s 2) := by
  rw [intIsPair, ExtIsPair]
  simp

/-- Pairing Axiom described externally. -/
theorem ext_pairing [ModelPairing V] [ModelPairing V] (a b : V) :
    ∃ (c : V), ExtIsPair a b c := by
  let s : ℕ → V := default
  let h0 := ModelPairing.pairing s default
  simp [realize_liftAt'] at h0
  obtain ⟨c, h_c⟩:= h0 a b
  use c

/-- The singleton is unique. -/
theorem ext_singleton_unique [ModelPairing V] {a b b' : V} :
    ExtIsSingleton a b → ExtIsSingleton a b' → b = b' := by
  intro h_b
  intro h_b'
  apply ModelSets.extensionality
  intro z
  apply Iff.trans (h_b z) (h_b' z).symm

/-- {a} = {b} implies a = b. -/
theorem ext_singleton_inj [ModelPairing V] {a a' b : V} :
    ExtIsSingleton a b → ExtIsSingleton a' b → a = a' := by
  rw [ExtIsSingleton, ExtIsSingleton]
  intro h_a
  intro h_a'
  have h1 : a = a ↔ a =a' := by
    apply Iff.trans (h_a a).symm (h_a' a)
  apply h1.mp rfl

/-- {a, a} = {a}. -/
theorem singleton_by_pair [ModelPairing V] {a b : V} :
    ExtIsSingleton a b ↔ ExtIsPair a a b := by
  constructor
  · intro h_singleton
    rw [ExtIsSingleton] at h_singleton
    rw [ExtIsPair]
    intro x
    rw [h_singleton x]
    apply or_self_iff.symm
  · rw [ExtIsSingleton, ExtIsPair]
    intro h_pair
    intro x
    rw [h_pair]
    apply or_self_iff

theorem ext_pair_unique [ModelPairing V] {a b c c' : V} :
    (ExtIsPair a b c) → (ExtIsPair a b c') → c = c' := by
  intro h_c
  intro h_c'
  rw [ExtIsPair] at h_c
  rw [ExtIsPair] at h_c'
  apply ModelSets.extensionality
  intro z
  apply Iff.trans (h_c z) (h_c' z).symm

theorem ext_pairing_inj [ModelPairing V] {a b a' b' c : V} :
    (ExtIsPair a b c) → (ExtIsPair a' b' c) → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  intro h_abc h_abc'
  have h0 : ∀ x, x = a ∨ x = b ↔ x = a' ∨ x = b' := by
    intro x
    apply Iff.trans (h_abc x).symm (h_abc' x)
  have h0_a : a = a' ∨ a = b' := by
    apply (h0 a).mp (Or.inl rfl)
  have h0_a' : a' = a ∨ a' = b := by
    apply (h0 a').mpr (Or.inl rfl)
  have h0_b : b = a' ∨ b = b' := by
    apply (h0 b).mp (Or.inr rfl)
  have h0_b' : b' = a ∨ b' = b := by
    apply (h0 b').mpr (Or.inr rfl)
  by_cases h_a_eq_a' : a = a'
  · by_cases h_b_eq_b' : b = b'
    · left
      apply And.intro h_a_eq_a' h_b_eq_b'
    · have h1 : b = a' := by
        apply Or.resolve_right h0_b h_b_eq_b'
      have h2 : b' = a := by
        apply Or.resolve_right h0_b' (Ne.symm h_b_eq_b')
      absurd h_b_eq_b'
      rw [h1, h_a_eq_a'.symm, h2.symm]
  · by_cases h_b_eq_b' : b = b'
    · have h1 : a = b' := by
        apply Or.resolve_left h0_a h_a_eq_a'
      have h2 : a' = b := by
        apply Or.resolve_left h0_a' (Ne.symm h_a_eq_a')
      absurd h_a_eq_a'
      rw [h1, h_b_eq_b'.symm, h2.symm]
    · right
      constructor
      · apply symm
        apply Or.resolve_right h0_b' (Ne.symm h_b_eq_b')
      · apply Or.resolve_right h0_b h_b_eq_b'

theorem ext_singleton [ModelPairing V] : ∀ (a : V), ∃ (b : V), ExtIsSingleton a b := by
  intro a
  have h_pick : ∃ (b : V), ExtIsPair a a b := by
    apply ext_pairing
  obtain ⟨b, hb⟩ := h_pick
  use b
  rw [singleton_by_pair]
  exact hb

/-- {a} = {b, c} implies a=b=c. -/
theorem singleton_eq_pair [ModelPairing V] {a b c x : V} :
    ExtIsSingleton a x → ExtIsPair b c x → a = b ∧ a = c := by
  intro h_a h_bc
  have h1 : (a = b ∧ a = c) ∨ (a = c ∧ a = b) := by
    apply ext_pairing_inj
    apply singleton_by_pair.mp
    apply h_a
    apply h_bc
  rcases h1 with h1l | h1r
  · exact h1l
  · exact h1r.symm

/-- Describe fv 2 is an ordered pair of fv 0 and fv 1. -/
def intIsOrderedPair {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  ∀'(bv'' n ∈' fv' 2 ⇔
  (intIsSingleton.liftAndReplaceFV 1 0 ![fv' 0, bv'' n]
  ∨' intIsPair.liftAndReplaceFV 1 0 ![fv' 0, fv' 1, bv'' n]))

/-- Describe c is an ordered pair of a and b. -/
def ExtIsOrderedPair [ModelPairing V] (a b c : V) :=
  ∀ (x : V), (x ∈ c) ↔ (ExtIsSingleton a x) ∨ (ExtIsPair a b x)

@[simp]
theorem realize_is_ordered_pair [ModelPairing V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsOrderedPair.Realize s xs ↔
    ExtIsOrderedPair (s 0) (s 1) (s 2) := by
  rw [intIsOrderedPair, ExtIsOrderedPair]
  simp [realize_liftAt']

/-- The ordered pair exists. -/
theorem ext_ordered_pair [ModelPairing V] (a b : V) : ∃ (c : V), ExtIsOrderedPair a b c := by
  obtain ⟨d1, h_d1⟩ := ext_singleton a
  obtain ⟨d2, h_d2⟩ := ext_pairing a b
  obtain ⟨c, h_c⟩ := ext_pairing d1 d2
  use c
  rw [ExtIsOrderedPair]
  intro x
  rw [h_c x]
  have h_d1' : x = d1 ↔ ExtIsSingleton a x := by
    constructor
    · intro h1
      rw [h1]
      exact h_d1
    · intro h1
      apply ext_singleton_unique h1 h_d1
  have h_d2' : x=d2 ↔ ExtIsPair a b x := by
    constructor
    · intro h1
      rw [h1]
      exact h_d2
    · intro h1
      apply ext_pair_unique h1 h_d2
  rw [h_d1', h_d2']

theorem ext_ordered_pair_unique [ModelPairing V] (a b c c' : V) :
    ExtIsOrderedPair a b c → ExtIsOrderedPair a b c' → c = c' := by
  intro h_c h_c'
  apply ModelSets.extensionality
  intro z
  rw [ExtIsOrderedPair] at h_c
  rw [ExtIsOrderedPair] at h_c'
  apply Iff.trans (h_c z) (h_c' z).symm

theorem ext_ordered_pair_inj [ModelPairing V] (a b a' b' c : V) :
    ExtIsOrderedPair a b c → ExtIsOrderedPair a' b' c → a = a' ∧ b = b' := by
  rw [ExtIsOrderedPair, ExtIsOrderedPair]
  intro h_ab
  intro h_ab'
  have h0 : ∀ (x : V), ExtIsSingleton a x ∨ ExtIsPair a b x ↔
      ExtIsSingleton a' x ∨ ExtIsPair a' b' x := by
    intro x
    apply Iff.trans (h_ab x).symm (h_ab' x)
  by_cases h_a_eq_b : a = b
  · rw [h_a_eq_b]
    rw [h_a_eq_b] at h0
    obtain ⟨sb, h_sb⟩ := ext_singleton b
    have h0_sb : ExtIsSingleton a' sb ∨ ExtIsPair a' b' sb := by
      apply (h0 sb).mp
      apply Or.inl h_sb
    rcases h0_sb with h0_sbl | h0_sbr
    · have h1 : b = a' := by
        apply ext_singleton_inj h_sb h0_sbl
      rw [h1.symm] at h0_sbl
      rw [h1.symm] at h0
      constructor
      · exact h1
      · obtain ⟨pbb', h_pbb'⟩ := ext_pairing b b'
        have h2 : ExtIsSingleton b pbb' ∨ ExtIsPair b b pbb' := by
          apply (h0 pbb').mpr
          apply Or.inr h_pbb'
        rcases h2 with h2l | h2r
        · have h3 : b = b ∧ b = b' := by
            apply singleton_eq_pair h2l h_pbb'
          apply h3.right
        · have h3 : ((b = b)∧(b = b'))∨(b = b'∧ b =b):= by
            apply ext_pairing_inj h2r h_pbb'
          rcases h3 with h3l | h3r
          · apply h3l.right
          · apply h3r.left
    · apply singleton_eq_pair h_sb h0_sbr
  · obtain ⟨sa, h_sa⟩ := ext_singleton a
    have h0_sa : ExtIsSingleton a' sa ∨ ExtIsPair a' b' sa := by
      apply (h0 sa).mp
      apply Or.inl h_sa
    have h1 : a = a' := by
      rcases h0_sa with h0_sa_l | h0_sa_r
      · apply ext_singleton_inj h_sa h0_sa_l
      · have h1 : a = a' ∧ a = b' := by
          apply singleton_eq_pair h_sa h0_sa_r
        apply h1.left
    constructor
    · exact h1
    · obtain ⟨pab, h_pab⟩ := ext_pairing a b
      have h0_pab : ExtIsSingleton a' pab ∨ ExtIsPair a' b' pab := by
        apply (h0 pab).mp
        apply Or.inr h_pab
      rcases h0_pab with h0_pab_l | h0_pab_r
      · absurd h_a_eq_b
        have h2 : a' = a ∧ a' = b := by
          apply singleton_eq_pair h0_pab_l h_pab
        rw [h2.left.symm, h2.right]
      · have h3: (a = a'∧ b = b')∨(a = b' ∧ b = a') := by
          apply ext_pairing_inj h_pab h0_pab_r
        rcases h3 with h3l | h3r
        · apply h3l.right
        · rw [h3r.right, h1.symm, h3r.left]

theorem int_ordered_pair_inj [ModelPairing V] (s : ℕ → V) (xs : Fin 0 → V) : (∀'∀'∀'∀'∀'(
  intIsOrderedPair.liftAndReplaceFV 5 0 ![bv 5 0, bv 5 1, bv 5 4]
  ⟹ intIsOrderedPair.liftAndReplaceFV 5 0 ![bv 5 2, bv 5 3, bv 5 4]
  ⟹ bv 5 0 =' bv 5 2 ∧' bv 5 1 =' bv 5 3)).Realize s xs := by
  simp [realize_liftAt']
  intro a₁ a₂ a₃ a₄ a₅
  apply ext_ordered_pair_inj

class ModelEP (V : Type u) extends ModelEmptyset V, ModelPairing V

theorem ext_singleton_of_emptyset [ModelEP V] : ∀ (e : V),
    ExtIsEmptyset e → ∃ (a : V), ExtIsSingleton e a := by
  intro e he
  obtain ⟨a, ha⟩ := ext_singleton e
  use a

theorem int_singleton_of_emptyset [ModelEP V] (s : ℕ → V) (xs : Fin 0 → V) :
    (∀'(intIsEmptyset.liftAndReplaceFV 1 0 ![bv 1 0]
    ⟹∃'(intIsSingleton.liftAndReplaceFV 2 0 ![bv 2 0, bv 2 1]))).Realize s xs := by
  simp [realize_liftAt']
  intro e he
  obtain ⟨a, ha⟩ := ext_singleton_of_emptyset e he
  use a

end Pairing

section Union

/-- Describe fv 1 is the union of fv 0 (in the set-theoretic sense). -/
def intIsUnion {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  ∀'(bv'' n ∈' fv' 1 ⇔ ∃'(bv'' n ∈' bv'' (n+1) ∧' bv'' (n+1) ∈' fv' 0))


/-- Describe t₂ is the union of t₁ (in the set-theoretic sense). -/
def intIsUnion' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsUnion.replaceFV (makeTsN ![t₁, t₂])

/-- Desdribe b is an union of a. -/
def ExtIsUnion [ModelSets V] (a b : V) := ∀ (x : V),
  (x ∈ b ↔ ∃ (c : V), (x ∈ c ∧ c ∈ a))

/-- Model with the Union axiom. -/
class ModelUnion (V : Type u) extends ModelSets V where
  union_exists : ∀ (s : ℕ → V), ∀ (xs : Fin 0 → V),
  (∀'∃'(intIsUnion.liftAndReplaceFV 2 0 ![bv' 0, bv' 1])).Realize s xs

class ModelEPU (V : Type u) extends ModelEmptyset V, ModelPairing V, ModelUnion V

@[simp]
theorem realize_is_union [ModelUnion V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsUnion.Realize s xs ↔ ExtIsUnion (s 0) (s 1)  := by
  rw [intIsUnion, ExtIsUnion]
  simp

theorem union_of_ordered_pair [ModelEPU V] {a b c d : V} :
    ExtIsOrderedPair a b c → ExtIsUnion c d → ExtIsPair a b d := by
  intro h_abc
  intro h_cd
  rw [ExtIsPair]
  rw [ExtIsUnion] at h_cd
  rw [ExtIsOrderedPair] at h_abc
  intro x
  constructor
  · intro h_xd
    have h1 : ∃ y, x ∈ y ∧ y ∈ c := by
      apply (h_cd x).mp
      exact h_xd
    obtain ⟨y, h_y⟩ := h1
    have h2 : ExtIsSingleton a y ∨ ExtIsPair a b y := by
      apply (h_abc y).mp h_y.right
    rcases h2 with h2l | h2r
    · rw [ExtIsSingleton] at h2l
      left
      apply (h2l x).mp h_y.left
    · rw [ExtIsPair] at h2r
      apply (h2r x).mp h_y.left
  · intro h_xab
    rcases h_xab with h_a | h_b
    · apply (h_cd x).mpr
      obtain ⟨y, h_y⟩ := ext_singleton a
      use y
      constructor
      · rw [h_a]
        rw [ExtIsSingleton] at h_y
        apply (h_y a).mpr rfl
      · apply (h_abc y).mpr (Or.inl h_y)
    · apply (h_cd x).mpr
      obtain ⟨y, h_y⟩ := ext_pairing a b

      use y
      constructor
      · rw [ExtIsPair] at h_y
        apply (h_y x).mpr (Or.inr h_b)
      · apply (h_abc y).mpr (Or.inr h_y)

theorem int_union_of_ordered_pair [ModelEPU V] {s : ℕ → V} {xs : Fin 0 → V} :
    (∀'∀'∀'∀'(intIsOrderedPair.liftAndReplaceFV 4 0 ![bv' 0, bv' 1, bv' 2]
    ⟹ intIsUnion.liftAndReplaceFV 4 0 ![bv' 2, bv' 3]
    ⟹ intIsPair.liftAndReplaceFV 4 0 ![bv' 0, bv' 1, bv' 3])).Realize s xs := by
  simp [realize_liftAt']
  intro a b c d
  apply union_of_ordered_pair

end Union

section Powerset

/-- Make a formula fv 0 ⊆ fv 1. -/
def intIsSubset {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  (∀'(bv'' n ∈' fv (n+1) 0 ⟹ bv'' n ∈' fv (n+1) 1))

/-- Make a formula t1 ⊆ t2. -/
def intIsSubset' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsSubset.replaceFV (makeTsN ![t₁, t₂])

@[inherit_doc] infixl : 120 " ⊆' " => intIsSubset'

/-- Make a formula t1 ⊈ t2. -/
def intNotIsSubset' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n:= ∼(intIsSubset' t₁ t₂)

@[inherit_doc] infixl : 120 " ⊈' " => intNotIsSubset'

/-- a is a subset of b. -/
def ExtIsSubset [ModelSets V] (a b : V) := ∀ (x : V), (x ∈ a → x ∈ b)
/-- a is not a subset of b. -/
def ExtNotIsSubset [ModelSets V] (a b : V) := ¬ ∀ (x : V), (x ∈ a → x ∈ b)
infixl : 50 " ⊆ " => ExtIsSubset
infixl : 50 " ⊈ " => ExtNotIsSubset

/-- Make a formula that fv 0 is a subset of fv 1. -/
def intIsPowerset {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  ∀'(intIsSubset.liftAndReplaceFV 1 0 ![bv'' n, fv' 0] ⇔ bv'' n ∈' fv' 1)

/-- Make a formula that t₂ is a powerset of t₁. -/
def intIsPowerset' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :=
  intIsPowerset.replaceFV (makeTsN ![t₁, t₂])

/-- Describe b is a powerset of a. -/
def ExtIsPowerset [ModelSets V] (a b : V) := ∀ (x : V),
  (ExtIsSubset x a) ↔ x ∈ b

/-- Model with the Powerset Axiom. -/
class ModelPowerset (V : Type u) extends ModelSets V where
  powerset_exists : ∀ (s : ℕ → V), ∀ (xs : Fin 0 → V),
  (∀'∃'(intIsPowerset.liftAndReplaceFV 2 0 ![bv 2 0, bv 2 1])).Realize s xs

class ModelEPUP (V : Type u) extends ModelEmptyset V, ModelPairing V, ModelUnion V, ModelPowerset V

@[simp]
theorem realize_is_subset [ModelPowerset V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) :
intIsSubset.Realize s xs ↔ ExtIsSubset (s 0) (s 1) := by
  rw [intIsSubset, ExtIsSubset]
  simp

@[simp]
theorem realize_is_subset' [ModelPowerset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)): (t₁ ⊆' t₂).Realize s xs ↔
    ExtIsSubset (t₁.realize (Sum.elim s xs)) (t₂.realize (Sum.elim s xs)) := by
  unfold intIsSubset' makeTsN intIsSubset ExtIsSubset
  simp

@[simp]
theorem realize_is_powerset [ModelPowerset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsPowerset.Realize s xs ↔ ExtIsPowerset (s 0) (s 1) := by
  rw [intIsPowerset, ExtIsPowerset]
  unfold intIsSubset ExtIsSubset
  simp [realize_liftAt']

@[simp]
theorem realize_is_powerset' [ModelPowerset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
    (intIsPowerset' t₁ t₂).Realize s xs ↔
    ExtIsPowerset (t₁.realize (Sum.elim s xs)) (t₂.realize (Sum.elim s xs)) := by
  rw [intIsPowerset']
  unfold makeTsN
  simp

theorem subset_self [ModelEPUP V] : ∀ (a : V), a ⊆ a := by
  intro a
  rw [ExtIsSubset]
  intro x
  simp

theorem int_subset_self [ModelEPUP V] {s : ℕ → V} {xs : Fin 0 → V} : (∀'
(bv 1 0 ⊆' bv 1 0)).Realize s xs := by
  simp
  apply subset_self

/-- P(∅)={∅} -/
theorem powerset_of_emptyset [ModelEPUP V]: ∀ (emp a: V),
    ExtIsEmptyset emp → ExtIsPowerset emp a → ExtIsSingleton emp a:= by
  intro emp a
  rw [ExtIsPowerset, ExtIsSingleton]
  intro h_emp h_powerset
  intro x
  rw [(h_powerset x).symm]
  constructor
  · rw [ExtIsSubset]
    intro h1
    apply ModelSets.extensionality
    intro z
    constructor
    · apply h1 z
    · intro h_z
      absurd h_z
      apply h_emp
  · intro h1
    rw [h1]
    apply subset_self

/-- P(∅)={∅} internally. -/
theorem int_powerset_of_emptyset [ModelEPUP V] {s : ℕ → V}
    {xs : Fin 0 → V} : (∀'∀'(intIsEmptyset' (bv' 0) ⟹
    intIsPowerset' (bv' 0) (bv' 1) ⟹ intIsSingleton' (bv' 0) (bv' 1))).Realize s xs:= by
  simp
  intro emp a
  apply powerset_of_emptyset

end Powerset

section Infinity

/-- Make a formula for fv 1 is a successor of fv 0. -/
def intIsSuccessor {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  (∀'(bv'' n ∈' fv' 1 ⇔ (bv'' n ∈' fv' 0 ∨' bv'' n =' fv' 0)))
/-- Make a formula for t₂ is a successor of t₁-. -/
def intIsSuccessor' {n : ℕ} (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n:= intIsSuccessor.replaceFV (makeTsN ![t₁, t₂])

def ExtIsSuccessor [ModelSets V] (a b : V) := ∀ (x : V), x ∈ b ↔ (x ∈ a ∨ x = a)

@[simp]
theorem realize_is_successor [ModelPowerset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) : intIsSuccessor.Realize s xs ↔
    ExtIsSuccessor (s 0) (s 1) := by
  rw [intIsSuccessor, ExtIsSuccessor]
  simp

@[simp]
theorem realize_is_successor' [ModelPowerset V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n)) :
    (intIsSuccessor' t₁ t₂).Realize s xs ↔
    ExtIsSuccessor (Term.realize (Sum.elim s xs) t₁)
    (Term.realize (Sum.elim s xs) t₂) := by
  rw [intIsSuccessor']
  unfold makeTsN
  simp

/-- Make a formula for fv 0 is inductive, i.e., ∅∈fv 0 and x∈fv 0 implies S(x)∈fv 0. -/
def intIsInductive {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  (∀'(intIsEmptyset' (bv'' n) ⟹ (bv'' n ∈' fv' 0))) ∧'
  (∀'(bv'' n ∈' fv' 0 ⟹ ∀'(intIsSuccessor' (bv'' n)
  (bv'' (n+1)) ⟹ bv'' (n+1) ∈' fv' 0)))

/-- Make a formula for t is inductive. -/
def intIsInductive' {n : ℕ} (t : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsInductive.replaceFV (makeTsN ![t])

/-- Describe a is inductive. -/
def ExtIsInductive [ModelEmptyset V] (a : V) := (∀ (emp : V),
  ExtIsEmptyset emp → emp ∈ a) ∧ (∀ (x : V), x ∈ a → ∀ (y : V),
  ExtIsSuccessor x y → y ∈ a)

@[simp]
theorem realize_is_inductive [ModelEPUP V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) :  intIsInductive.Realize s xs ↔ ExtIsInductive (s 0) := by
  rw [intIsInductive, ExtIsInductive]
  simp

@[simp]
theorem realize_is_inductive' [ModelEPUP V] {n : ℕ} (s : ℕ → V)
  (xs : Fin n → V) (t : LZFC.Term (ℕ ⊕ Fin n)) :
  (intIsInductive' t).Realize s xs ↔
  (ExtIsInductive (Term.realize (Sum.elim s xs) t)) := by
  rw [intIsInductive']
  unfold makeTsN
  simp

/-- ∅ belongs to every inductive set. -/
theorem ext_emp_in_inductive [ModelEPUP V] {emp a : V} :
    ExtIsEmptyset emp → ExtIsInductive a → emp ∈ a := by
  intro h_emp h_a
  unfold ExtIsInductive at h_a
  apply h_a.left emp h_emp

/-- If a is inductive and x∈a, then S(x)∈a. -/
theorem ext_inductive_one_step [ModelEPUP V] {a y : V} (x : V) :
  ExtIsInductive a → x ∈ a → ExtIsSuccessor x y → y ∈ a := by
  intro h_a h_xa h_xy
  unfold ExtIsInductive at h_a
  apply h_a.right x h_xa y h_xy

/-- Model with the Infinity axiom. -/
class ModelInfinity (V : Type u) extends ModelSets V where
  infinity_exists : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V),
  (∃'intIsInductive' (bv'' n)).Realize s xs

class ModelEPUPI (V : Type u) extends ModelEPUP V, ModelInfinity V

/-- The exitetence of an infinite set described externally. -/
theorem ext_infinity_exists [ModelEPUPI V]: ∃ (x : V), ExtIsInductive x := by
  let s : ℕ → V := default
  let xs : Fin 0 → V := default
  obtain ⟨x, h_x⟩ := realize_ex.mp (ModelInfinity.infinity_exists s xs)
  use x
  simp at h_x
  exact h_x

end Infinity

section Regularity

/-- Make a formula for the Regularity Axiom. -/
def intRegularity {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  (∀'(
    (∃'(bv'' (n+1))∈'(bv'' n))
    ⟹ (∃'((bv'' (n+1))∈'(bv'' n)
        ∧' ∀'((bv'' (n+2))∈'(bv'' n)
            ⟹ (bv'' (n+2))∉'(bv'' (n+1)))))))

/-- Model with the Regularity Axiom. -/
class ModelRegularity (V : Type u) extends ModelSets V where
  regularity : ∀ (s : ℕ → V), ∀ (xs : Fin 0 → V), intRegularity.Realize s xs

class ModelEPUPIR (V : Type u) extends ModelEPUPI V, ModelRegularity V

/-- The Regularity axiom described externally. -/
theorem ExtRegularity [ModelEPUPIR V] (a : V) : (∃ (b : V), b ∈ a) →
    (∃ (b : V), b ∈ a ∧ ∀ (c : V), (c ∈ a → c ∉ b)) := by
  let s : ℕ → V := default
  let xs : Fin 0 → V := default
  let h := ModelRegularity.regularity s xs
  unfold intRegularity at h
  simp at h
  intro h_nonempty
  obtain ⟨b', h_b'⟩ := h_nonempty
  obtain ⟨b, h_b⟩ := (h a b') h_b'
  use b

/-- No set satisfies a∈a. -/
theorem no_loop [ModelEPUPIR V] (a : V) : a ∉ a := by
  obtain ⟨a_sing, h_a_sing⟩ := ext_singleton a
  unfold ExtIsSingleton at h_a_sing
  have a_sing_nonempty : ∃ (b : V), b ∈ a_sing := by
    use a
    apply (h_a_sing a).mpr rfl
  obtain ⟨b, h_b⟩ := ExtRegularity a_sing a_sing_nonempty
  have h1 : b = a := by
    apply (h_a_sing b).mp h_b.left
  rw [← h1]
  apply h_b.right b
  apply (h_a_sing b).mpr
  exact h1

/-- No set satisfies a∈a internally. -/
theorem int_no_loop [ModelEPUPIR V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V) :
    (∀'bv'' n ∉' bv'' n).Realize s xs := by
  simp
  apply no_loop

end Regularity

section Comprehension

/-- t = {x∈(bv n) : ϕ}. -/
def intIsSeparation {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
  LZFC.BoundedFormula ℕ n := (∀'((bv'' n ∈' fv' 1) ⇔
  (bv'' n ∈' fv' 0 ∧' ϕ.liftAndReplaceFV 1 n ![bv'' n])))
def intIsSeparation' {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) (n' : ℕ)
  (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin (n + n'))) : LZFC.BoundedFormula ℕ (n + n') :=
  (∀'(bv'' (n+n') ∈' t₂.liftAt 1 (n+n') ⇔
  (bv'' (n+n') ∈' t₁.liftAt 1 (n+n') ∧' ϕ.liftAndReplaceFV (n'+1) n ![bv'' (n+n')])))

def ExtIsSeparation [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) : Prop := ∀ (x : V),
  (x ∈ b) ↔ (x ∈ a ∧ ϕ.Realize (replaceInitialValues s ![x]) xs)

@[simp]
theorem realize_separation [ModelSets V] {n : ℕ} (s : ℕ → V)
  (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) :
  (intIsSeparation ϕ).Realize s xs ↔ ExtIsSeparation s xs ϕ (s 0) (s 1) := by
  unfold intIsSeparation ExtIsSeparation
  simp

theorem FirstOrder.Language.Term.liftAt_zero {n m : ℕ}
    (t : LZFC.Term (ℕ ⊕ Fin n)) : Term.liftAt 0 m t = t := by
  unfold Term.liftAt
  have h1 : (Sum.map id fun (i : Fin n) ↦ if ↑i < m then Fin.castAdd 0 i
      else i.addNat 0) = @id (ℕ ⊕ Fin n) := by
    funext i
    rcases i with k | k
    · simp
    · simp
  rw [h1]
  apply FirstOrder.Language.Term.relabel_id

theorem FirstOrder.Language.BoundedFormula.liftAt_zero {n m : ℕ}
    (ϕ : LZFC.BoundedFormula ℕ n) : liftAt 0 m ϕ = ϕ := by
  unfold liftAt
  induction' ϕ with _n _n t₁ t₂ _n _l _R _ts _n _f₁ _f₂ _f₁_ih _f₂_ih _n _f _f_ih
  · unfold mapTermRel
    rfl
  · unfold mapTermRel
    simp [FirstOrder.Language.Term.liftAt_zero]
  · unfold mapTermRel
    simp [FirstOrder.Language.Term.liftAt_zero]
  · unfold mapTermRel
    rw [_f₁_ih, _f₂_ih]
  · unfold mapTermRel
    simp
    apply _f_ih

@[simp]
theorem realize_separation'_no_lift [ModelSets V] {n : ℕ}
    (ϕ : LZFC.BoundedFormula ℕ n) (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin n))
    (s : ℕ → V) (xs : Fin n → V) : (intIsSeparation' ϕ 0 t₁ t₂).Realize s xs ↔
    ExtIsSeparation s xs ϕ (t₁.realize (Sum.elim s xs))
    (t₂.realize (Sum.elim s xs)):= by
  unfold intIsSeparation' ExtIsSeparation
  simp

@[simp]
theorem realize_separation'_lift [ModelSets V] {n : ℕ}
    (ϕ : LZFC.BoundedFormula ℕ n) (n' : ℕ) (h_n' : n' > 0)
    (t₁ t₂ : LZFC.Term (ℕ ⊕ Fin (n + n'))) (s : ℕ → V)
    (xs : Fin (n + n') → V) : (intIsSeparation' ϕ n' t₁ t₂).Realize s xs ↔
    ExtIsSeparation s xs (ϕ.liftAt n' n) (t₁.realize (Sum.elim s xs))
    (t₂.realize (Sum.elim s xs)):= by
  unfold intIsSeparation' ExtIsSeparation
  simp
  apply forall_congr'
  intro x
  apply iff_congr
  · rfl
  · apply and_congr
    · rfl
    · simp [realize_liftAt']
      have h1 : (liftAt n' n ϕ).Realize (replaceInitialValues s ![x]) xs ↔
          ϕ.Realize (replaceInitialValues s ![x])
          (xs ∘ fun i ↦ if ↑i < n then Fin.castAdd n' i else i.addNat n') := by
        rw [realize_liftAt']
        · omega
        · omega
      rw [h1]
      simp

theorem lift_ExtIsSeparation [ModelSets V] {n n' : ℕ} {h_n' : n' > 0}
    {s : ℕ → V} {xs : Fin (n + n') → V} {ϕ : LZFC.BoundedFormula ℕ n}
    {a b : V} : ExtIsSeparation s xs (ϕ.liftAt n' n) a b ↔
    ExtIsSeparation s (fun (k : Fin n) ↦ xs (k.castAdd n')) ϕ a b := by
  unfold ExtIsSeparation
  apply forall_congr'
  intro x
  apply iff_congr
  · rfl
  · apply and_congr
    · rfl
    · rw [realize_liftAt']
      · simp
        rfl
      · omega
      · omega

/-- Model with the Comprehension schema. -/
class ModelComprehension (V : Type u) extends ModelSets V where
  comprehension_schema : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
  (ϕ : LZFC.BoundedFormula ℕ n), (∀'∃'(intIsSeparation' ϕ 2 (bv'' n)
  (bv'' (n+1)))).Realize s xs

/-- The Comprehension schema described externally. -/
theorem ext_comprehension [ModelComprehension V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) (a : V) :
    ∃ (b : V), ExtIsSeparation s xs ϕ a b := by
  obtain ⟨b, h_b⟩ := realize_ex.mp (ModelComprehension.comprehension_schema s xs ϕ a)
  use b
  simp at h_b
  have h_2_gt_0 : 2 > 0 := by omega
  have h1 : ExtIsSeparation s (fun (k : Fin n) ↦
      (fixedSnoc (fixedSnoc xs a) b) (k.castAdd 2)) ϕ a b := by
    apply lift_ExtIsSeparation.mp h_b
    omega
  simp at h1
  exact h1

class ModelEPUPIC (V : Type u) extends ModelEPUPI V, ModelComprehension V

/-- Make a formula for fv 0 is ω. -/
def intIsOmega {n : ℕ} : LZFC.BoundedFormula ℕ n :=
  intIsInductive ∧' (∀'(intIsInductive.replaceFV (makeTsN ![bv'' n]) ⟹
  fv' 0 ⊆' bv'' n))

/-- Make a formula for t is ω. -/
def intIsOmega' {n : ℕ} (t : LZFC.Term (ℕ ⊕ Fin n)) :
  LZFC.BoundedFormula ℕ n := intIsOmega.replaceFV (makeTsN ![t])

/-- Describe a is ω. -/
def ExtIsOmega [ModelEPUPI V] (a : V) := ExtIsInductive a ∧
  (∀ (b : V), ExtIsInductive b → a ⊆ b)

@[simp]
theorem realize_is_omega [ModelEPUPI V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} : intIsOmega.Realize s xs ↔ ExtIsOmega (s 0)  := by
  rw [intIsOmega, ExtIsOmega]
  unfold makeTsN
  simp

@[simp]
theorem realize_is_omega' [ModelEPUPI V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} (t : LZFC.Term (ℕ ⊕ Fin n)) :
    (intIsOmega' t).Realize s xs ↔ ExtIsOmega (t.realize (Sum.elim s xs))  := by
  unfold intIsOmega'
  unfold makeTsN
  simp

theorem ext_omega_exists [ModelEPUPIC V] {n : ℕ} {s : ℕ → V}
    {xs : Fin n → V} : ∃ (omega : V), ExtIsOmega omega := by
  obtain ⟨a, h_a⟩ := realize_ex.mp (ModelInfinity.infinity_exists s xs)
  simp at h_a
  let ϕ : LZFC.BoundedFormula ℕ n :=
    ∀'(intIsInductive.replaceFV (makeTsN ![bv'' n]) ⟹ fv' 0 ∈' bv'' n)
  obtain ⟨b, h_b⟩ := ext_comprehension s xs ϕ a
  use b
  unfold ExtIsSeparation at h_b
  have h_realize_ϕ : ∀ (x : V), ϕ.Realize (replaceInitialValues s ![x]) xs ↔
      ∀ (c : V), ExtIsInductive c → x ∈ c := by
    intro x
    unfold ϕ
    simp
  have h_b' : ∀ (x : V), x ∈ b ↔ x∈ a ∧ ∀ (c : V), ExtIsInductive c → x ∈ c := by
    intro x
    rw [h_b]
    apply and_congr
    · rfl
    · apply h_realize_ϕ
  unfold ExtIsOmega
  constructor
  · unfold ExtIsInductive
    constructor
    · intro emp h_emp
      apply (h_b emp).mpr
      constructor
      · unfold ExtIsInductive at h_a
        apply h_a.left emp h_emp
      · unfold ϕ
        simp
        intro c h_c
        apply ext_emp_in_inductive h_emp h_c
    · intro x h_xb y h_xy
      apply (h_b y).mpr
      constructor
      · unfold ExtIsInductive at h_a
        apply h_a.right x
        · apply ((h_b x).mp h_xb).left
        · apply h_xy
      · apply (h_realize_ϕ y).mpr
        intro c h_c
        have h_x_in_c : x ∈ c := by
          apply ((h_b' x).mp h_xb).right c h_c
        apply ext_inductive_one_step x h_c h_x_in_c h_xy
  · intro c h_c
    intro x h_xb
    apply ((h_b' x).mp h_xb).right c h_c

theorem ext_omega_minus_emptyset [ModelEPUPIC V] :
    ∀ (emp : V), ExtIsEmptyset emp → ∀ (omega : V),
    ExtIsOmega omega → ∃ (b : V), ∀ (x : V), (x ∈ b ↔ (x ∈ omega ∧ x ≠ emp)) := by
  intro emp h_emp omega h_omega
  let s : ℕ → V := fun k => (default : V)
  let xs := ![emp, omega]
  let ϕ : LZFC.BoundedFormula ℕ 2 := ∼ (fv' 0 =' (bv' 0))
  obtain ⟨b, h_b⟩ := ext_comprehension s xs ϕ omega
  use b
  unfold ExtIsSeparation at h_b
  exact h_b

theorem int_omega_minus_emptyset [ModelEPUPIC V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V): (∀'∀'(intIsEmptyset' (bv'' n) ⟹
    intIsOmega' (bv'' (n+1)) ⟹ ∃'∀'(bv'' (n+3) ∈' bv'' (n+2) ⇔
    (bv'' (n+3) ∈' bv'' (n+1) ∧' bv'' (n+3) ≠' bv'' n)))).Realize s xs := by
  simp
  intro emp omega h_emp h_omega
  obtain ⟨b, h_b⟩ := ext_omega_minus_emptyset emp h_emp omega h_omega
  use b

theorem omega_closed_under_succ [ModelEPUPIC V] : ∀ (omega : V),
    ExtIsOmega omega → ∀ (x y : V), (x ∈ omega → ExtIsSuccessor x y →
    y ∈ omega) := by
  intro omega h_omega x y h_x_omega h_xy
  unfold ExtIsOmega ExtIsInductive at h_omega
  apply h_omega.left.right x h_x_omega y h_xy

/-- The principle of mathematical induction for ω. -/
theorem ext_induction [ModelEPUPIC V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    (ϕ : LZFC.BoundedFormula ℕ n) :
    (∀ (emp : V), ExtIsEmptyset emp
    → (∀ (omega : V), ExtIsOmega omega
    → ((ϕ.Realize (replaceInitialValues s ![emp]) xs)
    → ((∀ (x : V), ϕ.Realize (replaceInitialValues s ![x]) xs →
      ∀ (y : V), ExtIsSuccessor x y → ϕ.Realize (replaceInitialValues s ![y]) xs)
    → (∀ (x : V), x ∈ omega → ϕ.Realize (replaceInitialValues s ![x]) xs))))) := by
  intro emp h_emp
  intro omega h_omega
  intro h_basis
  intro h_inductive
  obtain ⟨b, h_b⟩ := ext_comprehension s xs ϕ omega
  have h1 : ExtIsInductive b := by
    unfold ExtIsInductive
    constructor
    · intro _emp _h_emp
      unfold ExtIsSeparation at h_b
      apply (h_b _emp).mpr
      constructor
      · unfold ExtIsOmega at h_omega
        unfold ExtIsInductive at h_omega
        apply h_omega.left.left _emp _h_emp
      · have h_emp_eq : _emp = emp := by
          apply ext_emptyset_unique
          exact _h_emp
          exact h_emp
        rw [h_emp_eq]
        exact h_basis
    · intro x h_xb y h1
      unfold ExtIsSeparation at h_b
      apply (h_b y).mpr
      constructor
      · have h_x_in_omega : x ∈ omega := by
          apply ((h_b x).mp h_xb).left
        apply omega_closed_under_succ omega h_omega x y h_x_in_omega h1
      · have h_ϕ_x : ϕ.Realize (replaceInitialValues s ![x]) xs := by
          apply ((h_b x).mp h_xb).right
        apply h_inductive x h_ϕ_x y h1
  intro x h_x
  unfold ExtIsOmega at h_omega
  have h2 : omega ⊆ b := by
    apply h_omega.right b h1
  unfold ExtIsSeparation at h_b
  have h3 : x ∈ b := by
    apply h2
    exact h_x
  apply ((h_b x).mp h3).right

theorem int_induction [ModelEPUPIC V] {n : ℕ} {s : ℕ → V} {xs : Fin n → V}
    (ϕ : LZFC.BoundedFormula ℕ n) :
    (∀'(intIsEmptyset' (bv'' n)
      ⟹ (∀' (intIsOmega' (bv'' (n+1))
        ⟹ (ϕ.liftAndReplaceFV 2 n ![bv'' n]
          ⟹ ((∀'(ϕ.liftAndReplaceFV 3 n ![bv'' (n+2)]
            ⟹ (∀'(intIsSuccessor' (bv'' (n+2)) (bv'' (n+3))
              ⟹ ϕ.liftAndReplaceFV 4 n ![bv'' (n+3)]))))
            ⟹ (∀'(bv'' (n+2) ∈' bv'' (n+1) ⟹
            ϕ.liftAndReplaceFV 3 n ![bv'' (n+2)])))))))).Realize s xs := by
  simp
  unfold makeTsN
  simp [realize_liftAt']
  intro emp h_emp
  intro omega h_omega
  intro h_basis
  intro h_inductive
  apply ext_induction
  · apply h_emp
  · apply h_omega
  · apply h_basis
  · apply h_inductive

end Comprehension

end ZFC
