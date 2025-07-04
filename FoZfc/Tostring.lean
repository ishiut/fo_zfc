import FoZfc.Basic
import FoZfc.BoundedFormulaOps

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

open ZFC

universe u v

variable {V : Type u}
variable {α : Type*}

#check toString

/-- Converts a term into a string-/
def TermToString [ToString α] {n : ℕ} (t : Language.LZFC.Term (α ⊕ Fin n)) :=
match t with
| Language.Term.var (Sum.inl a) => s!"fv{toString a}"
| Language.Term.var (Sum.inr k) => s!"bv{k}"
| _ => "error"

#eval TermToString (fv 0 0) --- Output: "fv0"

def t0 : Language.LZFC.Term ((List ℕ) ⊕ Fin 0) := Language.Term.var (Sum.inl [1, 2, 3])
#eval TermToString t0 --- Output : "fv[1, 2, 3]"

-- When k≥n, it returns TermToString (ts 0).
-- Probably, in that case, they go to the default value.
/-- Converts a tuple of terms into a string-/
def TermTupleToString [ToString α] {n : ℕ} {m : ℕ} (ts : Fin m → Language.LZFC.Term (α ⊕ Fin n)) (k : ℕ): String :=
  match m with
  | 0 => "error"
  | m' + 1 => TermToString (ts (Fin.ofNat' (m' + 1) k))

-- /-- Make a string for a tuple of terms-/
-- def TermTupleToString [ToString α] {n : ℕ} {m : ℕ} (ts : Fin (m + 1)→ Language.LZFC.Term (α ⊕ Fin n)) (k : ℕ): String :=
--   TermToString (ts (Fin.ofNat' (m + 1) k))

#check (fun {n : ℕ} (ts : Fin 2 → Language.LZFC.Term (ℕ ⊕ Fin n)) => Language.BoundedFormula.rel is_elt_of₂ ts)

#eval TermTupleToString ![fv 0 0, fv 0 1] 0
#eval TermTupleToString ![fv 2 0, fv 2 1] 0 --- Output: "fv0"
#eval TermTupleToString ![fv 2 0, fv 2 1] 1 --- Output: "fv1"
#eval TermTupleToString ![fv 2 0, fv 2 1] 2 --- Output: "fv0"



/-- Converts a formula into a string-/
def FormulaToString [ToString α] {n : ℕ} (ϕ : Language.LZFC.BoundedFormula α n) : String :=
match ϕ with
| Language.BoundedFormula.falsum => "⊥"
| Language.BoundedFormula.ex ϕ1 => s!"∃'bv{n}({FormulaToString ϕ1})"
| Language.BoundedFormula.all ϕ1 => s!"∀'bv{n}({FormulaToString ϕ1})"
| Language.BoundedFormula.or ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ∨ {FormulaToString ϕ2}"
| Language.BoundedFormula.and ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ∧ {FormulaToString ϕ2}"
| ∼ϕ1 => s!"∼{FormulaToString ϕ1}"
| Language.BoundedFormula.equal t1 t2 => s!"{TermToString t1} = {TermToString t2}"
| Language.BoundedFormula.rel is_elt_of₂ ts  =>
    s!"{TermTupleToString ts 0} ∈ {TermTupleToString ts 1}"
| Language.BoundedFormula.imp ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ⟹ {FormulaToString ϕ2}"

-- #eval FormulaToString ϕbot
-- #eval FormulaToString (∼ϕbot)
-- #eval FormulaToString ((fv 0 0)='(fv 0 1))
-- #eval FormulaToString ((fv 0 0)∈'(fv 0 1))
-- #eval FormulaToString (ϕbot ⟹ ((fv 0 0)∈'(fv 0 1)))
-- #eval FormulaToString (ϕbot ⟹ (fv 0 0)∈'(fv 0 1))
-- #eval FormulaToString (∀'((bv 1 0)∈'(fv 1 0)))
-- #eval FormulaToString ((fv 0 0)='(fv 0 1) ⊔ (fv 0 0)='(fv 0 2))
-- #eval FormulaToString ((fv 0 0)='(fv 0 1) ⊓ (fv 0 0)='(fv 0 2))
-- -- #eval FormulaToString (∀'((bv 1 0)='(fv 1 0)))
-- #eval FormulaToString (∀'((bv 1 0)='(fv 1 0)))
-- #eval FormulaToString (∀' ∀'((bv 2 0)='(fv 2 0)))
-- #eval FormulaToString (∃'((bv 2 0)='(fv 2 0)))
-- #eval FormulaToString (∃' ∀'((bv 2 1)∈'(bv 2 0)))
-- #eval FormulaToString (∀' ∃'((bv 2 1)∈'(bv 2 0)))

/-- Converts a term into a string with depth -/
def TermToString' {n : ℕ} (t : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
match t with
| Term.var (Sum.inl k) => s!"fv {n} {k}"
| Term.var (Sum.inr k) => s!"bv {n} {k}"
| _ => "error"

/-- Converts the first term of a pair into a string with depth -/
def TermPairFirstToString' {n : ℕ} {m : ℕ} (ts : Fin m → Language.LZFC.Term (ℕ ⊕ Fin n)) : String :=
  match m with
  -- | 0 => ""
  -- | 1 => ""
  | 2 => TermToString' (ts 0)
  | _ => ""

/-- Converts the second term of a pair into a string with depth -/
def TermPairSecondToString' {n : ℕ} {m : ℕ} (ts : Fin m → Language.LZFC.Term (ℕ ⊕ Fin n)) : String :=
  match m with
  -- | 0 => ""
  -- | 1 => ""
  | 2 => TermToString' (ts 1)
  | _ => ""

/-- Converts a formula into a string with depath -/
def FormulaToString' {n : ℕ} (ϕ : Language.LZFC.BoundedFormula ℕ n) : String :=
match ϕ with
| BoundedFormula.falsum => "⊥"
| BoundedFormula.ex ϕ1 => s!"∃'bv{n}({FormulaToString' ϕ1})"
| BoundedFormula.all ϕ1 => s!"∀'bv{n}({FormulaToString' ϕ1})"
| BoundedFormula.not (BoundedFormula.imp ϕ1 (BoundedFormula.not ϕ2)) =>
    s!"({FormulaToString' ϕ1} ∧ {FormulaToString' ϕ2})"
| BoundedFormula.imp (BoundedFormula.not ϕ1) ϕ2 =>
    s!"({FormulaToString' ϕ1} ∨ {FormulaToString' ϕ2})"
| ∼ϕ1 => s!"∼{FormulaToString' ϕ1}"
| BoundedFormula.equal t1 t2 => s!"{TermToString' t1} = {TermToString' t2}"
| BoundedFormula.rel is_elt_of₂ ts  =>
    s!"{TermPairFirstToString' ts} ∈ {TermPairSecondToString' ts}"
| BoundedFormula.imp ϕ1 ϕ2 => s!"({FormulaToString' ϕ1} ⟹ {FormulaToString' ϕ2})"

-- #eval FormulaToString ((fv 0 0)='(fv 0 1) ⊔ (fv 0 0)='(fv 0 2))
#check ((fv 0 0)='(fv 0 1) ⇔ (fv 0 0)='(fv 0 2))
#eval FormulaToString' ((fv 0 0)='(fv 0 1) ⇔ (fv 0 0)='(fv 0 2))
