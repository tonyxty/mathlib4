import Mathlib.ModelTheory.Satisfiability


universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

namespace Theory

variable (T)

def eliminatesQuantifier (φ : L.BoundedFormula α n) : Prop :=
  ∃ ψ, ψ.IsQF ∧ T.SemanticallyEquivalent φ ψ

def hasQE : Prop :=
  ∀ {α : Type w} (φ : L.BoundedFormula α n), T.eliminatesQuantifier φ

end Theory

namespace Embedding

variable (hQE : T.hasQE)

variable (M : Type (max u v)) (N : Type (max u v))

variable [Nonempty M] [Nonempty N]
variable [L.Structure M] [L.Structure N]
variable (_hM : T.Model M) (_hN : T.Model N)

theorem isElementry_of_hasQE (f : M ↪[L] N) :
    ∀ {n} (φ : L.Formula (Fin n)) (v : Fin n → M), φ.Realize (f ∘ v) ↔ φ.Realize v := by
  intro n φ v
  obtain ⟨ψ, hQF, h⟩ := hQE φ
  rw [h.realize_iff _hM, h.realize_iff _hN, Formula.Realize]
  have : default = f ∘ (default : Fin 0 → M) := by simp
  rw [this]
  apply f.realize_QFFormula hQF
