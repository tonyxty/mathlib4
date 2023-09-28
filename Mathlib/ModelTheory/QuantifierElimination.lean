import Mathlib.ModelTheory.Satisfiability


universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

variable (M : Type (max u v)) (N : Type (max u v))

variable [Nonempty M] [Nonempty N]
variable [L.Structure M] [L.Structure N]
variable (_hM : T.Model M) (_hN : T.Model N)

namespace Theory

def eliminatesQuantifier (φ : L.Formula α) : Prop :=
  ∃ ψ, ψ.IsQF ∧ T.SemanticallyEquivalent φ ψ

theorem eliminatesQuantifier_iff_realize_common_substructure {φ : L.Formula α} :
    T.eliminatesQuantifier φ ↔
    (∀ {A} {M N : Type max u v} [L.Structure A] [Nonempty M] [Nonempty N]
      [L.Structure M] [L.Structure N] [T.Model M] [T.Model N]
      (f : A ↪[L] M) (g : A ↪[L] N) (v : α → A),
      φ.Realize (f ∘ v) ↔ φ.Realize (g ∘ v)) := by
  constructor
  · intro ⟨ψ, hQF, h⟩ _ M N _ _ _ _ _ _hM _hN f g v
    rw [h.realize_iff _hM, h.realize_iff _hN, f.realize_QF_formula hQF, g.realize_QF_formula hQF]
  · intro h
    let ι := L.lhomWithConstants α
    let T₁ := (ι.onTheory T) ∪ {Formula.equivSentence φ}
    -- S is the set of quantifier-free consequences of φ
    let S := { σ : L[[α]].Sentence | σ.IsQF ∧ T₁ ⊨ᵇ σ }
    -- we show that T ∪ S ∪ {¬φ} is not satisfiable
    let T' : L[[α]].Theory := (ι.onTheory T) ∪ S
    have : ¬ Theory.IsSatisfiable (T' ∪ {∼(Formula.equivSentence φ)}) := sorry
    -- now let ψ be the conjunction of a finite subset of S that entails φ modulo T
    obtain ⟨T₂, h', h⟩ :=
      finset_models_of_union_models_right ((models_iff_not_satisfiable _).mpr this)
    let ψ := BoundedFormula.iInf T₂ Formula.equivSentence.symm
    use ψ; constructor
    · apply BoundedFormula.isQF_iInf
      intro σ hσ
      apply BoundedFormula.IsQF.mapTermRel
      apply BoundedFormula.IsQF.mapTermRel
      exact (h' (Finset.mem_coe.mpr hσ)).left
    · apply semanticallyEquivalent_of_realize_iff
      intro M _ _ _ v
      sorry


def hasQE : Prop :=
  ∀ {α : Type w} (φ : L.Formula α), T.eliminatesQuantifier φ

end Theory

namespace Embedding

variable (hQE : T.hasQE)

theorem isElementry_of_hasQE (f : M ↪[L] N) :
    ∀ {n} (φ : L.Formula (Fin n)) (v : Fin n → M), φ.Realize (f ∘ v) ↔ φ.Realize v := by
  intro n φ v
  obtain ⟨ψ, hQF, h⟩ := hQE φ
  rw [h.realize_iff _hM, h.realize_iff _hN]
  exact f.realize_QF_formula hQF
