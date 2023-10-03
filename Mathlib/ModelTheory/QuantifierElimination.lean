import Mathlib.ModelTheory.Satisfiability


universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type max u v}

variable (M : Type (max u v)) (N : Type (max u v))

variable [Nonempty M] [Nonempty N]
variable [L.Structure M] [L.Structure N]
variable (_hM : T.Model M) (_hN : T.Model N)

namespace Theory

def eliminatesQuantifier (φ : L.Formula α) : Prop :=
  ∃ ψ, ψ.IsQF ∧ T.SemanticallyEquivalent φ ψ

theorem eliminatesQuantifier_iff_realize_common_substructure {φ : L.Formula α} :
    T.eliminatesQuantifier φ ↔
    (∀ {A : Type max u v} {M N : Type max u v} [L.Structure A] [Nonempty M] [Nonempty N]
      [L.Structure M] [L.Structure N] [T.Model M] [T.Model N]
      (f : A ↪[L] M) (g : A ↪[L] N) (v : α → A),
      φ.Realize (f ∘ v) ↔ φ.Realize (g ∘ v)) := by
  constructor
  · intro ⟨ψ, hQF, h⟩ _ M N _ _ _ _ _ _hM _hN f g v
    rw [h.realize_iff _hM, h.realize_iff _hN, f.realize_QF_formula hQF, g.realize_QF_formula hQF]
  · intro h
    let ι := L.lhomWithConstants α
    -- S is the set of quantifier-free consequences of φ
    let S := { σ : L.Formula α | σ.IsQF ∧ T ⊨ᵇ φ ⟹ σ }
    -- we show that T ∪ S ∪ {¬φ} is not satisfiable
    let T' : L[[α]].Theory := (ι.onTheory T) ∪ Formula.equivSentence '' S
    have : ¬ Theory.IsSatisfiable (T' ∪ {∼(Formula.equivSentence φ)}) := by
      intro ⟨M⟩
      let A : L[[α]].Substructure M := Substructure.closure (L[[α]]) ∅
      let _ := ι.reduct A
      have D := L[[α]].completeTheory A
      have : IsSatisfiable (ι.onTheory T ∪ D ∪ {Formula.equivSentence φ}) := sorry
      obtain ⟨N⟩ := this
      have : ι.IsExpansionOn M := sorry
      have : ι.IsExpansionOn N := sorry
      have : M ⊨ T := (ι.onTheory_model T).mp
        (M.is_model.mono (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _))
      have : N ⊨ T := (ι.onTheory_model T).mp
        (N.is_model.mono (Set.subset_union_of_subset_left (Set.subset_union_left _ _) _))
      have i : A ↪[L] M := sorry
      have j : A ↪[L] N := sorry
      have : ¬M ⊨ Formula.equivSentence φ := (Sentence.realize_not _).mp
        (M.is_model.realize_of_mem _ (Set.mem_union_right _ (Set.mem_singleton _)))
      apply this
      have := h i j (fun d => L.con d)
      have i_con : i ∘ (fun d => L.con d) = fun d : α => (L.con d : M) := sorry
      have j_con : j ∘ (fun d => L.con d) = fun d : α => (L.con d : N) := sorry
      rw [i_con, ← φ.realize_equivSentence M, j_con, ← φ.realize_equivSentence N] at this
      rw [this]
      exact (N.is_model.realize_of_mem _ (Set.mem_union_right _ (Set.mem_singleton _)))
    -- now let ψ be the conjunction of a finite subset of S that entails φ modulo T
    obtain ⟨T₁, hsub, h'⟩ :=
      finset_models_of_union_models_right ((models_iff_not_satisfiable _).mpr this)
    let ψ := BoundedFormula.iInf T₁ Formula.equivSentence.symm
    use ψ; constructor
    · apply BoundedFormula.isQF_iInf
      intro _ hσ
      apply BoundedFormula.IsQF.mapTermRel
      apply BoundedFormula.IsQF.mapTermRel
      obtain ⟨σ', hσ', rfl⟩ := hsub (Finset.mem_coe.mpr hσ)
      exact (Formula.isQF_equivSentence σ').mp hσ'.left
    · intro M v xs; simp
      constructor
      · intro hφ _ hσ
        obtain ⟨_, hσ', rfl⟩ := hsub (Finset.mem_coe.mpr hσ)
        simp
        exact BoundedFormula.realize_imp.mp (hσ'.right M v xs) hφ
      · intro h''
        apply Unique.forall_iff.mpr
        apply (Formula.realize_equivSentence' M φ v).mp
        let _ := constantsOn.structure v
        have : M ⊨ ι.onTheory T ∪ T₁ := by
          refine' ((ι.onTheory_model T).mpr M.is_model).union _
          constructor
          intro σ hσ
          apply (Formula.realize_equivSentence_symm M σ v).mp
          have := h'' σ hσ
          rw [Unique.eq_default xs] at this
          apply Unique.forall_iff.mpr this
        exact models_sentence_iff.mp h' (ModelType.of (ι.onTheory T ∪ T₁) M)

def hasQE : Prop :=
  ∀ {α : Type max u v} (φ : L.Formula α), T.eliminatesQuantifier φ

end Theory

namespace Embedding

variable (hQE : T.hasQE)

theorem isElementry_of_hasQE (f : M ↪[L] N) :
    ∀ {n} (φ : L.Formula (ULift.{max u v} (Fin n))) (v : ULift.{max u v} (Fin n) → M),
    φ.Realize (f ∘ v) ↔ φ.Realize v := by
  intro n φ v
  obtain ⟨ψ, hQF, h⟩ := hQE φ
  rw [h.realize_iff _hM, h.realize_iff _hN]
  exact f.realize_QF_formula hQF
