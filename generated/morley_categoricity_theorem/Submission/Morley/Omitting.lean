import Mathlib

/-!
# The omitting types theorem

A chapter of the formalisation of Morley's categoricity theorem.

For a theory `T` in a countable language and a set `p` of formulas in `n` free variables which is
*non-isolated* over `T` (`Submission.Morley.IsNonIsolated`), `T` has a model omitting `p`
(`Submission.Morley.exists_model_omitting`).

## Implementation notes

The proof is a Baire category argument on the Stone space `T.CompleteType ℕ` of complete types in
countably many variables, rather than an explicit Henkin chain construction. Mathlib provides that
this space is compact, totally separated and (hence) a Baire space, and that every point of it is
realized by a tuple `v : ℕ → M` in some model `M` of `T`
(`FirstOrder.Language.Theory.exists_modelType_is_realized_in`).

Two countable families of dense open subsets are used:

* `henkinSet T φ`, for `φ : L.BoundedFormula ℕ 1`: the types for which `∃ x, φ x` has a witness
  among the variables `ℕ` whenever it holds at all;
* `omitSet T p k`, for `k : Fin n → ℕ`: the types containing `¬ψ` at the tuple `k` for some
  `ψ ∈ p`. Density of these sets is exactly where non-isolation is used.

A point `q` in the intersection is realized by some `v : ℕ → M`; the Henkin conditions say that
`Set.range v` is closed under the functions of `L` and passes the Tarski–Vaught test, so it is an
elementary substructure of `M`, and the omitting conditions say that every one of its `n`-tuples
fails some formula of `p`.
-/

open Cardinal Set FirstOrder FirstOrder.Language FirstOrder.Language.Theory

namespace Submission.Morley

variable {L : FirstOrder.Language.{0, 0}} {n : ℕ}

/-! ### Non-isolated types -/

/-- A set `p` of formulas in `n` free variables is *non-isolated* over the theory `T` when no
formula consistent with `T` isolates (supports) it: for every formula `φ(x̄)` which is realized in
some model of `T`, there is `ψ ∈ p` such that `T ∪ {∃x̄ φ(x̄)}` does not entail `∀x̄ (φ x̄ → ψ x̄)`,
i.e. some model of `T` has a tuple satisfying `φ ∧ ¬ψ`.

This is the semantic phrasing of "`p` is not principal/isolated over `T`"; by the completeness
theorem it agrees with the syntactic version. -/
def IsNonIsolated (T : L.Theory) (p : Set (L.Formula (Fin n))) : Prop :=
  ∀ φ : L.Formula (Fin n),
    (∃ (M : T.ModelType.{0, 0, 0}) (v : Fin n → M), φ.Realize v) →
      ∃ ψ ∈ p, ∃ (M : T.ModelType.{0, 0, 0}) (v : Fin n → M), φ.Realize v ∧ ¬ψ.Realize v

/-! ### Realization only depends on the free variables -/

/-- Two assignments that agree on the free variables of a bounded formula realize it alike. -/
theorem realize_congr_freeVar {α : Type} [DecidableEq α] {M : Type} [L.Structure M] {m : ℕ}
    (φ : L.BoundedFormula α m) (v v' : α → M) (h : ∀ a ∈ φ.freeVarFinset, v a = v' a)
    (xs : Fin m → M) : φ.Realize v xs ↔ φ.Realize v' xs := by
  rw [← BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
        (v := fun a : φ.freeVarFinset => v (a : α)) (v' := v) (xs := xs) (fun _ => rfl),
      BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
        (v := fun a : φ.freeVarFinset => v (a : α)) (v' := v') (xs := xs)
        (fun a => h a a.2)]

/-! ### The Stone space of complete `ℕ`-types -/

section TypeSpace

variable {T : L.Theory}

/-- The clopen set of complete `ℕ`-types over `T` containing the formula `χ`. -/
def typesSat (T : L.Theory) (χ : L.Formula ℕ) : Set (T.CompleteType ℕ) :=
  T.typesWith (Formula.equivSentence χ)

theorem isOpen_typesSat (T : L.Theory) (χ : L.Formula ℕ) : IsOpen (typesSat T χ) :=
  _root_.CompleteType.isOpen_typesWith _

theorem mem_typesSat_typeOf {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T] (v : ℕ → M)
    (χ : L.Formula ℕ) : T.typeOf v ∈ typesSat T χ ↔ χ.Realize v :=
  CompleteType.formula_mem_typeOf

/-- Every complete `ℕ`-type is realized by a tuple in some model, and then membership in the type
is exactly realization of the corresponding formula. -/
theorem exists_realize_completeType (q : T.CompleteType ℕ) :
    ∃ (M : T.ModelType.{0, 0, 0}) (v : ℕ → M),
      ∀ χ : L.Formula ℕ, q ∈ typesSat T χ ↔ χ.Realize v := by
  obtain ⟨M, v, hv⟩ := Theory.exists_modelType_is_realized_in T q
  exact ⟨M, v, fun χ => by rw [← hv]; exact mem_typesSat_typeOf v χ⟩

theorem typesSat_nonempty_iff (T : L.Theory) (χ : L.Formula ℕ) :
    (typesSat T χ).Nonempty ↔ ∃ (M : T.ModelType.{0, 0, 0}) (v : ℕ → M), χ.Realize v := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨M, v, hv⟩ := exists_realize_completeType q
    exact ⟨M, v, (hv χ).1 hq⟩
  · rintro ⟨M, v, hv⟩
    exact ⟨T.typeOf v, (mem_typesSat_typeOf v χ).2 hv⟩

/-- To check density it suffices to meet every nonempty basic clopen set. -/
theorem dense_of_forall_typesSat {S : Set (T.CompleteType ℕ)}
    (h : ∀ χ : L.Formula ℕ, (typesSat T χ).Nonempty → (typesSat T χ ∩ S).Nonempty) : Dense S := by
  rw [_root_.CompleteType.isTopologicalBasis_range_typesWith.dense_iff]
  rintro o ⟨θ, rfl⟩ ho
  have hrw : T.typesWith θ = typesSat T (Formula.equivSentence.symm θ) := by
    rw [typesSat, Equiv.apply_symm_apply]
  rw [hrw] at ho ⊢
  exact h _ ho

end TypeSpace

/-! ### Henkin witnesses -/

section Henkin

variable {T : L.Theory}

/-- Substitutes the variable `i` for the unique bound variable of `φ`. -/
def instVar (φ : L.BoundedFormula ℕ 1) (i : ℕ) : L.Formula ℕ :=
  Formula.relabel (Sum.elim id fun _ => i) φ.toFormula

theorem realize_instVar {M : Type} [L.Structure M] (φ : L.BoundedFormula ℕ 1) (i : ℕ)
    (w : ℕ → M) : (instVar φ i).Realize w ↔ φ.Realize w fun _ => w i := by
  rw [instVar, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  rfl

theorem realize_ex_one {M : Type} [L.Structure M] (φ : L.BoundedFormula ℕ 1) (v : ℕ → M) :
    Formula.Realize (BoundedFormula.ex φ) v ↔ ∃ a : M, φ.Realize v fun _ => a := by
  have h1 : Formula.Realize (BoundedFormula.ex φ) v ↔
      ∃ a : M, φ.Realize v (Fin.snoc default a) := BoundedFormula.realize_ex
  rw [h1]
  refine exists_congr fun a => ?_
  have h : (Fin.snoc (default : Fin 0 → M) a) = fun _ => a := by
    funext j
    simp [Fin.snoc]
  rw [h]

/-- The set of types for which `φ` has a witness among the constants, if it has one at all. -/
def henkinSet (T : L.Theory) (φ : L.BoundedFormula ℕ 1) : Set (T.CompleteType ℕ) :=
  (typesSat T φ.ex)ᶜ ∪ ⋃ i : ℕ, typesSat T (instVar φ i)

theorem isOpen_henkinSet (T : L.Theory) (φ : L.BoundedFormula ℕ 1) :
    IsOpen (henkinSet T φ) :=
  ((_root_.CompleteType.isClosed_typesWith _).isOpen_compl).union
    (isOpen_iUnion fun _ => isOpen_typesSat _ _)

theorem dense_henkinSet (T : L.Theory) (φ : L.BoundedFormula ℕ 1) : Dense (henkinSet T φ) := by
  refine dense_of_forall_typesSat fun χ hχ => ?_
  by_cases hcase : ∃ (M : T.ModelType.{0, 0, 0}) (v : ℕ → M),
      χ.Realize v ∧ ∃ a : M, φ.Realize v fun _ => a
  · obtain ⟨M, v, hv1, a, ha⟩ := hcase
    obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset (χ.freeVarFinset ∪ φ.freeVarFinset)
    simp only [Finset.mem_union, not_or] at hi
    have hagree : ∀ j, j ≠ i → Function.update v i a j = v j :=
      fun j hj => Function.update_of_ne hj _ _
    have hχ' : χ.Realize (Function.update v i a) := by
      refine (realize_congr_freeVar χ v (Function.update v i a) (fun b hb => ?_) default).1 hv1
      exact (hagree b fun h => hi.1 (h ▸ hb)).symm
    have hφ' : φ.Realize (Function.update v i a) fun _ => Function.update v i a i := by
      rw [Function.update_self]
      refine (realize_congr_freeVar φ v (Function.update v i a) (fun b hb => ?_) _).1 ha
      exact (hagree b fun h => hi.2 (h ▸ hb)).symm
    refine ⟨T.typeOf (Function.update v i a),
      (mem_typesSat_typeOf _ χ).2 hχ', Or.inr (mem_iUnion.2 ⟨i, ?_⟩)⟩
    exact (mem_typesSat_typeOf _ (instVar φ i)).2 ((realize_instVar φ i _).2 hφ')
  · obtain ⟨q, hq⟩ := hχ
    refine ⟨q, hq, Or.inl fun hmem => ?_⟩
    obtain ⟨M, v, hv⟩ := exists_realize_completeType q
    exact hcase ⟨M, v, (hv χ).1 hq, (realize_ex_one φ v).1 ((hv _).1 hmem)⟩

end Henkin

/-! ### Omitting the type on a tuple of constants -/

section Omit

variable {T : L.Theory} {p : Set (L.Formula (Fin n))}

/-- The negation of `ψ` with the variable `x i` replaced by the variable `k i`. -/
def negParam (ψ : L.Formula (Fin n)) (k : Fin n → ℕ) : L.Formula ℕ :=
  (Formula.relabel k ψ).not

theorem realize_negParam {M : Type} [L.Structure M] (ψ : L.Formula (Fin n)) (k : Fin n → ℕ)
    (w : ℕ → M) : (negParam ψ k).Realize w ↔ ¬ψ.Realize (w ∘ k) := by
  rw [negParam, Formula.realize_not, Formula.realize_relabel]

/-- Non-isolation, in the form needed for the density argument: any formula `χ` in the variables
`ℕ` which is consistent with `T` can be realized together with the failure of some `ψ ∈ p` at the
tuple of variables `k`. -/
theorem exists_realize_negParam (hp : IsNonIsolated T p) (χ : L.Formula ℕ) (k : Fin n → ℕ)
    (h : ∃ (M : T.ModelType.{0, 0, 0}) (v : ℕ → M), χ.Realize v) :
    ∃ ψ ∈ p, ∃ (M : T.ModelType.{0, 0, 0}) (v : ℕ → M),
      χ.Realize v ∧ ¬ψ.Realize (v ∘ k) := by
  classical
  set γ : Type := Option {j : ℕ // j ∈ χ.freeVarFinset} with hγ
  set g : ℕ → Fin n ⊕ γ := fun j =>
    if hj : ∃ i, k i = j then Sum.inl hj.choose
    else if hj2 : j ∈ χ.freeVarFinset then Sum.inr (some ⟨j, hj2⟩) else Sum.inr none with hg
  set E : L.Formula (Fin n ⊕ γ) := Formula.iInf fun ii : Fin n × Fin n =>
    if k ii.1 = k ii.2 then Term.equal (Term.var (Sum.inl ii.1)) (Term.var (Sum.inl ii.2))
    else ⊤ with hE
  set Φ : L.Formula (Fin n) := Formula.iExs γ (Formula.relabel g χ ⊓ E) with hΦ
  -- realization of `Φ`
  have hrealΦ : ∀ (M : Type) (_ : L.Structure M) (u : Fin n → M), Φ.Realize u ↔
      ∃ w : γ → M, χ.Realize (Sum.elim u w ∘ g) ∧ ∀ i₁ i₂ : Fin n, k i₁ = k i₂ → u i₁ = u i₂ := by
    intro M _ u
    rw [hΦ, Formula.realize_iExs]
    refine exists_congr fun w => ?_
    rw [Formula.realize_inf, Formula.realize_relabel, hE, Formula.realize_iInf]
    refine and_congr Iff.rfl ⟨fun hcon i₁ i₂ hk => ?_, fun hcon ii => ?_⟩
    · have := hcon (i₁, i₂)
      rw [if_pos hk, Formula.realize_equal] at this
      simpa using this
    · by_cases hk : k ii.1 = k ii.2
      · rw [if_pos hk, Formula.realize_equal]
        simpa using hcon ii.1 ii.2 hk
      · rw [if_neg hk]
        exact fun hf => hf
  obtain ⟨M, v, hv⟩ := h
  have hΦv : Φ.Realize (v ∘ k) := by
    rw [hrealΦ M inferInstance]
    refine ⟨fun c => c.elim (v 0) fun jj => v (jj : ℕ), ?_, fun i₁ i₂ hk => by simp [hk]⟩
    refine (realize_congr_freeVar χ v _ (fun j hj => ?_) default).1 hv
    by_cases hj1 : ∃ i, k i = j
    · simp only [hg, Function.comp_apply, dif_pos hj1, Sum.elim_inl, Function.comp_apply,
        hj1.choose_spec]
    · simp only [hg, Function.comp_apply, dif_neg hj1, dif_pos hj, Sum.elim_inr, Option.elim_some]
  obtain ⟨ψ, hψp, M', u', hΦu', hnψ⟩ := hp Φ ⟨M, v ∘ k, hΦv⟩
  rw [hrealΦ M' inferInstance] at hΦu'
  obtain ⟨w', hw'χ, hw'E⟩ := hΦu'
  refine ⟨ψ, hψp, M', Sum.elim u' w' ∘ g, hw'χ, ?_⟩
  have hcomp : (Sum.elim u' w' ∘ g) ∘ k = u' := by
    funext i₀
    have hex : ∃ i, k i = k i₀ := ⟨i₀, rfl⟩
    simp only [Function.comp_apply, hg, dif_pos hex, Sum.elim_inl]
    exact hw'E _ _ (hex.choose_spec.trans rfl)
  rw [hcomp]
  exact hnψ

/-- The (open) set of types which omit `p` on the tuple of constants indexed by `k`. -/
def omitSet (T : L.Theory) (p : Set (L.Formula (Fin n))) (k : Fin n → ℕ) :
    Set (T.CompleteType ℕ) :=
  ⋃ ψ ∈ p, typesSat T (negParam ψ k)

theorem isOpen_omitSet (T : L.Theory) (p : Set (L.Formula (Fin n))) (k : Fin n → ℕ) :
    IsOpen (omitSet T p k) :=
  isOpen_biUnion fun _ _ => isOpen_typesSat _ _

theorem dense_omitSet (hp : IsNonIsolated T p) (k : Fin n → ℕ) : Dense (omitSet T p k) := by
  refine dense_of_forall_typesSat fun χ hχ => ?_
  obtain ⟨ψ, hψp, M, v, hχv, hnψ⟩ :=
    exists_realize_negParam hp χ k ((typesSat_nonempty_iff T χ).1 hχ)
  refine ⟨T.typeOf v, (mem_typesSat_typeOf v χ).2 hχv, mem_biUnion hψp ?_⟩
  exact (mem_typesSat_typeOf v (negParam ψ k)).2 ((realize_negParam ψ k v).2 hnψ)

end Omit

/-! ### The Tarski–Vaught test for the set of constants -/

section TarskiVaught

/-- If every existential formula with parameters among the `v i` has a witness among the `v i`,
then the Tarski–Vaught condition holds for `Set.range v`. -/
theorem exists_witness_of_henkin {M : Type} [L.Structure M] (v : ℕ → M)
    (H : ∀ φ : L.BoundedFormula ℕ 1, (∃ a : M, φ.Realize v fun _ => a) →
      ∃ i : ℕ, φ.Realize v fun _ => v i)
    {l : ℕ} (φ' : L.BoundedFormula Empty (l + 1)) (k : Fin l → ℕ) (a : M)
    (h : φ'.Realize default (Fin.snoc (fun j => v (k j)) a)) :
    ∃ i : ℕ, φ'.Realize default (Fin.snoc (fun j => v (k j)) (v i)) := by
  set g : Empty ⊕ Fin (l + 1) → ℕ ⊕ Fin 1 :=
    Sum.elim (fun e => e.elim) (Fin.snoc (fun j : Fin l => Sum.inl (k j)) (Sum.inr 0)) with hg
  set φ : L.BoundedFormula ℕ 1 := BoundedFormula.relabel g φ'.toFormula with hφ
  have key : ∀ xs : Fin 1 → M,
      φ.Realize v xs ↔ φ'.Realize default (Fin.snoc (fun j => v (k j)) (xs 0)) := by
    intro xs
    have h2 : (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ g) ∘ Sum.inr
        = Fin.snoc (fun j => v (k j)) (xs 0) := by
      show Sum.elim v (xs ∘ Fin.castAdd 0) ∘
        (Fin.snoc (fun j : Fin l => Sum.inl (k j)) (Sum.inr 0)) = _
      rw [Fin.comp_snoc]
      rfl
    have main : ∀ ys : Fin 0 → M,
        BoundedFormula.Realize φ'.toFormula (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ g) ys ↔
          φ'.Realize default (Fin.snoc (fun j => v (k j)) (xs 0)) := by
      intro ys
      rw [Unique.eq_default ys]
      refine Iff.trans (BoundedFormula.realize_toFormula φ' _) ?_
      rw [h2, Unique.eq_default ((Sum.elim v (xs ∘ Fin.castAdd 0) ∘ g) ∘ Sum.inl)]
    rw [hφ, BoundedFormula.realize_relabel]
    exact main _
  exact H φ ⟨a, (key _).2 h⟩ |>.imp fun i hi => (key _).1 hi

end TarskiVaught

/-! ### The omitting types theorem -/

section Main

variable {T : L.Theory} {p : Set (L.Formula (Fin n))}

/-- Baire category on the (compact, hence Baire) Stone space of complete `ℕ`-types produces a
complete type which has Henkin witnesses for every existential formula and which omits `p` on
every tuple of constants. -/
theorem exists_completeType_henkin_omitting (hL : L.card ≤ ℵ₀) (hT : T.IsSatisfiable)
    (hp : IsNonIsolated T p) :
    ∃ q : T.CompleteType ℕ,
      (∀ φ : L.BoundedFormula ℕ 1, q ∈ henkinSet T φ) ∧ ∀ k : Fin n → ℕ, q ∈ omitSet T p k := by
  haveI : Countable L.Symbols := Cardinal.mk_le_aleph0_iff.mp hL
  haveI : Countable (L.BoundedFormula ℕ 1) :=
    Function.Injective.countable
      (f := fun φ : L.BoundedFormula ℕ 1 => (⟨1, φ⟩ : Σ m, L.BoundedFormula ℕ m))
      sigma_mk_injective
  haveI : Nonempty (T.CompleteType ℕ) := CompleteType.nonempty_iff.2 hT
  have hd : Dense (⋂ i : L.BoundedFormula ℕ 1 ⊕ (Fin n → ℕ),
      Sum.elim (henkinSet T) (omitSet T p) i) := by
    refine dense_iInter_of_isOpen (fun i => ?_) fun i => ?_
    · cases i with
      | inl φ => exact isOpen_henkinSet T φ
      | inr k => exact isOpen_omitSet T p k
    · cases i with
      | inl φ => exact dense_henkinSet T φ
      | inr k => exact dense_omitSet hp k
  obtain ⟨q, hq⟩ := hd.nonempty
  rw [mem_iInter] at hq
  exact ⟨q, fun φ => hq (Sum.inl φ), fun k => hq (Sum.inr k)⟩

/-- **The omitting types theorem.** If `T` is a satisfiable theory in a countable language and `p`
is a set of formulas in `n` free variables which is non-isolated over `T`, then `T` has a model
omitting `p`: no `n`-tuple of the model realizes every formula of `p`. -/
theorem exists_model_omitting (hL : L.card ≤ ℵ₀) (T : L.Theory) (hT : T.IsSatisfiable)
    (p : Set (L.Formula (Fin n))) (hp : IsNonIsolated T p) :
    ∃ M : T.ModelType.{0, 0, 0}, ∀ a : Fin n → M, ∃ φ ∈ p, ¬φ.Realize a := by
  classical
  obtain ⟨q, hH, hO⟩ := exists_completeType_henkin_omitting hL hT hp
  obtain ⟨M, v, hv⟩ := exists_realize_completeType q
  have H : ∀ φ : L.BoundedFormula ℕ 1, (∃ a : M, φ.Realize v fun _ => a) →
      ∃ i : ℕ, φ.Realize v fun _ => v i := by
    intro φ ha
    rcases hH φ with h | h
    · exact absurd ((hv _).2 ((realize_ex_one φ v).2 ha)) h
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact ⟨i, (realize_instVar φ i v).1 ((hv _).1 hi)⟩
  have O : ∀ k : Fin n → ℕ, ∃ ψ ∈ p, ¬ψ.Realize (v ∘ k) := by
    intro k
    obtain ⟨ψ, hψp, hmem⟩ := mem_iUnion₂.1 (hO k)
    exact ⟨ψ, hψp, (realize_negParam ψ k v).1 ((hv _).1 hmem)⟩
  -- The set of constants is closed under the functions of `L`.
  have hclosed : ∀ {m : ℕ} (f : L.Functions m) (x : Fin m → M),
      (∀ i, x i ∈ Set.range v) → Structure.funMap f x ∈ Set.range v := by
    intro m f x hx
    choose k hk using hx
    have hxk : (fun i => v (k i)) = x := funext hk
    set φ : L.BoundedFormula ℕ 1 :=
      Term.bdEqual (Term.func f fun i => Term.var (Sum.inl (k i))) (Term.var (Sum.inr 0)) with hφ
    have hrel : ∀ xs : Fin 1 → M, φ.Realize v xs ↔ Structure.funMap f x = xs 0 := by
      intro xs
      rw [hφ, BoundedFormula.realize_bdEqual]
      simp only [Term.realize_func, Term.realize_var, Sum.elim_inl, Sum.elim_inr, hxk]
    obtain ⟨i, hi⟩ := H φ ⟨Structure.funMap f x, (hrel _).2 rfl⟩
    exact ⟨i, ((hrel _).1 hi).symm⟩
  set S : L.Substructure M := { carrier := Set.range v, fun_mem := fun f x hx => hclosed f x hx }
    with hS
  have htv : ∀ (l : ℕ) (φ' : L.BoundedFormula Empty (l + 1)) (x : Fin l → S) (a : M),
      φ'.Realize default (Fin.snoc ((↑) ∘ x) a) →
        ∃ b : S, φ'.Realize default (Fin.snoc ((↑) ∘ x) (b : M)) := by
    intro l φ' x a hreal
    have hx : ∀ i, (x i : M) ∈ Set.range v := fun i => (x i).2
    choose k hk using hx
    have hxk : (fun j => v (k j)) = (↑) ∘ x := funext hk
    rw [← hxk] at hreal ⊢
    obtain ⟨i, hi⟩ := exists_witness_of_henkin v H φ' k a hreal
    exact ⟨⟨v i, ⟨i, rfl⟩⟩, hi⟩
  set N : L.ElementarySubstructure M := S.toElementarySubstructure htv with hN
  have hfinal : ∀ a : Fin n → N, ∃ ψ ∈ p, ¬ψ.Realize a := by
    intro a
    have ha : ∀ i, ((a i : M)) ∈ Set.range v := fun i => (a i).2
    choose k hk using ha
    obtain ⟨ψ, hψp, hnψ⟩ := O k
    refine ⟨ψ, hψp, fun hcon => hnψ ?_⟩
    have hcon' := (N.subtype.map_formula ψ a).2 hcon
    rwa [show (N.subtype : N → M) ∘ a = v ∘ k from funext fun i => (hk i).symm] at hcon'
  exact ⟨N.toModel T, hfinal⟩

end Main

end Submission.Morley
