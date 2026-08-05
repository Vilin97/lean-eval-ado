import Mathlib
import Submission.Morley.Saturated
import Submission.Morley.Port.ElementaryChain
import Submission.Morley.SatStep
import Submission.Morley.SatTypes

/-!
# Existence of `κ⁺`-saturated elementary extensions

Every model `M` of a theory `T` in a countable language has an elementary extension `N` of
cardinality at most `(κ + #M) ^ κ` realizing **every** complete `1`-type over **every** parameter
set `A ⊆ N` with `#A ≤ κ`; this is `Submission.Morley.exists_saturated_elementaryExtension`.

## The construction

`N` is the colimit of an elementary chain of length `κ⁺`.  Every construction available elsewhere
in this development is a recursion *inside a fixed structure*; here the structures themselves grow,
so the chain is built as follows.

* All stages are realized as **subsets of one fixed ambient type** `U` (of cardinality `2 ^ ν`,
  where `ν = (κ + #M) ^ κ`), each carrying an `L`-structure: this is
  `Submission.Morley.Stage`.  Because the transition maps are then literal inclusions, the
  coherence conditions `map_self` and `map_map` of `FirstOrder.Language.ElementaryChain` hold by
  `rfl` (`Submission.Morley.stageChain`), and the colimit machinery of
  `Submission/Morley/Port/ElementaryChain.lean` applies verbatim.
* The stages are produced by `Submission.Morley.choiceRec`, a transfinite recursion which at each
  step *chooses* a value satisfying the predicate `Submission.Morley.Good` — extending the base and
  all earlier stages elementarily, small, and realizing the required types — if one exists.  That
  one exists is proved separately, by transfinite induction, in
  `Submission.Morley.good_choiceRec`; the step itself is
  `Submission.Morley.exists_good_aux`, which forms the direct limit of the earlier stages, applies
  one compactness step (`Submission.Morley.exists_step`) and transports the result back into `U`
  along an injection extending the one already fixed on the earlier stages
  (`Submission.Morley.exists_injective_extend`, `Submission.Morley.inducedStructure`).
* Types are handled *syntactically*, as arbitrary sets of formulas
  `S ⊆ L.Formula (γ ⊕ Fin 1)` in one free variable over a `γ`-indexed tuple of parameters, where
  `#γ = κ`; `Submission.Morley.FinSat` is finite satisfiability of such a set.  Since there are
  only `2 ^ κ` such sets and `#X ^ κ` such tuples, each stage stays of size at most `ν = ν ^ κ`.
  No cardinality assumption on the type spaces (hence no stability assumption) is needed.
* At the end, a `γ`-tuple of parameters of the colimit lies in a single stage because `κ⁺` is
  regular (`Submission.Morley.exists_upper_bound_toType`), and `κ⁺` is a limit ordinal so there is
  always a next stage (`Submission.Morley.exists_gt_toType`).

## Main results

* `Submission.Morley.exists_step`: one compactness step, of controlled cardinality.
* `Submission.Morley.exists_chain_saturated`: the chain construction, in the purely syntactic
  form — the colimit realizes every finitely satisfiable set of formulas over `γ` parameters.
* `Submission.Morley.exists_saturated_elementaryExtension`: the main theorem, phrased with the
  complete types `Submission.Morley.S₁` of `Submission/Morley/Stable.lean`.
* `Submission.Morley.exists_saturated_elementaryExtension_lt` and
  `Submission.Morley.exists_saturated_elementaryExtension_realizedTypes`: the same, with `#A < κ`
  and in the `realizedTypes` phrasing of `Submission.Morley.IsSaturated`.
* `Submission.Morley.isSaturated_of_forall_realize`: realizing all types over parameter sets of
  size at most `κ` gives `Submission.Morley.IsSaturated` as soon as `#N ≤ κ⁺`.
* `Submission.Morley.exists_isSaturated_elementaryExtension`: consequently a *saturated*
  elementary extension exists whenever `(κ + #M) ^ κ ≤ κ⁺`.

## What is not proved here

`IsSaturated N` outright, for arbitrary `T` and `κ`, is not a theorem of `ZFC`: a saturated model
of cardinality `κ` need not exist unless `T` is stable in `κ` or the cardinal arithmetic
cooperates.  Sharpening the bound `(κ + #M) ^ κ` to `κ⁺` in the `ω`-stable case would require
indexing the successor step by *complete types over the current stage* rather than by arbitrary
sets of formulas, and hence a transport of `Submission.Morley.S₁` along an elementary embedding,
which is not developed here.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

universe u v

/-! ## Transporting a structure along a bijection -/

section Transport

variable {L : FirstOrder.Language.{u, v}}

/-- A junk `L`-structure on an inhabited type, used as a default value. -/
@[reducible] def junkStructure (Z : Type*) [Inhabited Z] : L.Structure Z where
  funMap _ _ := default
  RelMap _ _ := True

/-- The `L`-structure on `Z` obtained by transporting the structure of `Y` along a bijection. -/
@[reducible] def inducedStructure {Y Z : Type*} [L.Structure Y] (e : Y ≃ Z) : L.Structure Z where
  funMap f x := e (Structure.funMap f fun i => e.symm (x i))
  RelMap r x := Structure.RelMap r fun i => e.symm (x i)

/-- A bijection is an isomorphism onto the transported structure. -/
def inducedEquiv {Y Z : Type*} [L.Structure Y] (e : Y ≃ Z) :
    letI : L.Structure Z := inducedStructure e
    Y ≃[L] Z :=
  letI : L.Structure Z := inducedStructure e
  { toEquiv := e
    map_fun' := fun {_} f x => by
      show e (Structure.funMap f x) = e (Structure.funMap f fun i => e.symm (e (x i)))
      simp
    map_rel' := fun {_} r x => by
      show (Structure.RelMap r fun i => e.symm (e (x i))) ↔ Structure.RelMap r x
      simp }

/-- An `L`-structure transports along a bijection: `Z` carries an `L`-structure making `e` an
isomorphism. -/
theorem exists_inducedStructure {Y Z : Type*} [inst : L.Structure Y] (e : Y ≃ Z) :
    ∃ i : L.Structure Z, ∃ f : @FirstOrder.Language.Equiv L Y Z inst i, f.toEquiv = e :=
  ⟨inducedStructure e, inducedEquiv e, rfl⟩

end Transport

/-! ## Extending an injection -/

section Extend

/-- An injection defined on a subtype extends to an injection of the whole type, provided the
codomain has enough room outside the current range. -/
theorem exists_injective_extend {X Y U : Type} (g : X → Y) (hg : Function.Injective g)
    (h : X → U) (hh : Function.Injective h) (hcard : #Y ≤ #((Set.range h)ᶜ : Set U)) :
    ∃ h' : Y → U, Function.Injective h' ∧ ∀ x, h' (g x) = h x := by
  classical
  -- an injection of the complement of the range of `g` into the complement of the range of `h`
  obtain ⟨k⟩ : Nonempty (((Set.range g)ᶜ : Set Y) ↪ ((Set.range h)ᶜ : Set U)) :=
    (Cardinal.le_def _ _).1 ((Cardinal.mk_set_le _).trans hcard)
  set h' : Y → U := fun y => if hy : y ∈ Set.range g then h (Classical.choose hy)
    else (k ⟨y, hy⟩ : U) with hh'
  have hmem : ∀ (y : Y) (hy : y ∈ Set.range g), h' y = h (Classical.choose hy) := by
    intro y hy; rw [hh']; exact dif_pos hy
  have hnmem : ∀ (y : Y) (hy : y ∉ Set.range g), h' y = (k ⟨y, hy⟩ : U) := by
    intro y hy; rw [hh']; exact dif_neg hy
  refine ⟨h', ?_, ?_⟩
  · intro y₁ y₂ hy
    by_cases h₁ : y₁ ∈ Set.range g <;> by_cases h₂ : y₂ ∈ Set.range g
    · rw [hmem _ h₁, hmem _ h₂] at hy
      calc y₁ = g (Classical.choose h₁) := (Classical.choose_spec h₁).symm
        _ = g (Classical.choose h₂) := by rw [hh hy]
        _ = y₂ := Classical.choose_spec h₂
    · rw [hmem _ h₁, hnmem _ h₂] at hy
      exact absurd (⟨Classical.choose h₁, hy⟩ : (k ⟨y₂, h₂⟩ : U) ∈ Set.range h) (k ⟨y₂, h₂⟩).2
    · rw [hnmem _ h₁, hmem _ h₂] at hy
      exact absurd (⟨Classical.choose h₂, hy.symm⟩ : (k ⟨y₁, h₁⟩ : U) ∈ Set.range h)
        (k ⟨y₁, h₁⟩).2
    · rw [hnmem _ h₁, hnmem _ h₂] at hy
      exact congrArg Subtype.val (k.injective (Subtype.ext hy))
  · intro x
    rw [hmem _ (Set.mem_range_self x)]
    exact congrArg h (hg (Classical.choose_spec (Set.mem_range_self x)))

end Extend

/-! ## One step: realizing every finitely satisfiable small type -/

section Step

variable {L : FirstOrder.Language.{0, 0}} {γ : Type}

/-- `FinSat v S` says that every finite subset of the set `S` of formulas in one free variable is
realized in `X`, the parameters being interpreted by `v`. -/
def FinSat {X : Type} [L.Structure X] (v : γ → X) (S : Set (L.Formula (γ ⊕ Fin 1))) : Prop :=
  ∀ t : Finset (L.Formula (γ ⊕ Fin 1)), ↑t ⊆ S →
    ∃ a : X, ∀ φ ∈ t, φ.Realize (Sum.elim v fun _ => a)

/-- In a countable language there are at most `κ` formulas in one free variable with at most `κ`
parameters. -/
theorem mk_formula_le {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ ℵ₀) (hγ : #γ ≤ κ) :
    #(L.Formula (γ ⊕ Fin 1)) ≤ κ := by
  have h1 : #(L.Formula (γ ⊕ Fin 1)) ≤ #(Σ n, L.BoundedFormula (γ ⊕ Fin 1) n) :=
    Cardinal.mk_le_of_injective (f := fun φ => ⟨0, φ⟩) fun _ _ h => by simpa using h
  refine h1.trans (BoundedFormula.card_le.trans (max_le hκ ?_))
  have e1 : Cardinal.lift.{0, 0} #(γ ⊕ Fin 1) ≤ κ := by
    simp only [Cardinal.lift_id, Cardinal.mk_sum, Cardinal.mk_fin, Nat.cast_one]
    exact le_trans (add_le_add hγ (Cardinal.one_le_aleph0.trans hκ)) (Cardinal.add_eq_self hκ).le
  have e2 : Cardinal.lift.{0, 0} L.card ≤ κ := by
    rw [Cardinal.lift_id]
    exact hL.trans hκ
  exact le_trans (add_le_add e1 e2) (Cardinal.add_eq_self hκ).le

/-- **One step of the chain.**  Every structure of size at most `ν` has an elementary extension of
size at most `ν` realizing every finitely satisfiable set of formulas over at most `κ`
parameters, provided `ν ^ κ = ν`. -/
theorem exists_step (hL : L.card ≤ ℵ₀) {κ ν : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hγ : #γ ≤ κ)
    (hν : ℵ₀ ≤ ν) (hνp : ν ^ κ ≤ ν)
    {X : Type} [L.Structure X] [Nonempty X] (hX : #X ≤ ν) :
    ∃ (Y : Type) (_ : L.Structure Y) (f : X ↪ₑ[L] Y), #Y ≤ ν ∧
      ∀ (v : γ → X) (S : Set (L.Formula (γ ⊕ Fin 1))), FinSat v S →
        ∃ b : Y, ∀ φ ∈ S, φ.Realize (Sum.elim (fun i => f (v i)) fun _ => b) := by
  classical
  set ι : Type := (γ → X) × Set (L.Formula (γ ⊕ Fin 1)) with hι
  set p : ι → Set (L.Formula (X ⊕ Fin 1)) := fun q =>
    if FinSat q.1 q.2 then Formula.relabel (Sum.map q.1 id) '' q.2 else ∅ with hp
  have hrel : ∀ (v : γ → X) (φ : L.Formula (γ ⊕ Fin 1)) {Z : Type} [L.Structure Z]
      (g : X → Z) (b : Z),
      (Formula.relabel (Sum.map v id) φ).Realize (Sum.elim g fun _ => b) ↔
        φ.Realize (Sum.elim (fun i => g (v i)) fun _ => b) := by
    intro v φ Z _ g b
    rw [Formula.realize_relabel]
    refine iff_of_eq (congrArg _ ?_)
    funext z
    rcases z with i | j <;> rfl
  have hfin : ∀ q : ι, ∀ t : Finset (L.Formula (X ⊕ Fin 1)), ↑t ⊆ p q →
      ∃ a : X, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a) := by
    intro q t ht
    by_cases hq : FinSat q.1 q.2
    · have himg : ↑t ⊆ Formula.relabel (Sum.map q.1 id) '' q.2 := by
        rw [hp] at ht; simpa [hq] using ht
      choose g hg1 hg2 using fun ψ (h : ψ ∈ t) => himg h
      set t' : Finset (L.Formula (γ ⊕ Fin 1)) := t.attach.image fun ψ => g ψ.1 ψ.2 with ht'
      obtain ⟨a, ha⟩ := hq t' (by
        intro ψ hψ
        rw [ht'] at hψ
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
          true_and, Subtype.exists] at hψ
        obtain ⟨χ, hχ, rfl⟩ := hψ
        exact hg1 χ hχ)
      refine ⟨a, fun ψ hψ => ?_⟩
      have hmem : g ψ hψ ∈ t' := by
        rw [ht']
        exact Finset.mem_image.2 ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
      have := ha _ hmem
      have heq := hg2 ψ hψ
      rw [← heq, hrel q.1 (g ψ hψ) id a]
      exact this
    · rw [hp] at ht
      simp only [hq, if_false] at ht
      exact ⟨Classical.arbitrary X, fun ψ hψ => absurd (ht hψ) (Set.notMem_empty _)⟩
  have hιcard : #ι ≤ ν := by
    rw [hι]
    refine (Cardinal.mk_prod _ _).le.trans ?_
    have h1 : Cardinal.lift.{0} #(γ → X) ≤ ν := by
      rw [Cardinal.lift_id, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id]
      exact le_trans (Cardinal.power_le_power_left
        (Cardinal.mk_ne_zero X) hγ |>.trans
        (Cardinal.power_le_power_right hX)) hνp
    have h2 : Cardinal.lift.{0} #(Set (L.Formula (γ ⊕ Fin 1))) ≤ ν := by
      rw [Cardinal.lift_id, Cardinal.mk_set]
      refine le_trans (Cardinal.power_le_power_left two_ne_zero
        (mk_formula_le hκ hL hγ)) ?_
      refine le_trans (Cardinal.power_le_power_right ?_) hνp
      exact le_trans (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 2)).le) hν
    calc Cardinal.lift.{0} #(γ → X) * Cardinal.lift.{0} #(Set (L.Formula (γ ⊕ Fin 1)))
        ≤ ν * ν := mul_le_mul' h1 h2
      _ = ν := Cardinal.mul_eq_self hν
  obtain ⟨Y, instY, f, hYcard, hreal⟩ :=
    exists_elementaryExtension_realizing_card_le hL hν hX hιcard p hfin
  refine ⟨Y, instY, f, hYcard, fun v S hS => ?_⟩
  obtain ⟨b, hb⟩ := hreal (v, S)
  refine ⟨b, fun φ hφ => ?_⟩
  have : Formula.relabel (Sum.map v id) φ ∈ p (v, S) := by
    rw [hp]
    simp only [hS, if_true]
    exact ⟨φ, hφ, rfl⟩
  have h2 := hb _ this
  rwa [hrel v φ (fun x => f x) b] at h2

end Step

/-! ## Transfinite recursion by choice -/

section ChoiceRec

variable {J : Type*} [LinearOrder J] [WellFoundedLT J] {D : Type*} [Inhabited D]

open Classical in
/-- Transfinite recursion by choice: at stage `i` pick, if possible, a value satisfying `P`
relative to the values already chosen. -/
noncomputable def choiceRec (P : J → (J → D) → D → Prop) : J → D :=
  (IsWellFounded.wf (r := ((· < ·) : J → J → Prop))).fix fun i ih =>
    if hex : ∃ d, P i (fun j => if h : j < i then ih j h else default) d then hex.choose
    else default

open Classical in
/-- The defining equation of `choiceRec`. -/
theorem choiceRec_eq (P : J → (J → D) → D → Prop) (i : J) :
    choiceRec P i =
      if hex : ∃ d, P i (fun j => if _h : j < i then choiceRec P j else default) d then hex.choose
      else default :=
  WellFounded.fix_eq _ _ i

/-- If a good value exists at stage `i`, then the chosen value is good. -/
theorem choiceRec_spec (P : J → (J → D) → D → Prop)
    (hloc : ∀ (i : J) (g g' : J → D), (∀ j, j < i → g j = g' j) → ∀ d, P i g d → P i g' d)
    (i : J) (h : ∃ d, P i (choiceRec P) d) : P i (choiceRec P) (choiceRec P i) := by
  classical
  set g : J → D := fun j => if _h : j < i then choiceRec P j else default with hg
  have hag : ∀ j, j < i → g j = choiceRec P j := fun j hj => dif_pos hj
  have h' : ∃ d, P i g d := by
    obtain ⟨d, hd⟩ := h
    exact ⟨d, hloc i (choiceRec P) g (fun j hj => (hag j hj).symm) d hd⟩
  rw [choiceRec_eq, dif_pos h']
  exact hloc i g (choiceRec P) hag _ h'.choose_spec

end ChoiceRec

/-! ## Stages of the chain -/

section Stage

variable {L : FirstOrder.Language.{0, 0}} {U : Type}

/-- One stage of the construction: a subset of the ambient type `U` together with an
`L`-structure on it. -/
def Stage (L : FirstOrder.Language.{0, 0}) (U : Type) : Type :=
  Σ s : Set U, L.Structure ↥s

/-- The carrier of a stage. -/
@[reducible] def Stage.carrier (d : Stage L U) : Type := ↥d.1

instance Stage.structure (d : Stage L U) : L.Structure d.carrier := d.2

instance instInhabitedStage (L : FirstOrder.Language.{0, 0}) (U : Type) [Inhabited U] :
    Inhabited (Stage L U) :=
  ⟨⟨Set.univ, @junkStructure L ↥(Set.univ : Set U) ⟨⟨default, trivial⟩⟩⟩⟩

/-- `IsElemIncl d e` says that the carrier of `d` is contained in that of `e` and that the
inclusion is elementary. -/
def IsElemIncl (d e : Stage L U) : Prop :=
  d.1 ⊆ e.1 ∧ ∀ g : d.carrier → e.carrier, (∀ x, (g x : U) = (x : U)) →
    ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → d.carrier),
      φ.Realize (g ∘ x) ↔ φ.Realize x

/-- An elementary embedding respecting the ambient elements witnesses an elementary inclusion. -/
theorem isElemIncl_of_emb {d e : Stage L U} (hsub : d.1 ⊆ e.1)
    (E : d.carrier ↪ₑ[L] e.carrier) (hE : ∀ x, (E x : U) = (x : U)) : IsElemIncl d e :=
  ⟨hsub, fun g hg _n φ x => by
    have hgx : g ∘ x = (E : d.carrier → e.carrier) ∘ x :=
      funext fun i => Subtype.ext ((hg (x i)).trans (hE (x i)).symm)
    rw [hgx]
    exact E.map_formula φ x⟩

/-- The elementary embedding attached to an elementary inclusion. -/
def IsElemIncl.emb {d e : Stage L U} (h : IsElemIncl d e) : d.carrier ↪ₑ[L] e.carrier where
  toFun := Set.inclusion h.1
  map_formula' := fun {n} φ x => h.2 (Set.inclusion h.1) (fun _ => rfl) n φ x

@[simp]
theorem IsElemIncl.coe_emb {d e : Stage L U} (h : IsElemIncl d e) (x : d.carrier) :
    ((h.emb x : e.carrier) : U) = (x : U) := rfl

theorem IsElemIncl.refl (d : Stage L U) : IsElemIncl d d :=
  isElemIncl_of_emb subset_rfl (ElementaryEmbedding.refl L _) fun _ => rfl

theorem IsElemIncl.trans {d e f : Stage L U} (h₁ : IsElemIncl d e) (h₂ : IsElemIncl e f) :
    IsElemIncl d f :=
  isElemIncl_of_emb (h₁.1.trans h₂.1) (h₂.emb.comp h₁.emb) fun _ => rfl

/-- The elementary chain attached to a monotone family of stages. -/
def stageChain {J : Type} [Preorder J] (F : J → Stage L U)
    (h : ∀ i j, i ≤ j → IsElemIncl (F i) (F j)) : ElementaryChain L J where
  carrier := fun i => (F i).carrier
  struc := fun i => (F i).2
  map := fun i j hij => (h i j hij).emb
  map_self := fun _ _ => Subtype.ext rfl
  map_map := fun _ _ _ _ _ _ => Subtype.ext rfl

end Stage

/-! ## Building the chain -/

section Build

variable {L : FirstOrder.Language.{0, 0}} {γ U : Type} {ι : Type} [LinearOrder ι]

/-- The requirements on the stage produced at step `α`: it extends the base and all earlier
stages elementarily, it is small, and it realizes every finitely satisfiable set of formulas
over `γ` parameters taken from an earlier stage. -/
def Good (γ : Type) (base : Stage L U) (ν : Cardinal.{0}) (α : ι) (prev : ι → Stage L U)
    (d : Stage L U) : Prop :=
  IsElemIncl base d ∧ #d.1 ≤ ν ∧ (∀ β, β < α → IsElemIncl (prev β) d) ∧
    ∀ β, β < α → ∀ (v : γ → (prev β).carrier) (w : γ → d.carrier),
      (∀ i, (w i : U) = (v i : U)) → ∀ S : Set (L.Formula (γ ⊕ Fin 1)), FinSat v S →
        ∃ b : d.carrier, ∀ φ ∈ S, φ.Realize (Sum.elim w fun _ => b)

/-- `Good` only depends on the earlier stages. -/
theorem good_local (base : Stage L U) (ν : Cardinal.{0}) (α : ι) (g g' : ι → Stage L U)
    (hgg : ∀ j, j < α → g j = g' j) (d : Stage L U) :
    Good γ base ν α g d → Good γ base ν α g' d := by
  rintro ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, fun β hβ => ?_, fun β hβ => ?_⟩
  · rw [← hgg β hβ]; exact h3 β hβ
  · rw [← hgg β hβ]; exact h4 β hβ

/-- **The colimit-plus-one-step construction.**  Given a chain of small stages there is a single
small stage extending all of them elementarily and realizing every finitely satisfiable set of
formulas over `γ` parameters taken from one of them. -/
theorem exists_good_aux (hL : L.card ≤ ℵ₀) {κ ν : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hγ : #γ ≤ κ)
    (hν : ℵ₀ ≤ ν) (hνp : ν ^ κ ≤ ν) (hU : ν < #U)
    {J : Type} [LinearOrder J] [Nonempty J] (hJcard : #J ≤ ν)
    (G : J → Stage L U) (hGcard : ∀ i, #(G i).1 ≤ ν) (hGne : ∀ i, (G i).1.Nonempty)
    (hGchain : ∀ i j : J, i ≤ j → IsElemIncl (G i) (G j)) :
    ∃ d : Stage L U, (∀ i, IsElemIncl (G i) d) ∧ #d.1 ≤ ν ∧
      ∀ (i : J) (v : γ → (G i).carrier) (w : γ → d.carrier), (∀ n, (w n : U) = (v n : U)) →
        ∀ S : Set (L.Formula (γ ⊕ Fin 1)), FinSat v S →
          ∃ b : d.carrier, ∀ φ ∈ S, φ.Realize (Sum.elim w fun _ => b) := by
  classical
  have hexists : ∀ z : (stageChain G hGchain).Limit, ∃ (i : J) (x : (G i).carrier),
      (stageChain G hGchain).toLimit i x = z := (stageChain G hGchain).exists_toLimit
  have htoLim : ∀ (i : J) (x : (G i).carrier),
      (stageChain G hGchain).toLimitElementary i x = (stageChain G hGchain).toLimit i x :=
    fun _ _ => rfl
  -- a well-defined map from the limit back into the ambient type
  have hwd : ∀ (i j : J) (x : (G i).carrier) (y : (G j).carrier),
      (stageChain G hGchain).toLimit i x = (stageChain G hGchain).toLimit j y →
        ((x : U)) = ((y : U)) := by
    intro i j x y hxy
    obtain ⟨δ, hi, hj⟩ := exists_ge_ge i j
    have h1 : (hGchain i δ hi).emb x = (hGchain j δ hj).emb y := by
      apply ((stageChain G hGchain).toLimit δ).injective
      show (stageChain G hGchain).toLimit δ ((stageChain G hGchain).map i δ hi x) =
        (stageChain G hGchain).toLimit δ ((stageChain G hGchain).map j δ hj y)
      rw [(stageChain G hGchain).toLimit_map hi x, (stageChain G hGchain).toLimit_map hj y]
      exact hxy
    exact congrArg (fun z : (G δ).carrier => (z : U)) h1
  have hexu : ∀ z : (stageChain G hGchain).Limit, ∃ u : U, ∀ (i : J) (x : (G i).carrier),
      (stageChain G hGchain).toLimit i x = z → ((x : U)) = u := by
    intro z
    obtain ⟨i, x, hx⟩ := hexists z
    exact ⟨(x : U), fun j y hy => hwd j i y x (hy.trans hx.symm)⟩
  choose hmap hmapspec using hexu
  have hmap_of : ∀ (i : J) (x : (G i).carrier),
      hmap ((stageChain G hGchain).toLimit i x) = ((x : U)) :=
    fun i x => (hmapspec ((stageChain G hGchain).toLimit i x) i x rfl).symm
  have hmapinj : Function.Injective hmap := by
    intro z z' hzz
    obtain ⟨i, x, rfl⟩ := hexists z
    obtain ⟨j, y, rfl⟩ := hexists z'
    rw [hmap_of, hmap_of] at hzz
    obtain ⟨δ, hi, hj⟩ := exists_ge_ge i j
    have h1 : (stageChain G hGchain).map i δ hi x = (stageChain G hGchain).map j δ hj y :=
      Subtype.ext hzz
    rw [← (stageChain G hGchain).toLimit_map hi x, ← (stageChain G hGchain).toLimit_map hj y, h1]
  -- the limit is small and nonempty
  have hXcard : #(stageChain G hGchain).Limit ≤ ν := by
    refine (stageChain G hGchain).mk_limit_le_of_lift_mk_le hν ?_ ?_
    · rw [Cardinal.lift_id]; exact hJcard
    · intro i; rw [Cardinal.lift_id]; exact hGcard i
  obtain ⟨u₀, hu₀⟩ := hGne (Classical.arbitrary J)
  haveI : Nonempty (stageChain G hGchain).Limit :=
    ⟨(stageChain G hGchain).toLimit (Classical.arbitrary J) ⟨u₀, hu₀⟩⟩
  -- one step
  obtain ⟨Y, instY, f, hYcard, hstep⟩ :=
    exists_step (L := L) (γ := γ) hL hκ hγ hν hνp (X := (stageChain G hGchain).Limit) hXcard
  letI := instY
  -- place `Y` inside the ambient type, extending `hmap`
  have hroom : #Y ≤ #((Set.range hmap)ᶜ : Set U) := by
    refine hYcard.trans ?_
    by_contra hc
    rw [not_le] at hc
    have h1 : #U ≤ ν + ν := by
      rw [← Cardinal.mk_sum_compl (Set.range hmap)]
      exact add_le_add (Cardinal.mk_range_le.trans hXcard) hc.le
    rw [Cardinal.add_eq_self hν] at h1
    exact absurd h1 (not_le.2 hU)
  obtain ⟨h', h'inj, h'ext⟩ :=
    exists_injective_extend (fun z : (stageChain G hGchain).Limit => f z) f.injective hmap
      hmapinj hroom
  obtain ⟨instT, iso, hiso⟩ := exists_inducedStructure (L := L) (Equiv.ofInjective h' h'inj)
  letI := instT
  have hisocoe : ∀ y : Y, ((iso y : ↥(Set.range h')) : U) = h' y := by
    intro y
    have h1 : (iso y : ↥(Set.range h')) = Equiv.ofInjective h' h'inj y := by
      rw [← hiso]; rfl
    rw [h1]
    rfl
  refine ⟨⟨Set.range h', instT⟩, ?_, Cardinal.mk_range_le.trans hYcard, ?_⟩
  · intro i
    refine isElemIncl_of_emb ?_ ((iso.toElementaryEmbedding.comp f).comp
      ((stageChain G hGchain).toLimitElementary i)) ?_
    · intro u hu
      exact ⟨f ((stageChain G hGchain).toLimit i ⟨u, hu⟩), by rw [h'ext, hmap_of]⟩
    · intro x
      show ((iso (f ((stageChain G hGchain).toLimitElementary i x))) : U) = _
      rw [hisocoe, h'ext, htoLim, hmap_of]
  · intro i v w hw S hS
    have hFinSat' : FinSat (fun n => (stageChain G hGchain).toLimitElementary i (v n)) S := by
      intro t ht
      obtain ⟨a, ha⟩ := hS t ht
      exact (exists_realize_finset_iff ((stageChain G hGchain).toLimitElementary i) v t).1 ⟨a, ha⟩
    obtain ⟨b, hb⟩ :=
      hstep (fun n => (stageChain G hGchain).toLimitElementary i (v n)) S hFinSat'
    refine ⟨iso b, fun φ hφ => ?_⟩
    have key := (iso.toElementaryEmbedding.map_formula φ
      (Sum.elim (fun n => f ((stageChain G hGchain).toLimitElementary i (v n))) fun _ => b)).2
      (hb φ hφ)
    have hfun : (fun z => (iso.toElementaryEmbedding z : ↥(Set.range h'))) ∘
        (Sum.elim (fun n => f ((stageChain G hGchain).toLimitElementary i (v n)))
          fun _ : Fin 1 => b) =
        Sum.elim w fun _ : Fin 1 => (iso b : ↥(Set.range h')) := by
      funext z
      rcases z with n | m
      · refine Subtype.ext ?_
        show ((iso (f ((stageChain G hGchain).toLimitElementary i (v n)))) : U) = _
        rw [hisocoe, h'ext, htoLim, hmap_of]
        simp only [Sum.elim_inl]
        exact (hw n).symm
      · rfl
    rw [hfun] at key
    exact key

/-- **The successor/limit step.**  Given a coherent family of earlier stages there is a good
stage at step `α`. -/
theorem exists_good (hL : L.card ≤ ℵ₀) {κ ν : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hγ : #γ ≤ κ)
    (hν : ℵ₀ ≤ ν) (hνp : ν ^ κ ≤ ν) (hU : ν < #U) (hιcard : #ι ≤ ν)
    {base : Stage L U} (hbaseNE : base.1.Nonempty) (hbase : #base.1 ≤ ν)
    (α : ι) (F : ι → Stage L U)
    (hbelow : ∀ β, β < α → IsElemIncl base (F β) ∧ #(F β).1 ≤ ν)
    (hchain : ∀ β β', β < α → β' < α → β ≤ β' → IsElemIncl (F β) (F β')) :
    ∃ d : Stage L U, Good γ base ν α F d := by
  classical
  by_cases hne : ∃ β : ι, β < α
  swap
  · exact ⟨base, IsElemIncl.refl base, hbase, fun β hβ => absurd ⟨β, hβ⟩ hne,
      fun β hβ => absurd ⟨β, hβ⟩ hne⟩
  obtain ⟨β₀, hβ₀⟩ := hne
  haveI : Nonempty {β : ι // β < α} := ⟨⟨β₀, hβ₀⟩⟩
  obtain ⟨d, hd1, hd2, hd3⟩ :=
    exists_good_aux (L := L) (γ := γ) hL hκ hγ hν hνp hU
      (J := {β : ι // β < α}) ((Cardinal.mk_subtype_le _).trans hιcard)
      (fun β => F β.1) (fun β => (hbelow β.1 β.2).2)
      (fun β => Set.Nonempty.mono (hbelow β.1 β.2).1.1 hbaseNE)
      (fun i j hij => hchain i.1 j.1 i.2 j.2 hij)
  refine ⟨d, ((hbelow β₀ hβ₀).1).trans (hd1 ⟨β₀, hβ₀⟩), hd2, fun β hβ => hd1 ⟨β, hβ⟩, ?_⟩
  intro β hβ v w hw S hS
  exact hd3 ⟨β, hβ⟩ v w hw S hS

variable [WellFoundedLT ι] [Inhabited U]

/-- Every stage produced by the recursion is good. -/
theorem good_choiceRec (hL : L.card ≤ ℵ₀) {κ ν : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hγ : #γ ≤ κ)
    (hν : ℵ₀ ≤ ν) (hνp : ν ^ κ ≤ ν) (hU : ν < #U) (hιcard : #ι ≤ ν)
    {base : Stage L U} (hbaseNE : base.1.Nonempty) (hbase : #base.1 ≤ ν) (α : ι) :
    Good γ base ν α (choiceRec (Good γ base ν)) (choiceRec (Good γ base ν) α) := by
  induction α using IsWellFounded.induction (r := ((· < ·) : ι → ι → Prop)) with
  | _ α ih =>
    refine choiceRec_spec (Good γ base ν) (fun i g g' hgg d => good_local base ν i g g' hgg d) α ?_
    refine exists_good hL hκ hγ hν hνp hU hιcard hbaseNE hbase α _ ?_ ?_
    · exact fun β hβ => ⟨(ih β hβ).1, (ih β hβ).2.1⟩
    · intro β β' hβ hβ' hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact IsElemIncl.refl _
      · exact (ih β' hβ').2.2.1 β hlt

/-- **The chain construction.**  The colimit of the chain realizes every finitely satisfiable
set of formulas over `γ` parameters. -/
theorem exists_chain_saturated (hL : L.card ≤ ℵ₀) {κ ν : Cardinal.{0}} (hκ : ℵ₀ ≤ κ)
    (hγ : #γ ≤ κ) (hν : ℵ₀ ≤ ν) (hνp : ν ^ κ ≤ ν) (hU : ν < #U) [Nonempty ι] (hιcard : #ι ≤ ν)
    (hcof : ∀ f : γ → ι, ∃ α : ι, ∀ i, f i ≤ α) (hnomax : ∀ α : ι, ∃ β : ι, α < β)
    (base : Stage L U) (hbaseNE : base.1.Nonempty) (hbase : #base.1 ≤ ν) :
    ∃ (N : Type) (instN : L.Structure N) (_ : base.carrier ↪ₑ[L] N), #N ≤ ν ∧
      ∀ (v : γ → N) (S : Set (L.Formula (γ ⊕ Fin 1))), @FinSat L γ N instN v S →
        ∃ b : N, ∀ φ ∈ S, @Formula.Realize L N instN _ φ (Sum.elim v fun _ => b) := by
  classical
  set F : ι → Stage L U := choiceRec (Good γ base ν) with hF
  have hGood : ∀ α : ι, Good γ base ν α F (F α) := fun α =>
    good_choiceRec hL hκ hγ hν hνp hU hιcard hbaseNE hbase α
  have hchain : ∀ α β : ι, α ≤ β → IsElemIncl (F α) (F β) := by
    intro α β hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact IsElemIncl.refl _
    · exact (hGood β).2.2.1 α hlt
  have hexists : ∀ z : (stageChain F hchain).Limit, ∃ (i : ι) (x : (F i).carrier),
      (stageChain F hchain).toLimit i x = z := (stageChain F hchain).exists_toLimit
  have htoLim : ∀ (i : ι) (x : (F i).carrier),
      (stageChain F hchain).toLimitElementary i x = (stageChain F hchain).toLimit i x :=
    fun _ _ => rfl
  have hNcard : #(stageChain F hchain).Limit ≤ ν := by
    refine (stageChain F hchain).mk_limit_le_of_lift_mk_le hν ?_ ?_
    · rw [Cardinal.lift_id]; exact hιcard
    · intro i; rw [Cardinal.lift_id]; exact (hGood i).2.1
  refine ⟨(stageChain F hchain).Limit, inferInstance,
    ((stageChain F hchain).toLimitElementary (Classical.arbitrary ι)).comp
      ((hGood (Classical.arbitrary ι)).1.emb), hNcard, ?_⟩
  intro v S hS
  -- pull the parameters back to a single stage
  have hpull : ∀ i : γ, ∃ (α : ι) (x : (F α).carrier),
      (stageChain F hchain).toLimit α x = v i := fun i => hexists (v i)
  choose α x hx using hpull
  obtain ⟨δ, hδ⟩ := hcof α
  set v' : γ → (F δ).carrier := fun i => (stageChain F hchain).map (α i) δ (hδ i) (x i) with hv'
  have hv'lim : ∀ i, (stageChain F hchain).toLimit δ (v' i) = v i := by
    intro i
    rw [hv', (stageChain F hchain).toLimit_map (hδ i) (x i)]
    exact hx i
  have hFinSat' : @FinSat L γ (F δ).carrier _ v' S := by
    intro t ht
    obtain ⟨a, ha⟩ := hS t ht
    refine (exists_realize_finset_iff ((stageChain F hchain).toLimitElementary δ) v' t).2 ⟨a, ?_⟩
    have hveq : (fun i => (stageChain F hchain).toLimitElementary δ (v' i)) = v := by
      funext i; rw [htoLim, hv'lim i]
    rw [hveq]
    exact ha
  obtain ⟨δ', hδ'⟩ := hnomax δ
  obtain ⟨b, hb⟩ := (hGood δ').2.2.2 δ hδ' v'
    (fun i => (hchain δ δ' hδ'.le).emb (v' i)) (fun _ => rfl) S hFinSat'
  refine ⟨(stageChain F hchain).toLimit δ' b, fun φ hφ => ?_⟩
  have key := ((stageChain F hchain).toLimitElementary δ').map_formula φ
    (Sum.elim (fun i => (hchain δ δ' hδ'.le).emb (v' i)) fun _ : Fin 1 => b)
  have hfun : (fun z => ((stageChain F hchain).toLimitElementary δ' z)) ∘
      (Sum.elim (fun i => (hchain δ δ' hδ'.le).emb (v' i)) fun _ : Fin 1 => b) =
      Sum.elim v fun _ : Fin 1 => (stageChain F hchain).toLimit δ' b := by
    funext z
    rcases z with i | j
    · show (stageChain F hchain).toLimitElementary δ'
        ((stageChain F hchain).map δ δ' hδ'.le (v' i)) = _
      rw [htoLim, (stageChain F hchain).toLimit_map hδ'.le (v' i)]
      exact hv'lim i
    · rfl
  rw [hfun] at key
  exact key.2 (hb φ hφ)

end Build

/-! ## Ordinal bookkeeping -/

section Ordinals

/-- A family of at most `κ` ordinals below `κ⁺` is bounded: `κ⁺` is regular. -/
theorem exists_upper_bound_toType {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) {A : Type} (hA : #A ≤ κ)
    (f : A → (Order.succ κ).ord.ToType) : ∃ α, ∀ a, f a ≤ α := by
  have hreg : (Order.succ κ).IsRegular := Cardinal.isRegular_succ hκ
  have hglt : ∀ a, ((Ordinal.ToType.toOrd (f a) : Set.Iio (Order.succ κ).ord) : Ordinal.{0}) <
      (Order.succ κ).ord := fun a => (Ordinal.ToType.toOrd (f a)).2
  have hsup : (⨆ a, ((Ordinal.ToType.toOrd (f a) : Set.Iio (Order.succ κ).ord) : Ordinal.{0})) <
      (Order.succ κ).ord := by
    refine Ordinal.iSup_lt_of_lt_cof ?_ hglt
    rw [hreg.cof_ord]
    exact lt_of_le_of_lt hA (Order.lt_succ κ)
  refine ⟨Ordinal.ToType.mk ⟨_, hsup⟩, fun a => ?_⟩
  rw [← Ordinal.ToType.mk.apply_symm_apply (f a)]
  refine Ordinal.ToType.mk.monotone ?_
  exact le_ciSup Ordinal.bddAbove_of_small a

/-- `κ⁺` is a limit ordinal, so its order type has no maximum. -/
theorem exists_gt_toType {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (α : (Order.succ κ).ord.ToType) :
    ∃ β, α < β := by
  have hlim : Order.IsSuccLimit (Order.succ κ).ord :=
    Cardinal.isSuccLimit_ord (hκ.trans (Order.le_succ κ))
  have h1 : ((Ordinal.ToType.toOrd α : Set.Iio (Order.succ κ).ord) : Ordinal.{0}) <
      (Order.succ κ).ord := (Ordinal.ToType.toOrd α).2
  refine ⟨Ordinal.ToType.mk ⟨_, hlim.succ_lt h1⟩, ?_⟩
  have h3 : Ordinal.ToType.toOrd α <
      (⟨_, hlim.succ_lt h1⟩ : Set.Iio (Order.succ κ).ord) :=
    Subtype.coe_lt_coe.1 (Order.lt_succ _)
  have h2 : Ordinal.ToType.mk (Ordinal.ToType.toOrd α) <
      Ordinal.ToType.mk ⟨_, hlim.succ_lt h1⟩ := Ordinal.ToType.mk.strictMono h3
  rwa [Ordinal.ToType.mk.apply_symm_apply] at h2

end Ordinals

/-! ## The main theorem -/

section Main

variable {L : FirstOrder.Language.{0, 0}}

/-- Relabelling the parameters of a formula along `r` amounts to precomposing the assignment. -/
theorem realize_relabel_sumMap {α β Z : Type} [L.Structure Z] (r : α → β)
    (φ : L.Formula (α ⊕ Fin 1)) (v : β → Z) (b : Z) :
    (Formula.relabel (Sum.map r id) φ).Realize (Sum.elim v fun _ => b) ↔
      φ.Realize (Sum.elim (fun a => v (r a)) fun _ => b) := by
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg _ ?_)
  funext z
  rcases z with a | j <;> rfl

/-- **Existence of `κ⁺`-saturated elementary extensions.**  Every model of `T` has an elementary
extension `N` of cardinality at most `(κ + #M) ^ κ` in which every complete `1`-type over a
parameter set of size at most `κ` is realised. -/
theorem exists_saturated_elementaryExtension (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (M : T.ModelType.{0, 0, 0}) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    ∃ (N : T.ModelType.{0, 0, 0}) (_ : M ↪ₑ[L] N),
      (∀ A : Set N, #A ≤ κ → ∀ p : S₁ L A, ∃ a : N, typeOfElem A a = p) ∧
        #N ≤ (κ + #M) ^ κ := by
  classical
  -- cardinal bookkeeping
  set ν : Cardinal.{0} := (κ + #M) ^ κ with hνdef
  have hκM : ℵ₀ ≤ κ + #M := hκ.trans (self_le_add_right _ _)
  have hν : ℵ₀ ≤ ν := hκM.trans (Cardinal.self_le_power _ (Cardinal.one_le_aleph0.trans hκ))
  have hνp : ν ^ κ ≤ ν := by
    rw [hνdef, ← Cardinal.power_mul, Cardinal.mul_eq_self hκ]
  have hMν : #M ≤ ν := le_trans (self_le_add_left _ _)
    (Cardinal.self_le_power _ (Cardinal.one_le_aleph0.trans hκ))
  have hsucc : Order.succ κ ≤ ν := by
    refine Order.succ_le_of_lt (lt_of_lt_of_le (Cardinal.cantor κ) ?_)
    refine Cardinal.power_le_power_right ?_
    exact le_trans (by exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 2)).le) hκM
  -- the ambient type
  set U : Type := Set ν.out with hUdef
  haveI : Inhabited U := ⟨(∅ : Set ν.out)⟩
  have hU : ν < #U := by
    rw [hUdef, Cardinal.mk_set, Cardinal.mk_out]
    exact Cardinal.cantor ν
  -- the parameter index and the length of the chain
  set γ : Type := κ.ord.ToType with hγdef
  have hγ : #γ = κ := Cardinal.mk_ord_toType κ
  set ι : Type := (Order.succ κ).ord.ToType with hιdef
  have hιcard : #ι ≤ ν := by rw [hιdef, Cardinal.mk_ord_toType]; exact hsucc
  haveI : Nonempty ι := by
    rw [← Cardinal.mk_ne_zero_iff, hιdef, Cardinal.mk_ord_toType]
    exact ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos (hκ.trans (Order.le_succ κ)))
  -- a copy of `M` inside the ambient type
  obtain ⟨e₀⟩ : Nonempty ((M : Type) ↪ U) := (Cardinal.le_def _ _).1 (hMν.trans hU.le)
  obtain ⟨instB, isoB, hisoB⟩ :=
    exists_inducedStructure (L := L) (Equiv.ofInjective e₀ e₀.injective)
  letI := instB
  have hbaseNE : (Set.range e₀ : Set U).Nonempty := ⟨e₀ (Classical.arbitrary M), ⟨_, rfl⟩⟩
  obtain ⟨N₀, instN, g, hNcard, hsat⟩ :=
    exists_chain_saturated (L := L) (γ := γ) (ι := ι) hL hκ hγ.le hν hνp hU hιcard
      (fun f => exists_upper_bound_toType hκ (le_of_eq hγ) f) (fun α => exists_gt_toType hκ α)
      ⟨Set.range e₀, instB⟩ hbaseNE (Cardinal.mk_range_le.trans hMν)
  letI := instN
  have embB : (M : Type) ↪ₑ[L] Stage.carrier (⟨Set.range e₀, instB⟩ : Stage L U) :=
    isoB.toElementaryEmbedding
  set f : (M : Type) ↪ₑ[L] N₀ := g.comp embB with hf
  haveI : Nonempty N₀ := ⟨f (Classical.arbitrary M)⟩
  haveI : N₀ ⊨ T := (f.theory_model_iff T).1 M.is_model
  have main : ∀ A : Set N₀, #A ≤ κ → ∀ p : S₁ L A, ∃ a : N₀, typeOfElem A a = p := by
    intro A hA p
    -- name the parameters by `γ`
    obtain ⟨r⟩ : Nonempty ((A : Type) ↪ γ) := (Cardinal.le_def _ _).1 (hA.trans hγ.ge)
    set v : γ → N₀ := fun c => if h : ∃ a : (A : Type), r a = c then ((h.choose : A) : N₀)
      else Classical.arbitrary N₀ with hv
    have hvr : ∀ a : (A : Type), v (r a) = (a : N₀) := by
      intro a
      have hex : ∃ a' : (A : Type), r a' = r a := ⟨a, rfl⟩
      rw [hv]
      simp only [dif_pos hex]
      exact congrArg _ (r.injective hex.choose_spec)
    have hveq : (fun a : (A : Type) => v (r a)) = fun a : (A : Type) => (a : N₀) := funext hvr
    set S : Set (L.Formula (γ ⊕ Fin 1)) :=
      Formula.relabel (Sum.map (fun a : (A : Type) => r a) id) '' typeForms p with hS
    have hFinSat : @FinSat L γ N₀ instN v S := by
      intro t ht
      have hts : ∀ χ ∈ t, ∃ φ, φ ∈ typeForms p ∧
          Formula.relabel (Sum.map (fun a : (A : Type) => r a) id) φ = χ := by
        intro χ hχ
        have h0 := ht hχ
        rw [hS] at h0
        exact h0
      choose ψ hψ1 hψ2 using hts
      have hsubT : ↑(t.attach.image fun χ : {x // x ∈ t} => ψ χ.1 χ.2) ⊆ typeForms p := by
        intro χ hχ
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
          true_and, Subtype.exists] at hχ
        obtain ⟨χ', hχ', heq⟩ := hχ
        rw [← heq]
        exact hψ1 χ' hχ'
      obtain ⟨a, ha⟩ := exists_realize_of_finset_typeForms p _ hsubT
      refine ⟨a, fun χ hχ => ?_⟩
      have hmem : ψ χ hχ ∈ t.attach.image fun χ' => ψ χ'.1 χ'.2 :=
        Finset.mem_image.2 ⟨⟨χ, hχ⟩, Finset.mem_attach _ _, rfl⟩
      have h1 := ha _ hmem
      rw [← hψ2 χ hχ, realize_relabel_sumMap, hveq]
      exact h1
    obtain ⟨b, hb⟩ := hsat v S hFinSat
    refine ⟨b, typeOfElem_eq_of_forall_realize p b fun φ hφ => ?_⟩
    have hmem : Formula.relabel (Sum.map (fun a : (A : Type) => r a) id) φ ∈ S := by
      rw [hS]; exact ⟨φ, hφ, rfl⟩
    have h1 := hb _ hmem
    rw [realize_relabel_sumMap, hveq] at h1
    exact h1
  exact ⟨Theory.ModelType.of T N₀, f, main, hNcard⟩

/-- **`κ`-saturated elementary extensions**, in the exact shape asked for by the callers: types
over parameter sets of size *strictly less than* `κ` are realised. -/
theorem exists_saturated_elementaryExtension_lt (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (M : T.ModelType.{0, 0, 0}) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    ∃ (N : T.ModelType.{0, 0, 0}) (_ : M ↪ₑ[L] N),
      (∀ A : Set N, #A < κ → ∀ p : S₁ L A, ∃ a : N, typeOfElem A a = p) ∧
        #N ≤ (κ + #M) ^ κ := by
  obtain ⟨N, f, hsat, hcard⟩ := exists_saturated_elementaryExtension hL M hκ
  exact ⟨N, f, fun A hA p => hsat A hA.le p, hcard⟩

/-- The same statement in the `realizedTypes` phrasing used by
`Submission.Morley.IsSaturated`. -/
theorem exists_saturated_elementaryExtension_realizedTypes (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (M : T.ModelType.{0, 0, 0}) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) :
    ∃ (N : T.ModelType.{0, 0, 0}) (_ : M ↪ₑ[L] N),
      (∀ A : Set N, #A ≤ κ → ∀ p : ((L[[A]]).completeTheory N).CompleteType (Fin 1),
          p ∈ ((L[[A]]).completeTheory N).realizedTypes N (Fin 1)) ∧
        #N ≤ (κ + #M) ^ κ := by
  obtain ⟨N, f, hsat, hcard⟩ := exists_saturated_elementaryExtension hL M hκ
  exact ⟨N, f, fun A hA p => mem_realizedTypes_one_iff.2 (hsat A hA p), hcard⟩

/-- A model realizing every `1`-type over a parameter set of size at most `κ` and of cardinality
at most `κ⁺` is **saturated**. -/
theorem isSaturated_of_forall_realize {T : L.Theory} {N : T.ModelType.{0, 0, 0}}
    {κ : Cardinal.{0}} (h : ∀ A : Set N, #A ≤ κ → ∀ p : S₁ L A, ∃ a : N, typeOfElem A a = p)
    (hN : #N ≤ Order.succ κ) : IsSaturated N := by
  intro A hA p
  exact mem_realizedTypes_one_iff.2 (h A (Order.lt_succ_iff.1 (lt_of_lt_of_le hA hN)) p)

/-- **Existence of a saturated elementary extension** whenever the cardinal arithmetic allows
it, i.e. whenever `(κ + #M) ^ κ ≤ κ⁺`. -/
theorem exists_isSaturated_elementaryExtension (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (M : T.ModelType.{0, 0, 0}) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ)
    (hcard : (κ + #M) ^ κ ≤ Order.succ κ) :
    ∃ (N : T.ModelType.{0, 0, 0}) (_ : M ↪ₑ[L] N), IsSaturated N ∧ #N ≤ Order.succ κ := by
  obtain ⟨N, f, hsat, hNcard⟩ := exists_saturated_elementaryExtension hL M hκ
  exact ⟨N, f, isSaturated_of_forall_realize hsat (hNcard.trans hcard), hNcard.trans hcard⟩

end Main

end Submission.Morley
