import Mathlib
import Submission.Morley.Vaught

/-!
# The pair language, and countable Vaughtian pairs

This file develops the first two stages of the proof of Vaught's two-cardinal theorem
(`Submission.Morley.VaughtTwoCardinal`, stated in `Submission.Morley.Vaught`): the *pair
language* together with the transfer of "the predicate names an elementary substructure", and the
construction of a **countable** Vaughtian pair out of an arbitrary one.

## The pair language

Given a language `L`, the *pair language* is `L.sum predLang`, where `predLang` has a single
unary relation symbol.  A structure for the pair language is an `L`-structure `M` together with a
distinguished subset `predSet L M`.

Instead of proving a syntactic relativisation lemma by induction on formulas — which is the usual
route, and which produces an operation `φ ↦ φ^P` on formulas — we axiomatise the situation
"`predSet L M` is an elementary substructure of `M`" by an explicit scheme of pair-language
*sentences*, `pairTheory L`, expressing the Tarski–Vaught test.  This is strictly more convenient
downstream: being a theory, the scheme transfers along elementary embeddings of pairs in **both**
directions (whereas a relativisation lemma only transfers along one), which is exactly what both
the Löwenheim–Skolem step and the later chain constructions need.  Conversely,
`predElementarySubstructure` turns any model of `pairTheory L` into an honest
`L.ElementarySubstructure`, via Mathlib's Tarski–Vaught test; closure of the predicate under the
function symbols of `L` is *derived* from the scheme rather than assumed.

## Main definitions

* `Submission.Morley.predLang`, `Submission.Morley.predSet`: the extra unary predicate and the
  set it names.
* `Submission.Morley.pairStructure`: the pair-language structure attached to a subset.
* `Submission.Morley.pairTheory`: the Tarski–Vaught scheme, plus nonemptiness of the predicate.
* `Submission.Morley.CountableVPair`: a countable Vaughtian pair, packaged.

## Main results

* `Submission.Morley.models_pairTheory_iff`: what it means to model `pairTheory L`.
* `Submission.Morley.predElementarySubstructure`: in a model of `pairTheory L`, the predicate is
  an `L`-elementary substructure.
* `Submission.Morley.models_pairTheory_of_elementarySubstructure`: conversely, a nonempty
  elementary substructure makes `pairTheory L` true in the associated pair structure.
* `Submission.Morley.exists_mem_predSet_realize`: the consistency statement driving the
  back-and-forth step — a type over a tuple from the predicate that is realised anywhere is
  finitely realised *inside* the predicate.
* `Submission.Morley.nonempty_countableVPair`: **a Vaughtian pair yields a countable Vaughtian
  pair** (downward Löwenheim–Skolem carried out in the pair language).
* `Submission.Morley.hasTwoCardinalModel_of_boundedFormula`: the final packaging step, turning a
  model with a parameter-definable set of prescribed cardinality into a `HasTwoCardinalModel`
  witness.

## What is *not* here

Vaught's two-cardinal theorem itself is not proved.  What remains, starting from
`nonempty_countableVPair`, is: an `ω`-chain of countable pairs realising prescribed types (which
needs compactness over the elementary diagram in the pair language), a back-and-forth argument
making the two sides of the resulting pair isomorphic, and an `ω₁`-length chain of copies of that
pair.  See the "Status" section of `Submission.Morley.Vaught`.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

/-! ## The language with one extra unary predicate -/

/-- The language with a single unary relation symbol and no other symbols. -/
def predLang : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := fun n => PLift (n = 1)

/-- The unique relation symbol of `predLang`. -/
def predSym : predLang.Relations 1 := ⟨rfl⟩

instance (n : ℕ) : IsEmpty (predLang.Functions n) := inferInstanceAs (IsEmpty Empty)

instance : Countable predLang.Symbols := by
  have h : Function.Injective (fun _ : predLang.Symbols => (0 : ℕ)) := by
    rintro (⟨n, f⟩ | ⟨n, ⟨rfl⟩⟩) (⟨m, g⟩ | ⟨m, ⟨rfl⟩⟩) _
    · exact isEmptyElim f
    · exact isEmptyElim f
    · exact isEmptyElim g
    · rfl
  exact h.countable

theorem predLang_card_le : predLang.card ≤ ℵ₀ :=
  Cardinal.mk_le_aleph0 (α := predLang.Symbols)

variable {L : FirstOrder.Language.{0, 0}}

/-- The inclusion of `L` into the pair language. -/
abbrev pairInl (L : FirstOrder.Language.{0, 0}) : L →ᴸ L.sum predLang := LHom.sumInl

theorem pairLang_card_le (hL : L.card ≤ ℵ₀) : (L.sum predLang).card ≤ ℵ₀ := by
  rw [Language.card_sum]
  simpa using add_le_of_le (le_refl ℵ₀) (by simpa using hL) (by simpa using predLang_card_le)

/-- The set named by the extra unary predicate. -/
def predSet (L : FirstOrder.Language.{0, 0}) (M : Type) [(L.sum predLang).Structure M] : Set M :=
  {x | @Structure.RelMap (L.sum predLang) M _ 1 (Sum.inr predSym) fun _ => x}

/-! ### Building a pair structure from a subset -/

/-- The pair-language structure on an `L`-structure `M` interpreting the new predicate as `s`. -/
@[reducible]
def pairStructure {M : Type} [L.Structure M] (s : Set M) : (L.sum predLang).Structure M where
  funMap {n} f x :=
    Sum.elim (fun g : L.Functions n => Structure.funMap g x) (fun g => isEmptyElim g) f
  RelMap {n} r x :=
    Sum.elim (fun R : L.Relations n => Structure.RelMap R x)
      (fun R : predLang.Relations n => x (Fin.cast R.down.symm 0) ∈ s) r

theorem pairStructure_isExpansionOn {M : Type} [inst : L.Structure M] (s : Set M) :
    @LHom.IsExpansionOn L (L.sum predLang) (pairInl L) M inst (pairStructure s) :=
  @LHom.IsExpansionOn.mk L (L.sum predLang) (pairInl L) M inst (pairStructure s)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem predSet_pairStructure {M : Type} [L.Structure M] (s : Set M) :
    @predSet L M (pairStructure s) = s := rfl

/-! ## The Tarski–Vaught scheme in the pair language -/

/-- The atomic formula saying that the `k`-th variable satisfies the new predicate. -/
def predVarF (L : FirstOrder.Language.{0, 0}) {α : Type} {m : ℕ} (k : Fin m) :
    (L.sum predLang).BoundedFormula α m :=
  Relations.boundedFormula (Sum.inr predSym) fun _ => Term.var (Sum.inr k)

@[simp]
theorem realize_predVarF {M : Type} [(L.sum predLang).Structure M] {α : Type} {m : ℕ}
    (k : Fin m) (v : α → M) (xs : Fin m → M) :
    (predVarF L k).Realize v xs ↔ xs k ∈ predSet L M := by
  rw [predVarF, BoundedFormula.realize_rel]
  rfl

/-- `allsPred L l ψ` universally quantifies the `l` free bound variables of `ψ`, relativised to
the new unary predicate. -/
def allsPred (L : FirstOrder.Language.{0, 0}) :
    ∀ (l : ℕ), (L.sum predLang).BoundedFormula Empty l → (L.sum predLang).Sentence
  | 0, ψ => ψ
  | l + 1, ψ => allsPred L l (∀' (predVarF L (Fin.last l) ⟹ ψ))

theorem realize_allsPred {M : Type} [(L.sum predLang).Structure M] :
    ∀ (l : ℕ) (ψ : (L.sum predLang).BoundedFormula Empty l),
      M ⊨ allsPred L l ψ ↔
        ∀ xs : Fin l → M, (∀ i, xs i ∈ predSet L M) → ψ.Realize default xs := by
  intro l
  induction l with
  | zero =>
    intro ψ
    constructor
    · intro h xs _
      rwa [Subsingleton.elim xs default]
    · intro h
      exact h default (fun i => i.elim0)
  | succ l ih =>
    intro ψ
    rw [allsPred, ih]
    constructor
    · intro h ys hys
      have := h (fun i => ys i.castSucc) (fun i => hys _)
      rw [BoundedFormula.realize_all] at this
      have h2 := this (ys (Fin.last l))
      rw [BoundedFormula.realize_imp, realize_predVarF, Fin.snoc_last] at h2
      have heq : (Fin.snoc (fun i => ys i.castSucc) (ys (Fin.last l)) : Fin (l + 1) → M) = ys :=
        Fin.snoc_init_self ys
      rw [heq] at h2
      exact h2 (hys _)
    · intro h xs hxs
      rw [BoundedFormula.realize_all]
      intro a
      rw [BoundedFormula.realize_imp, realize_predVarF, Fin.snoc_last]
      intro ha
      refine h _ (fun i => ?_)
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rwa [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]; exact hxs i

/-- The Tarski–Vaught sentence for the `L`-formula `φ`: if a tuple from the predicate has a
witness in the whole structure, then it has one inside the predicate. -/
def tvSentence (L : FirstOrder.Language.{0, 0}) {l : ℕ} (φ : L.BoundedFormula Empty (l + 1)) :
    (L.sum predLang).Sentence :=
  allsPred L l
    (((pairInl L).onBoundedFormula φ).ex ⟹
      ((predVarF L (Fin.last l) ⊓ (pairInl L).onBoundedFormula φ).ex))

theorem realize_tvSentence {M : Type} [L.Structure M] [(L.sum predLang).Structure M]
    [(pairInl L).IsExpansionOn M] {l : ℕ} (φ : L.BoundedFormula Empty (l + 1)) :
    M ⊨ tvSentence L φ ↔
      ∀ xs : Fin l → M, (∀ i, xs i ∈ predSet L M) →
        (∃ a : M, φ.Realize default (Fin.snoc xs a)) →
        ∃ b : M, b ∈ predSet L M ∧ φ.Realize default (Fin.snoc xs b) := by
  rw [tvSentence, realize_allsPred]
  refine forall_congr' fun xs => imp_congr_right fun _ => ?_
  simp [Fin.snoc_last]

/-- The sentence asserting that the new predicate is nonempty. -/
def predNonemptySentence (L : FirstOrder.Language.{0, 0}) : (L.sum predLang).Sentence :=
  (predVarF L (0 : Fin 1)).ex

theorem realize_predNonemptySentence {M : Type} [(L.sum predLang).Structure M] :
    M ⊨ predNonemptySentence L ↔ (predSet L M).Nonempty := by
  simp only [predNonemptySentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex, realize_predVarF, Set.Nonempty]
  refine exists_congr fun a => ?_
  rw [Subsingleton.elim (0 : Fin 1) (Fin.last 0), Fin.snoc_last]

/-- The theory saying that the new unary predicate names a nonempty elementary substructure. -/
def pairTheory (L : FirstOrder.Language.{0, 0}) : (L.sum predLang).Theory :=
  insert (predNonemptySentence L)
    (Set.range fun p : Σ l : ℕ, L.BoundedFormula Empty (l + 1) => tvSentence L p.2)

theorem models_pairTheory_iff {M : Type} [L.Structure M] [(L.sum predLang).Structure M]
    [(pairInl L).IsExpansionOn M] :
    M ⊨ pairTheory L ↔
      (predSet L M).Nonempty ∧
        ∀ (l : ℕ) (φ : L.BoundedFormula Empty (l + 1)) (xs : Fin l → M),
          (∀ i, xs i ∈ predSet L M) → (∃ a : M, φ.Realize default (Fin.snoc xs a)) →
          ∃ b : M, b ∈ predSet L M ∧ φ.Realize default (Fin.snoc xs b) := by
  rw [Theory.model_iff]
  constructor
  · intro h
    refine ⟨realize_predNonemptySentence.1 (h _ (Set.mem_insert _ _)), fun l φ => ?_⟩
    exact (realize_tvSentence φ).1 (h (tvSentence L φ) (Set.mem_insert_of_mem _ ⟨⟨l, φ⟩, rfl⟩))
  · rintro ⟨h1, h2⟩ σ (rfl | ⟨⟨l, φ⟩, rfl⟩)
    · exact realize_predNonemptySentence.2 h1
    · exact (realize_tvSentence φ).2 (h2 l φ)

/-! ### A model of `pairTheory` has the predicate as an elementary substructure -/

/-- The formula `f (x₀, …, x_{m-1}) = x_m`. -/
def funEqFormula {m : ℕ} (f : L.Functions m) : L.BoundedFormula Empty (m + 1) :=
  Term.bdEqual (Term.func f fun i => Term.var (Sum.inr i.castSucc))
    (Term.var (Sum.inr (Fin.last m)))

theorem realize_funEqFormula {M : Type} [L.Structure M] {m : ℕ} (f : L.Functions m)
    (xs : Fin m → M) (a : M) :
    (funEqFormula f).Realize (default : Empty → M) (Fin.snoc xs a) ↔
      Structure.funMap f xs = a := by
  simp [funEqFormula]

variable {M : Type} [L.Structure M] [(L.sum predLang).Structure M] [(pairInl L).IsExpansionOn M]

theorem predSet_closedUnder (h : M ⊨ pairTheory L) {m : ℕ} (f : L.Functions m) :
    ClosedUnder f (predSet L M) := by
  intro xs hxs
  obtain ⟨-, htv⟩ := models_pairTheory_iff.1 h
  obtain ⟨b, hb, hb2⟩ := htv m (funEqFormula f) xs hxs
    ⟨Structure.funMap f xs, (realize_funEqFormula f xs _).2 rfl⟩
  rw [realize_funEqFormula] at hb2
  exact hb2 ▸ hb

/-- The substructure named by the extra predicate. -/
def predSubstructure (h : M ⊨ pairTheory L) : L.Substructure M where
  carrier := predSet L M
  fun_mem f := predSet_closedUnder h f

@[simp]
theorem coe_predSubstructure (h : M ⊨ pairTheory L) :
    ((predSubstructure h : L.Substructure M) : Set M) = predSet L M := rfl

/-- **The predicate names an elementary substructure.** -/
def predElementarySubstructure (h : M ⊨ pairTheory L) : L.ElementarySubstructure M :=
  (predSubstructure h).toElementarySubstructure (by
    intro n φ x a ha
    obtain ⟨-, htv⟩ := models_pairTheory_iff.1 h
    obtain ⟨b, hb, hb2⟩ := htv n φ (fun i => (x i : M)) (fun i => (x i).2) ⟨a, ha⟩
    exact ⟨⟨b, hb⟩, hb2⟩)

@[simp]
theorem coe_predElementarySubstructure (h : M ⊨ pairTheory L) :
    ((predElementarySubstructure h : L.ElementarySubstructure M) : Set M) = predSet L M := rfl

/-- **Forth-step consistency.**  In a model of the pair theory, suppose the tuple `b` lies in the
predicate and satisfies every `L`-formula satisfied by `a`.  Then any formula witnessed over `a`
in the whole structure is witnessed over `b` *inside the predicate*.

This is the consistency input to the back-and-forth construction of a countable Vaughtian pair
whose two sides are isomorphic: it says that the type of `m` over `a`, transported to `b`, is
finitely satisfiable inside the predicate. -/
theorem exists_mem_predSet_realize (h : M ⊨ pairTheory L) {l : ℕ} (a b : Fin l → M)
    (hb : ∀ i, b i ∈ predSet L M)
    (hab : ∀ ψ : L.BoundedFormula Empty l, ψ.Realize default a → ψ.Realize default b)
    (φ : L.BoundedFormula Empty (l + 1)) (m : M) (hm : φ.Realize default (Fin.snoc a m)) :
    ∃ d : M, d ∈ predSet L M ∧ φ.Realize default (Fin.snoc b d) := by
  obtain ⟨-, htv⟩ := models_pairTheory_iff.1 h
  refine htv l φ b hb ?_
  exact BoundedFormula.realize_ex.1 (hab φ.ex (BoundedFormula.realize_ex.2 ⟨m, hm⟩))

/-! ### An honest elementary pair models `pairTheory` -/

theorem models_pairTheory_of_elementarySubstructure {M : Type} [L.Structure M]
    (N : L.ElementarySubstructure M) (hne : (N : Set M).Nonempty) :
    letI := pairStructure (L := L) (N : Set M)
    M ⊨ pairTheory L := by
  letI : (L.sum predLang).Structure M := pairStructure (L := L) (N : Set M)
  haveI : (pairInl L).IsExpansionOn M := pairStructure_isExpansionOn (N : Set M)
  rw [models_pairTheory_iff]
  rw [show predSet L M = (N : Set M) from rfl]
  refine ⟨hne, fun l φ xs hxs ha => ?_⟩
  obtain ⟨a, ha⟩ := ha
  set x' : Fin l → N := fun i => ⟨xs i, hxs i⟩ with hx'
  have hxsval : ((↑) : N → M) ∘ x' = xs := rfl
  have hdef : ((↑) : N → M) ∘ (default : Empty → N) = (default : Empty → M) :=
    Subsingleton.elim _ _
  have hex : (φ.ex).Realize (default : Empty → N) x' := by
    rw [← N.subtype.map_boundedFormula (φ.ex) (default : Empty → N) x']
    rw [show (N.subtype : N → M) ∘ (default : Empty → N) = (default : Empty → M) from hdef,
      show (N.subtype : N → M) ∘ x' = xs from hxsval]
    exact BoundedFormula.realize_ex.2 ⟨a, ha⟩
  obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.1 hex
  refine ⟨(b : M), b.2, ?_⟩
  rw [← N.subtype.map_boundedFormula φ (default : Empty → N) (Fin.snoc x' b)] at hb
  rw [show (N.subtype : N → M) ∘ (default : Empty → N) = (default : Empty → M) from hdef,
    show (N.subtype : N → M) ∘ Fin.snoc x' b = Fin.snoc xs (b : M) from by
      rw [Fin.comp_snoc]; rfl] at hb
  exact hb

/-! ## Countable Vaughtian pairs -/

/-- A **countable Vaughtian pair** for the `L`-theory `T`: a countable model of `T` in the pair
language, in which the extra predicate names a proper elementary substructure containing an
infinite parameter-definable set whose parameters also lie in the predicate. -/
structure CountableVPair (L : FirstOrder.Language.{0, 0}) (T : L.Theory) where
  /-- The underlying type of the pair. -/
  carrier : Type
  [strL : L.Structure carrier]
  [strPair : (L.sum predLang).Structure carrier]
  [expansion : (pairInl L).IsExpansionOn carrier]
  [countable : Countable carrier]
  [nonempty : Nonempty carrier]
  /-- The pair is a model of `T`. -/
  models_T : carrier ⊨ T
  /-- The predicate names a nonempty elementary substructure. -/
  models_pair : carrier ⊨ pairTheory L
  /-- The predicate is a proper subset. -/
  proper : predSet L carrier ≠ Set.univ
  /-- The index type of the parameters of the distinguished definable set. -/
  paramType : Type
  [finiteParam : Finite paramType]
  /-- The formula defining the distinguished set. -/
  defFormula : L.BoundedFormula paramType 1
  /-- The parameters of the distinguished definable set. -/
  params : paramType → carrier
  /-- The parameters lie in the predicate. -/
  params_mem : ∀ i, params i ∈ predSet L carrier
  /-- The distinguished definable set is contained in the predicate. -/
  defSet_subset : ∀ a : carrier, defFormula.Realize params (fun _ => a) → a ∈ predSet L carrier
  /-- The distinguished definable set is infinite. -/
  defSet_infinite : {a : carrier | defFormula.Realize params fun _ => a}.Infinite

attribute [instance] CountableVPair.strL CountableVPair.strPair CountableVPair.expansion
  CountableVPair.countable CountableVPair.nonempty CountableVPair.finiteParam

/-- A unary set definable with parameters from `A` is defined by a bounded formula in one
variable, with a finite tuple of parameters taken from `A`. -/
theorem exists_boundedFormula_of_definable₁ {M : Type} [L.Structure M] {A X : Set M}
    (h : A.Definable₁ L X) :
    ∃ (β : Type) (_ : Finite β) (χ : L.BoundedFormula β 1) (b : β → M),
      (∀ i, b i ∈ A) ∧ ∀ a : M, a ∈ X ↔ χ.Realize b fun _ => a := by
  classical
  obtain ⟨A₀, hA₀, hdef₀⟩ := Set.definable_iff_finitely_definable.1 h
  obtain ⟨ψ, hψ⟩ := Set.definable_iff_exists_formula_sum.1 hdef₀
  refine ⟨↥(A₀ : Set M), inferInstance,
    (BoundedFormula.relabel id ψ : L.BoundedFormula ↥(A₀ : Set M) 1),
    fun i => (i : M), fun i => hA₀ i.2, fun a => ?_⟩
  have hmem : a ∈ X ↔ (fun _ : Fin 1 => a) ∈ {x : Fin 1 → M | x 0 ∈ X} := Iff.rfl
  rw [hmem, hψ]
  rw [BoundedFormula.realize_relabel]
  simp only [Set.mem_setOf_eq, Function.comp_id]
  rw [Subsingleton.elim ((fun _ : Fin 1 => a) ∘ (Fin.natAdd 1 : Fin 0 → Fin (1 + 0)))
    (default : Fin 0 → M)]
  rfl

/-- The converse of `exists_boundedFormula_of_definable₁`: the set defined by a bounded formula
in one variable with finitely many parameters is definable over the range of the parameters. -/
theorem definable₁_of_boundedFormula {M : Type} [L.Structure M] {β : Type} [Finite β]
    (χ : L.BoundedFormula β 1) (b : β → M) :
    (Set.range b).Definable₁ L {a : M | χ.Realize b fun _ => a} := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin β
  set ψ : L.Formula (Fin m ⊕ Fin 1) :=
    Formula.relabel (Sum.map (e : β → Fin m) id) χ.toFormula with hψ
  have hb' : Set.range (b ∘ e.symm) = Set.range b := by
    rw [Set.range_comp]
    simp [Set.range_eq_univ.2 e.symm.surjective]
  have hset : {a : M | ψ.Realize (Sum.elim (b ∘ e.symm) fun _ => a)}
      = {a : M | χ.Realize b fun _ => a} := by
    ext a
    simp only [Set.mem_setOf_eq, hψ, Formula.realize_relabel,
      BoundedFormula.realize_toFormula]
    constructor
    · intro h
      have h1 : (Sum.elim (b ∘ e.symm) (fun _ : Fin 1 => a) ∘ Sum.map (e : β → Fin m) id) ∘ Sum.inl = b := by
        funext i; simp
      have h2 : (Sum.elim (b ∘ e.symm) (fun _ : Fin 1 => a) ∘ Sum.map (e : β → Fin m) id) ∘ Sum.inr
          = fun _ : Fin 1 => a := by
        funext i; simp
      rwa [h1, h2] at h
    · intro h
      have h1 : (Sum.elim (b ∘ e.symm) (fun _ : Fin 1 => a) ∘ Sum.map (e : β → Fin m) id) ∘ Sum.inl = b := by
        funext i; simp
      have h2 : (Sum.elim (b ∘ e.symm) (fun _ : Fin 1 => a) ∘ Sum.map (e : β → Fin m) id) ∘ Sum.inr
          = fun _ : Fin 1 => a := by
        funext i; simp
      rwa [h1, h2]
  have := definable₁_of_formula ψ (b ∘ e.symm)
  rwa [hb', hset] at this

/-- Packaging a model with a countable parameter-definable set as a two-cardinal model. -/
theorem hasTwoCardinalModel_of_boundedFormula {T : L.Theory} (M : Type) [L.Structure M]
    [Nonempty M] [M ⊨ T] {β : Type} [Finite β] (χ : L.BoundedFormula β 1) (b : β → M)
    {κ lam : Cardinal.{0}} (hM : #M = κ) (hX : #{a : M | χ.Realize b fun _ => a} = lam) :
    HasTwoCardinalModel T κ lam :=
  ⟨Theory.ModelType.of T M, Set.range b, {a : M | χ.Realize b fun _ => a},
    definable₁_of_boundedFormula χ b, hM, hX⟩

/-! ### Transfer along elementary embeddings of pairs -/

section Transfer

variable {A B : Type} [L.Structure A] [(L.sum predLang).Structure A] [(pairInl L).IsExpansionOn A]
  [L.Structure B] [(L.sum predLang).Structure B] [(pairInl L).IsExpansionOn B]

/-- An elementary embedding in the pair language is elementary for `L`-formulas. -/
theorem realize_comp_pairEmbedding (f : A ↪ₑ[L.sum predLang] B) {β : Type} {n : ℕ}
    (χ : L.BoundedFormula β n) (v : β → A) (xs : Fin n → A) :
    χ.Realize ((f : A → B) ∘ v) ((f : A → B) ∘ xs) ↔ χ.Realize v xs := by
  rw [← LHom.realize_onBoundedFormula (M := B) (pairInl L) χ (v := (f : A → B) ∘ v)
      (xs := (f : A → B) ∘ xs),
    ← LHom.realize_onBoundedFormula (M := A) (pairInl L) χ (v := v) (xs := xs)]
  exact f.map_boundedFormula _ v xs

omit [L.Structure A] [(pairInl L).IsExpansionOn A] [L.Structure B]
  [(pairInl L).IsExpansionOn B] in
/-- An elementary embedding in the pair language reflects and preserves the predicate. -/
theorem mem_predSet_pairEmbedding (f : A ↪ₑ[L.sum predLang] B) (a : A) :
    f a ∈ predSet L B ↔ a ∈ predSet L A := by
  have h := f.map_boundedFormula (predVarF L (0 : Fin 1)) (default : Empty → A) (fun _ => a)
  rw [realize_predVarF, realize_predVarF] at h
  simpa using h

end Transfer

/-! ### Löwenheim–Skolem produces a countable Vaughtian pair -/

/-- **A Vaughtian pair yields a countable Vaughtian pair.** -/
theorem nonempty_countableVPair {T : L.Theory} (hL : L.card ≤ ℵ₀) (h : HasVaughtianPair T) :
    Nonempty (CountableVPair L T) := by
  classical
  obtain ⟨M, N, X, hne, hdef, hXinf, hXsub⟩ := h
  obtain ⟨β, hβ, χ, b, hbN, hX⟩ := exists_boundedFormula_of_definable₁ hdef
  haveI : Finite β := hβ
  haveI hMinf : Infinite (M : Type) := Set.infinite_univ_iff.1 (hXinf.mono (Set.subset_univ X))
  -- the pair structure on `M`
  letI : (L.sum predLang).Structure (M : Type) := pairStructure (L := L) (N : Set M)
  haveI : (pairInl L).IsExpansionOn (M : Type) := pairStructure_isExpansionOn (N : Set M)
  have hpredM : predSet L (M : Type) = (N : Set M) := rfl
  have hNne : (N : Set M).Nonempty := by
    obtain ⟨x, hx⟩ := hXinf.nonempty
    exact ⟨x, hXsub hx⟩
  have hMpair : (M : Type) ⊨ pairTheory L := models_pairTheory_of_elementarySubstructure N hNne
  -- a point outside the predicate, and a countably infinite part of `X`
  obtain ⟨c, hc⟩ := Set.ne_univ_iff_exists_notMem _ |>.1 hne
  obtain ⟨x₀, hx₀X, hx₀inj⟩ : ∃ x₀ : ℕ → M, (∀ n, x₀ n ∈ X) ∧ Function.Injective x₀ := by
    refine ⟨fun n => ((Set.Infinite.natEmbedding X hXinf n : M)),
      fun n => (Set.Infinite.natEmbedding X hXinf n).2, ?_⟩
    exact fun m n hmn => (Set.Infinite.natEmbedding X hXinf).injective (Subtype.ext hmn)
  set s : Set M := Set.range b ∪ Set.range x₀ ∪ {c} with hs
  have hscount : s.Countable :=
    ((Set.countable_range b).union (Set.countable_range x₀)).union (Set.countable_singleton c)
  -- Löwenheim–Skolem in the pair language
  obtain ⟨S, hsS, hScard⟩ :=
    exists_elementarySubstructure_card_eq (L.sum predLang) s (ℵ₀ : Cardinal.{0}) le_rfl
      (by simpa using Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hscount))
      (by simpa using pairLang_card_le hL)
      (by simp [Cardinal.aleph0_le_mk (M : Type)])
  have hScard' : #(S : Type) = ℵ₀ := by simpa using hScard
  haveI : Countable (S : Type) := Cardinal.mk_le_aleph0_iff.1 hScard'.le
  letI : L.Structure (S : Type) := (pairInl L).reduct (S : Type)
  haveI : (pairInl L).IsExpansionOn (S : Type) := LHom.isExpansionOn_reduct _ _
  have hbS : ∀ i, b i ∈ S := fun i => hsS (Or.inl (Or.inl ⟨i, rfl⟩))
  have hx₀S : ∀ n, x₀ n ∈ S := fun n => hsS (Or.inl (Or.inr ⟨n, rfl⟩))
  have hcS : c ∈ S := hsS (Or.inr rfl)
  haveI : Nonempty (S : Type) := ⟨⟨c, hcS⟩⟩
  have hpredS : ∀ y : (S : Type), y ∈ predSet L (S : Type) ↔ (y : M) ∈ (N : Set M) := by
    intro y
    rw [← hpredM, ← mem_predSet_pairEmbedding S.subtype y]
    rfl
  have hMT' : (M : Type) ⊨ (pairInl L).onTheory T :=
    (LHom.onTheory_model (pairInl L) T).2 inferInstance
  have hST : (S : Type) ⊨ T :=
    (LHom.onTheory_model (pairInl L) T).1
      ((S.subtype.theory_model_iff ((pairInl L).onTheory T)).2 hMT')
  refine ⟨{
    carrier := (S : Type)
    models_T := hST
    models_pair := (S.subtype.theory_model_iff (pairTheory L)).2 hMpair
    proper := ?_
    paramType := β
    defFormula := χ
    params := fun i => ⟨b i, hbS i⟩
    params_mem := ?_
    defSet_subset := ?_
    defSet_infinite := ?_ }⟩
  · intro hcon
    have : (⟨c, hcS⟩ : (S : Type)) ∈ predSet L (S : Type) := hcon ▸ Set.mem_univ _
    exact hc ((hpredS _).1 this)
  · intro i
    exact (hpredS _).2 (hbN i)
  · intro a ha
    refine (hpredS a).2 (hXsub ?_)
    rw [hX]
    have := (realize_comp_pairEmbedding S.subtype χ (fun i => (⟨b i, hbS i⟩ : (S : Type)))
      (fun _ => a)).2 ha
    exact this
  · have hinj : Function.Injective (fun n : ℕ => (⟨x₀ n, hx₀S n⟩ : (S : Type))) := by
      intro m n hmn
      exact hx₀inj (congrArg (fun y : (S : Type) => (y : M)) hmn)
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (⟨x₀ n, hx₀S n⟩ : (S : Type)))
      hinj ?_
    intro n
    refine (realize_comp_pairEmbedding S.subtype χ (fun i => (⟨b i, hbS i⟩ : (S : Type)))
      (fun _ => (⟨x₀ n, hx₀S n⟩ : (S : Type)))).1 ?_
    exact (hX (x₀ n)).1 (hx₀X n)

end Submission.Morley
