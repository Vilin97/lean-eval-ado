import Mathlib
import Submission.Morley.TwoCardinal
import Submission.Morley.Realize
import Submission.Morley.Morleyization
import Submission.Morley.Port.ElementaryChain

/-!
# Vaught's two-cardinal theorem
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Naming parameters inside the pair language -/

/-- The reindexing sending the last bound variable to the free variable of a `1`-type and the
remaining ones to the parameters `b`. -/
def tpReindex {A : Type} {k : ℕ} (b : Fin k → A) : Empty ⊕ Fin (k + 1) → A ⊕ Fin 1 :=
  Sum.elim (fun e : Empty => e.elim) (Fin.lastCases (Sum.inr 0) fun j => Sum.inl (b j))

/-- The pair-language formula `ψ(b₀, …, b_{k-1}, x)` in the free variable `x`, with the tuple `b`
named by its own parameter symbols. -/
def tpFormula {A : Type} {k : ℕ} (b : Fin k → A) (ψ : L.BoundedFormula Empty (k + 1)) :
    (L.sum predLang).Formula (A ⊕ Fin 1) :=
  Formula.relabel (tpReindex b) ((pairInl L).onBoundedFormula ψ).toFormula

theorem realize_tpFormula {A M : Type} [L.Structure M] [(L.sum predLang).Structure M]
    [(pairInl L).IsExpansionOn M] {k : ℕ} (b : Fin k → A)
    (ψ : L.BoundedFormula Empty (k + 1)) (g : A → M) (d : M) :
    (tpFormula b ψ).Realize (Sum.elim g fun _ => d) ↔
      ψ.Realize default (Fin.snoc (fun j => g (b j)) d) := by
  have h1 : ((Sum.elim g fun _ => d) ∘ tpReindex b) ∘ Sum.inl = (default : Empty → M) :=
    Subsingleton.elim _ _
  have h2 : ((Sum.elim g fun _ => d) ∘ tpReindex b) ∘ Sum.inr
      = Fin.snoc (fun j => g (b j)) d := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [tpReindex]
  rw [tpFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula, h1, h2,
    LHom.realize_onBoundedFormula]

/-- The pair-language formula saying that the free variable satisfies the extra predicate. -/
def predFormula (L : FirstOrder.Language.{0, 0}) (A : Type) :
    (L.sum predLang).Formula (A ⊕ Fin 1) :=
  Relations.formula (Sum.inr predSym) fun _ => Term.var (Sum.inr 0)

theorem realize_predFormula {A M : Type} [(L.sum predLang).Structure M] (g : A → M) (d : M) :
    (predFormula L A).Realize (Sum.elim g fun _ => d) ↔ d ∈ predSet L M := by
  rw [predFormula, Formula.realize_rel]
  rfl

/-! ## Stages of the `ω`-chain -/

/-- One stage of the `ω`-chain: a countable nonempty pair-language structure in which the extra
predicate names an elementary substructure. -/
structure VStage (L : FirstOrder.Language.{0, 0}) where
  /-- The underlying type. -/
  carrier : Type
  [strL : L.Structure carrier]
  [strPair : (L.sum predLang).Structure carrier]
  [expansion : (pairInl L).IsExpansionOn carrier]
  [cnt : Countable carrier]
  [ne : Nonempty carrier]
  /-- The predicate names a nonempty elementary substructure. -/
  models_pair : carrier ⊨ pairTheory L

attribute [instance] VStage.strL VStage.strPair VStage.expansion VStage.cnt VStage.ne

/-- The index of the family of `1`-types realized at each step of the `ω`-chain: a length, two
tuples of that length, and one further element. -/
abbrev stepIndex (A : Type) : Type := Σ k : ℕ, (Fin k → A) × (Fin k → A) × A

instance (A : Type) [Countable A] : Countable (stepIndex A) := inferInstance

variable (L) in
/-- The `1`-type attached to an index `⟨k, a, b, m⟩`: the type of `m` over `a`, transported to
`b`, together with the requirement of lying in the predicate when `b` does. -/
def stepTypes (A : Type) [L.Structure A] [(L.sum predLang).Structure A] :
    stepIndex A → Set ((L.sum predLang).Formula (A ⊕ Fin 1)) := fun i =>
  {χ | SameType L i.2.1 i.2.2.1 ∧
    ((∃ ψ : L.BoundedFormula Empty (i.1 + 1),
        ψ.Realize default (Fin.snoc i.2.1 i.2.2.2) ∧ χ = tpFormula i.2.2.1 ψ) ∨
      ((∀ j, i.2.2.1 j ∈ predSet L A) ∧ χ = predFormula L A))}

theorem finitelySatisfiable_stepTypes (S : VStage L) (i : stepIndex S.carrier)
    (t : Finset ((L.sum predLang).Formula (S.carrier ⊕ Fin 1)))
    (ht : ↑t ⊆ stepTypes L S.carrier i) :
    ∃ a : S.carrier, ∀ χ ∈ t, χ.Realize (Sum.elim id fun _ => a) := by
  classical
  obtain ⟨k, a, b, m⟩ := i
  by_cases hst : SameType L a b
  · -- choose, for each formula of `t`, a bounded formula it comes from
    have hchoice : ∀ χ : {x // x ∈ t}, ∃ ψ : L.BoundedFormula Empty (k + 1),
        ψ.Realize default (Fin.snoc a m) ∧
          ((χ : (L.sum predLang).Formula (S.carrier ⊕ Fin 1)) = tpFormula b ψ ∨
            ((∀ j, b j ∈ predSet L S.carrier) ∧ (χ : _) = predFormula L S.carrier)) := by
      rintro ⟨χ, hχ⟩
      obtain ⟨-, hor⟩ := ht hχ
      rcases hor with ⟨ψ, hψ, rfl⟩ | ⟨hb, rfl⟩
      · exact ⟨ψ, hψ, Or.inl rfl⟩
      · exact ⟨⊤, by simp, Or.inr ⟨hb, rfl⟩⟩
    choose ψ hψreal hψeq using hchoice
    set Ψ : L.BoundedFormula Empty (k + 1) := BoundedFormula.iInf ψ with hΨdef
    have hΨ : Ψ.Realize default (Fin.snoc a m) := by
      rw [hΨdef, BoundedFormula.realize_iInf]
      exact hψreal
    have hab : ∀ φ : L.BoundedFormula Empty k,
        φ.Realize default a → φ.Realize default b :=
      fun φ hφ => ((sameType_iff_boundedFormula a b).1 hst φ).1 hφ
    have key : ∃ d : S.carrier, Ψ.Realize default (Fin.snoc b d) ∧
        ((∀ j, b j ∈ predSet L S.carrier) → d ∈ predSet L S.carrier) := by
      by_cases hb : ∀ j, b j ∈ predSet L S.carrier
      · obtain ⟨d, hd, hd2⟩ := exists_mem_predSet_realize S.models_pair a b hb hab Ψ m hΨ
        exact ⟨d, hd2, fun _ => hd⟩
      · have hex : (Ψ.ex).Realize (default : Empty → S.carrier) b :=
          hab Ψ.ex (BoundedFormula.realize_ex.2 ⟨m, hΨ⟩)
        obtain ⟨d, hd⟩ := BoundedFormula.realize_ex.1 hex
        exact ⟨d, hd, fun hcon => absurd hcon hb⟩
    obtain ⟨d, hd, hdP⟩ := key
    refine ⟨d, fun χ hχ => ?_⟩
    have hcomp : (ψ ⟨χ, hχ⟩).Realize (default : Empty → S.carrier) (Fin.snoc b d) := by
      rw [hΨdef, BoundedFormula.realize_iInf] at hd
      exact hd _
    rcases hψeq ⟨χ, hχ⟩ with heq | ⟨hb, heq⟩
    · have heq' : χ = tpFormula b (ψ ⟨χ, hχ⟩) := heq
      rw [heq', realize_tpFormula]
      exact hcomp
    · have heq' : χ = predFormula L S.carrier := heq
      rw [heq', realize_predFormula]
      exact hdP hb
  · have hempty : ∀ χ ∈ t, False := by
      intro χ hχ
      exact hst (ht hχ).1
    exact ⟨Classical.arbitrary S.carrier, fun χ hχ => absurd hχ (fun h => hempty χ h)⟩

/-- **One step of the `ω`-chain.**  Every stage has a countable elementary pair-extension in which,
for each pair of same-typed tuples `a`, `b` and each `m`, the type of `m` over `a` is realized over
`b` — inside the predicate whenever `b` lies inside the predicate. -/
theorem exists_next (hL : L.card ≤ ℵ₀) (S : VStage L) :
    ∃ (S' : VStage L) (f : S.carrier ↪ₑ[L.sum predLang] S'.carrier),
      ∀ (k : ℕ) (a b : Fin k → S.carrier) (m : S.carrier), SameType L a b →
        ∃ d : S'.carrier,
          SameType L (Fin.snoc (fun j => f (a j)) (f m)) (Fin.snoc (fun j => f (b j)) d) ∧
            ((∀ j, b j ∈ predSet L S.carrier) → d ∈ predSet L S'.carrier) := by
  classical
  obtain ⟨B, instB, hcB, f, hreal⟩ :=
    exists_countable_elementaryExtension_realizing (L := L.sum predLang) (A := S.carrier)
      (pairLang_card_le hL) (stepTypes L S.carrier) (finitelySatisfiable_stepTypes S)
  letI : (L.sum predLang).Structure B := instB
  letI : L.Structure B := (pairInl L).reduct B
  haveI : (pairInl L).IsExpansionOn B := LHom.isExpansionOn_reduct _ _
  haveI : Countable B := hcB
  haveI : Nonempty B := ⟨f (Classical.arbitrary S.carrier)⟩
  refine ⟨⟨B, (f.theory_model_iff (pairTheory L)).1 S.models_pair⟩, f, ?_⟩
  intro k a b m hst
  obtain ⟨d, hd⟩ := hreal ⟨k, a, b, m⟩
  have hsnoc : ∀ (x : Fin k → S.carrier) (y : S.carrier),
      (fun z => f z) ∘ Fin.snoc x y = Fin.snoc (fun j => f (x j)) (f y) := by
    intro x y
    rw [Fin.comp_snoc]
    rfl
  have htrans : ∀ φ : L.BoundedFormula Empty (k + 1),
      φ.Realize (default : Empty → B) (Fin.snoc (fun j => f (a j)) (f m)) ↔
        φ.Realize (default : Empty → S.carrier) (Fin.snoc a m) := by
    intro φ
    rw [← hsnoc a m, ← realize_comp_pairEmbedding f φ (default : Empty → S.carrier) (Fin.snoc a m)]
    exact iff_of_eq (congrArg (fun v => φ.Realize v _) (Subsingleton.elim _ _))
  refine ⟨d, ?_, ?_⟩
  · rw [sameType_iff_boundedFormula]
    intro φ
    rw [htrans φ]
    constructor
    · intro hφ
      have hmem : tpFormula b φ ∈ stepTypes L S.carrier ⟨k, a, b, m⟩ :=
        ⟨hst, Or.inl ⟨φ, hφ, rfl⟩⟩
      have := hd _ hmem
      rwa [realize_tpFormula] at this
    · intro hφ
      by_contra hcon
      have hnot : (∼φ).Realize (default : Empty → S.carrier) (Fin.snoc a m) := by
        rw [BoundedFormula.realize_not]; exact hcon
      have hmem : tpFormula b (∼φ) ∈ stepTypes L S.carrier ⟨k, a, b, m⟩ :=
        ⟨hst, Or.inl ⟨∼φ, hnot, rfl⟩⟩
      have := hd _ hmem
      rw [realize_tpFormula, BoundedFormula.realize_not] at this
      exact this hφ
  · intro hb
    have hmem : predFormula L S.carrier ∈ stepTypes L S.carrier ⟨k, a, b, m⟩ :=
      ⟨hst, Or.inr ⟨hb, rfl⟩⟩
    have := hd _ hmem
    rwa [realize_predFormula] at this

/-! ## Same types along elementary embeddings of pairs -/

section PairEmb

variable {X Y : Type} [L.Structure X] [(L.sum predLang).Structure X]
  [(pairInl L).IsExpansionOn X] [L.Structure Y] [(L.sum predLang).Structure Y]
  [(pairInl L).IsExpansionOn Y]

/-- An elementary embedding of pairs preserves and reflects `L`-types of tuples. -/
theorem sameType_comp_pairEmbedding (f : X ↪ₑ[L.sum predLang] Y) {k : ℕ} (u : Fin k → X) :
    SameType L u fun j => f (u j) := by
  intro φ
  have h := realize_comp_pairEmbedding f φ u (default : Fin 0 → X)
  rw [Subsingleton.elim ((f : X → Y) ∘ (default : Fin 0 → X)) (default : Fin 0 → Y)] at h
  exact h.symm

end PairEmb

/-! ## The `ω`-chain -/

/-- The stage produced by `exists_next`. -/
noncomputable def nextStage (hL : L.card ≤ ℵ₀) (S : VStage L) : VStage L :=
  (exists_next hL S).choose

/-- The elementary embedding of a stage into the next one. -/
noncomputable def nextEmb (hL : L.card ≤ ℵ₀) (S : VStage L) :
    S.carrier ↪ₑ[L.sum predLang] (nextStage hL S).carrier :=
  (exists_next hL S).choose_spec.choose

theorem nextEmb_spec (hL : L.card ≤ ℵ₀) (S : VStage L) {k : ℕ} (a b : Fin k → S.carrier)
    (m : S.carrier) (hst : SameType L a b) :
    ∃ d : (nextStage hL S).carrier,
      SameType L (Fin.snoc (fun j => nextEmb hL S (a j)) (nextEmb hL S m))
        (Fin.snoc (fun j => nextEmb hL S (b j)) d) ∧
        ((∀ j, b j ∈ predSet L S.carrier) → d ∈ predSet L (nextStage hL S).carrier) :=
  (exists_next hL S).choose_spec.choose_spec k a b m hst

/-- The `n`-th stage of the `ω`-chain starting at `S₀`. -/
noncomputable def chainStage (hL : L.card ≤ ℵ₀) (S₀ : VStage L) : ℕ → VStage L
  | 0 => S₀
  | n + 1 => nextStage hL (chainStage hL S₀ n)

/-- The `ω`-chain of stages. -/
noncomputable def omegaChain (hL : L.card ≤ ℵ₀) (S₀ : VStage L) :
    ElementaryChain (L.sum predLang) ℕ :=
  ElementaryChain.ofNatSucc (fun n => (chainStage hL S₀ n).carrier)
    fun n => nextEmb hL (chainStage hL S₀ n)

theorem omegaChain_carrier (hL : L.card ≤ ℵ₀) (S₀ : VStage L) (n : ℕ) :
    (omegaChain hL S₀).carrier n = (chainStage hL S₀ n).carrier := rfl

/-- A countable **homogeneous pair**: a countable model of the pair theory in which every type of
one element over a tuple is realized over every same-typed tuple, inside the predicate whenever
the target tuple is. -/
structure HomogPair (L : FirstOrder.Language.{0, 0}) where
  /-- The underlying type. -/
  carrier : Type
  [strL : L.Structure carrier]
  [strPair : (L.sum predLang).Structure carrier]
  [expansion : (pairInl L).IsExpansionOn carrier]
  [cnt : Countable carrier]
  [ne : Nonempty carrier]
  /-- The predicate names a nonempty elementary substructure. -/
  models_pair : carrier ⊨ pairTheory L
  /-- Homogeneity. -/
  homog : ∀ (k : ℕ) (a b : Fin k → carrier) (m : carrier), SameType L a b →
    ∃ d : carrier, SameType L (Fin.snoc a m) (Fin.snoc b d) ∧
      ((∀ j, b j ∈ predSet L carrier) → d ∈ predSet L carrier)

attribute [instance] HomogPair.strL HomogPair.strPair HomogPair.expansion HomogPair.cnt
  HomogPair.ne

noncomputable instance instStrLOmega (hL : L.card ≤ ℵ₀) (S₀ : VStage L) (n : ℕ) :
    L.Structure ((omegaChain hL S₀).carrier n) := (chainStage hL S₀ n).strL

noncomputable instance instExpOmega (hL : L.card ≤ ℵ₀) (S₀ : VStage L) (n : ℕ) :
    (pairInl L).IsExpansionOn ((omegaChain hL S₀).carrier n) := (chainStage hL S₀ n).expansion

noncomputable instance instCntOmega (hL : L.card ≤ ℵ₀) (S₀ : VStage L) (n : ℕ) :
    Countable ((omegaChain hL S₀).carrier n) := (chainStage hL S₀ n).cnt

noncomputable instance instNeOmega (hL : L.card ≤ ℵ₀) (S₀ : VStage L) (n : ℕ) :
    Nonempty ((omegaChain hL S₀).carrier n) := (chainStage hL S₀ n).ne

/-- **The `ω`-chain construction.**  Every stage embeds elementarily into a countable homogeneous
pair. -/
theorem exists_homogPair (hL : L.card ≤ ℵ₀) (S₀ : VStage L) :
    ∃ H : HomogPair L, Nonempty (S₀.carrier ↪ₑ[L.sum predLang] H.carrier) := by
  classical
  letI : L.Structure (omegaChain hL S₀).Limit := (pairInl L).reduct (omegaChain hL S₀).Limit
  haveI : (pairInl L).IsExpansionOn (omegaChain hL S₀).Limit := LHom.isExpansionOn_reduct _ _
  have hcard : #((omegaChain hL S₀).Limit) ≤ ℵ₀ :=
    (omegaChain hL S₀).mk_limit_le_of_lift_mk_le le_rfl (by simp) fun i => by
      simp
  haveI : Countable (omegaChain hL S₀).Limit := Cardinal.mk_le_aleph0_iff.1 hcard
  haveI : Nonempty (omegaChain hL S₀).Limit := ⟨(omegaChain hL S₀).toLimit 0 (Classical.arbitrary _)⟩
  have hApair : (omegaChain hL S₀).Limit ⊨ pairTheory L :=
    (((omegaChain hL S₀).toLimitElementary 0).theory_model_iff (pairTheory L)).1 S₀.models_pair
  -- the successor embeddings, and how they interact with the canonical maps
  have hstep : ∀ (n : ℕ) (x : (omegaChain hL S₀).carrier n),
      (omegaChain hL S₀).toLimit (n + 1) (nextEmb hL (chainStage hL S₀ n) x) = (omegaChain hL S₀).toLimit n x := by
    intro n x
    have h1 : (omegaChain hL S₀).map n (n + 1) (Nat.le_succ n) = nextEmb hL (chainStage hL S₀ n) :=
      ElementaryChain.ofNatSucc_map_succ _ _ n
    have h2 := (omegaChain hL S₀).toLimit_map (Nat.le_succ n) x
    rw [h1] at h2
    exact h2
  have hsnocmap : ∀ (n : ℕ) (k : ℕ) (u : Fin k → (omegaChain hL S₀).carrier n) (v : (omegaChain hL S₀).carrier n),
      (fun t => (omegaChain hL S₀).toLimit n
          ((Fin.snoc u v : Fin (k + 1) → (omegaChain hL S₀).carrier n) t)) =
        Fin.snoc (fun j => (omegaChain hL S₀).toLimit n (u j)) ((omegaChain hL S₀).toLimit n v) := by
    intro n k u v
    funext t
    refine Fin.lastCases ?_ (fun j => ?_) t <;> simp
  refine ⟨⟨(omegaChain hL S₀).Limit, hApair, ?_⟩, ⟨(omegaChain hL S₀).toLimitElementary 0⟩⟩
  intro k a b m hst
  obtain ⟨i, z, hz⟩ := (omegaChain hL S₀).exists_finite_common_stage
    (α := Fin k ⊕ Fin k ⊕ Unit) (Sum.elim a (Sum.elim b fun _ => m))
  obtain ⟨a1, b1, m1, ha, hb, hm⟩ :
      ∃ (a1 b1 : Fin k → (omegaChain hL S₀).carrier i) (m1 : (omegaChain hL S₀).carrier i),
        (∀ j, (omegaChain hL S₀).toLimit i (a1 j) = a j) ∧
          (∀ j, (omegaChain hL S₀).toLimit i (b1 j) = b j) ∧
            (omegaChain hL S₀).toLimit i m1 = m :=
    ⟨fun j => z (Sum.inl j), fun j => z (Sum.inr (Sum.inl j)), z (Sum.inr (Sum.inr ())),
      fun j => congrFun hz (Sum.inl j), fun j => congrFun hz (Sum.inr (Sum.inl j)),
      congrFun hz (Sum.inr (Sum.inr ()))⟩
  have hlift : ∀ (n : ℕ) (l : ℕ) (u : Fin l → (omegaChain hL S₀).carrier n),
      SameType L u fun j => (omegaChain hL S₀).toLimit n (u j) :=
    fun n _ u => sameType_comp_pairEmbedding ((omegaChain hL S₀).toLimitElementary n) u
  have ha1a : SameType L a1 a := by
    have h := hlift i k a1
    rwa [show (fun j => (omegaChain hL S₀).toLimit i (a1 j)) = a from funext ha] at h
  have hb1b : SameType L b1 b := by
    have h := hlift i k b1
    rwa [show (fun j => (omegaChain hL S₀).toLimit i (b1 j)) = b from funext hb] at h
  have hstage : SameType L a1 b1 := (ha1a.trans hst).trans hb1b.symm
  obtain ⟨d, hd, hdP⟩ := nextEmb_spec hL (chainStage hL S₀ i) a1 b1 m1 hstage
  refine ⟨(omegaChain hL S₀).toLimit (i + 1) d, ?_, ?_⟩
  · have h1 : SameType L
        (Fin.snoc (fun j => nextEmb hL (chainStage hL S₀ i) (a1 j))
          (nextEmb hL (chainStage hL S₀ i) m1)) (Fin.snoc a m) := by
      have h := hlift (i + 1) (k + 1)
        (Fin.snoc (fun j => nextEmb hL (chainStage hL S₀ i) (a1 j))
          (nextEmb hL (chainStage hL S₀ i) m1) :
            Fin (k + 1) → (omegaChain hL S₀).carrier (i + 1))
      rw [hsnocmap] at h
      simp only [hstep] at h
      rwa [show (fun j => (omegaChain hL S₀).toLimit i (a1 j)) = a from funext ha, hm] at h
    have h2 : SameType L (Fin.snoc (fun j => nextEmb hL (chainStage hL S₀ i) (b1 j)) d)
        (Fin.snoc b ((omegaChain hL S₀).toLimit (i + 1) d)) := by
      have h := hlift (i + 1) (k + 1)
        (Fin.snoc (fun j => nextEmb hL (chainStage hL S₀ i) (b1 j)) d :
          Fin (k + 1) → (omegaChain hL S₀).carrier (i + 1))
      rw [hsnocmap] at h
      simp only [hstep] at h
      rwa [show (fun j => (omegaChain hL S₀).toLimit i (b1 j)) = b from funext hb] at h
    exact (h1.symm.trans hd).trans h2
  · intro hbP
    have hb1P : ∀ j, b1 j ∈ predSet L ((omegaChain hL S₀).carrier i) := by
      intro j
      refine (mem_predSet_pairEmbedding ((omegaChain hL S₀).toLimitElementary i) (b1 j)).1 ?_
      show (omegaChain hL S₀).toLimit i (b1 j) ∈ predSet L (omegaChain hL S₀).Limit
      rw [hb j]
      exact hbP j
    exact (mem_predSet_pairEmbedding ((omegaChain hL S₀).toLimitElementary (i + 1)) d).2
      (hdP hb1P)

/-! ## Back-and-forth: the predicate is isomorphic to the whole pair -/

/-- The elementary substructure named by the predicate. -/
def HomogPair.pred (H : HomogPair L) : L.ElementarySubstructure H.carrier :=
  predElementarySubstructure H.models_pair

@[simp]
theorem HomogPair.coe_pred (H : HomogPair L) :
    ((H.pred : L.ElementarySubstructure H.carrier) : Set H.carrier) = predSet L H.carrier := rfl

theorem HomogPair.mem_pred (H : HomogPair L) {x : H.carrier} :
    x ∈ H.pred ↔ x ∈ predSet L H.carrier := Iff.rfl

instance (H : HomogPair L) : Nonempty (H.pred : Type) := by
  obtain ⟨⟨x, hx⟩, -⟩ := models_pairTheory_iff.1 H.models_pair
  exact ⟨⟨x, hx⟩⟩

/-- A homogeneous pair is a type-extension pair with itself. -/
theorem HomogPair.isTypeExtensionPair_self (H : HomogPair L) :
    IsTypeExtensionPair L H.carrier H.carrier := by
  intro k a a' hst m
  obtain ⟨d, hd, -⟩ := H.homog k a a' m hst
  exact ⟨d, hd⟩

theorem HomogPair.isTypeExtensionPair_pred (H : HomogPair L) :
    IsTypeExtensionPair L H.carrier (H.pred : Type) := by
  intro k a a' hst m
  have h1 : SameType L a' fun j => ((a' j : H.carrier)) :=
    sameType_of_elementaryEmbedding H.pred.subtype a'
  obtain ⟨d, hd, hdP⟩ := H.homog k a (fun j => ((a' j : H.carrier))) m (hst.trans h1)
  have hdmem : d ∈ predSet L H.carrier := hdP fun j => (a' j).2
  refine ⟨⟨d, hdmem⟩, hd.trans ?_⟩
  have h2 := sameType_of_elementaryEmbedding H.pred.subtype
    (Fin.snoc a' (⟨d, hdmem⟩ : (H.pred : Type)))
  have heq : (fun t => H.pred.subtype
      ((Fin.snoc a' (⟨d, hdmem⟩ : (H.pred : Type)) : Fin (k + 1) → (H.pred : Type)) t)) =
      Fin.snoc (fun j => ((a' j : H.carrier))) d := by
    funext t
    refine Fin.lastCases ?_ (fun j => ?_) t <;> simp
  rw [heq] at h2
  exact h2.symm

theorem HomogPair.isTypeExtensionPair_pred' (H : HomogPair L) :
    IsTypeExtensionPair L (H.pred : Type) H.carrier := by
  intro k a a' hst m
  have h1 : SameType L a fun j => ((a j : H.carrier)) :=
    sameType_of_elementaryEmbedding H.pred.subtype a
  obtain ⟨d, hd, -⟩ :=
    H.homog k (fun j => ((a j : H.carrier))) a' ((m : H.carrier)) (h1.symm.trans hst)
  refine ⟨d, ?_⟩
  have h2 := sameType_of_elementaryEmbedding H.pred.subtype (Fin.snoc a m)
  have heq : (fun t => H.pred.subtype
      ((Fin.snoc a m : Fin (k + 1) → (H.pred : Type)) t)) =
      Fin.snoc (fun j => ((a j : H.carrier))) ((m : H.carrier)) := by
    funext t
    refine Fin.lastCases ?_ (fun j => ?_) t <;> simp
  rw [heq] at h2
  exact h2.trans hd

/-- **The two sides of a homogeneous pair are isomorphic.**  Consequently the pair carries an
elementary self-embedding whose range is exactly the predicate and which fixes any prescribed
tuple from the predicate. -/
theorem HomogPair.exists_selfEmb (H : HomogPair L) {n : ℕ} (b : Fin n → H.carrier)
    (hb : ∀ i, b i ∈ predSet L H.carrier) :
    ∃ f : H.carrier ↪ₑ[L] H.carrier,
      Set.range (f : H.carrier → H.carrier) = predSet L H.carrier ∧ ∀ i, f (b i) = b i := by
  have hbb : SameType L b fun i => (⟨b i, hb i⟩ : (H.pred : Type)) :=
    SameType.symm (sameType_of_elementaryEmbedding H.pred.subtype
      fun i => (⟨b i, hb i⟩ : (H.pred : Type)))
  obtain ⟨e, he⟩ := nonempty_equiv_of_same_types_of_countable b
    (fun i => (⟨b i, hb i⟩ : (H.pred : Type))) hbb H.isTypeExtensionPair_pred
    H.isTypeExtensionPair_pred'
  refine ⟨H.pred.subtype.comp e.toElementaryEmbedding, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro i
    have : e (b i) = (⟨b i, hb i⟩ : (H.pred : Type)) := he i
    simp [this]

/-! ## The index type of the `ω₁`-chain -/

/-- The countable ordinals, as the index type of the `ω₁`-chain. -/
abbrev Om : Type := (ℵ₁ : Cardinal.{0}).ord.ToType

instance : Nonempty Om :=
  Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans aleph0_lt_aleph_one).ne'

theorem mk_Om : #Om = ℵ₁ := Cardinal.mk_ord_toType _

theorem mk_Iio_Om_le (i : Om) : #(Set.Iio i) ≤ ℵ₀ := by
  refine Cardinal.lt_aleph_one_iff.1 ?_
  have h : Cardinal.ord #Om = @Ordinal.type Om (· < ·) inferInstance := by
    rw [mk_Om]
    exact (Ordinal.type_toType _).symm
  have h2 := Cardinal.mk_Iio_lt i h
  rwa [mk_Om] at h2

theorem exists_gt_Om (a : Om) : ∃ c : Om, a < c := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have hinj : Function.Injective fun c : Om => (⟨c, hcon c⟩ : Set.Iic a) := by
    intro x y h
    simpa using h
  have h1 : #Om ≤ #(Set.Iic a) := Cardinal.mk_le_of_injective hinj
  have h3 : #(Set.Iic a : Set Om) ≤ ℵ₀ := by
    rw [← Set.Iio_insert]
    calc #(insert a (Set.Iio a) : Set Om) ≤ #(Set.Iio a : Set Om) + 1 := Cardinal.mk_insert_le
      _ ≤ ℵ₀ + 1 := add_le_add (mk_Iio_Om_le a) le_rfl
      _ = ℵ₀ := by simp
  rw [mk_Om] at h1
  exact absurd (h1.trans h3) (not_le.2 aleph0_lt_aleph_one)

/-- The least countable ordinal. -/
noncomputable def omBot : Om := wellFounded_lt.min Set.univ Set.univ_nonempty

theorem omBot_le (a : Om) : omBot ≤ a :=
  not_lt.1 (wellFounded_lt.not_lt_min Set.univ (Set.mem_univ a))

/-- The successor of a countable ordinal. -/
noncomputable def omSucc (a : Om) : Om := wellFounded_lt.min {c | a < c} (exists_gt_Om a)

theorem lt_omSucc (a : Om) : a < omSucc a :=
  wellFounded_lt.min_mem {c | a < c} (exists_gt_Om a)

theorem omSucc_le {a c : Om} (h : a < c) : omSucc a ≤ c :=
  not_lt.1 (wellFounded_lt.not_lt_min {c | a < c} h)

/-! ## Chains of copies of a fixed structure -/

@[simp]
theorem toLimitElementary_apply {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (C : ElementaryChain L ι) (i : ι) (x : C.carrier i) :
    C.toLimitElementary i x = C.toLimit i x := rfl

section ConstChain

variable {ι : Type} [Preorder ι] {A : Type} [L.Structure A]

/-- An elementary chain all of whose stages are the fixed structure `A`. -/
def constChain (mp : ∀ i j : ι, i ≤ j → A ↪ₑ[L] A)
    (hs : ∀ (i : ι) (x : A), mp i i le_rfl x = x)
    (hm : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : A),
      mp j k hjk (mp i j hij x) = mp i k (hij.trans hjk) x) :
    ElementaryChain L ι where
  carrier := fun _ => A
  map := mp
  map_self := hs
  map_map := hm

variable (mp : ∀ i j : ι, i ≤ j → A ↪ₑ[L] A)
  (hs : ∀ (i : ι) (x : A), mp i i le_rfl x = x)
  (hm : ∀ (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) (x : A),
    mp j k hjk (mp i j hij x) = mp i k (hij.trans hjk) x)

variable [IsDirectedOrder ι] [Nonempty ι]

theorem constChain_toLimit_map (i j : ι) (h : i ≤ j) (x : A) :
    (constChain mp hs hm).toLimit j (mp i j h x) = (constChain mp hs hm).toLimit i x :=
  (constChain mp hs hm).toLimit_map h x

omit [Nonempty ι] in
theorem mk_constChain_limit_le [Countable A] (hι : #ι ≤ ℵ₀) :
    #((constChain mp hs hm).Limit) ≤ ℵ₀ :=
  (constChain mp hs hm).mk_limit_le_of_lift_mk_le le_rfl (by simpa using hι)
    (fun i => by rw [Cardinal.lift_id]; exact Cardinal.mk_le_aleph0 (α := A))

theorem constChain_isTypeExtensionPair_left (hhom : IsTypeExtensionPair L A A) :
    IsTypeExtensionPair L A ((constChain mp hs hm).Limit) := by
  intro k a a' hst m
  obtain ⟨γ, z, hz⟩ := (constChain mp hs hm).exists_finite_common_stage (α := Fin k) a'
  have hz' : ∀ i, (constChain mp hs hm).toLimit γ (z i) = a' i := fun i => congrFun hz i
  have hzz : SameType L z fun i => (constChain mp hs hm).toLimit γ (z i) :=
    sameType_of_elementaryEmbedding ((constChain mp hs hm).toLimitElementary γ) z
  rw [funext hz'] at hzz
  obtain ⟨d, hd⟩ := hhom k a z (hst.trans hzz.symm) m
  refine ⟨(constChain mp hs hm).toLimit γ d, ?_⟩
  have hsn := sameType_of_elementaryEmbedding ((constChain mp hs hm).toLimitElementary γ)
    (Fin.snoc z d : Fin (k + 1) → A)
  have heq : (fun t => (constChain mp hs hm).toLimitElementary γ
      ((Fin.snoc z d : Fin (k + 1) → A) t))
      = Fin.snoc a' ((constChain mp hs hm).toLimit γ d) := by
    funext t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp
    · simp only [toLimitElementary_apply, Fin.snoc_castSucc]
      exact hz' t
  rw [heq] at hsn
  exact hd.trans hsn

theorem constChain_isTypeExtensionPair_right (hhom : IsTypeExtensionPair L A A) :
    IsTypeExtensionPair L ((constChain mp hs hm).Limit) A := by
  intro k a a' hst m
  obtain ⟨γ, z, hz⟩ := (constChain mp hs hm).exists_finite_common_stage
    (α := Fin k ⊕ Unit) (Sum.elim a fun _ => m)
  have hz1 : ∀ i, (constChain mp hs hm).toLimit γ (z (Sum.inl i)) = a i :=
    fun i => congrFun hz (Sum.inl i)
  have hz2 : (constChain mp hs hm).toLimit γ (z (Sum.inr ())) = m := congrFun hz (Sum.inr ())
  have h1 : SameType L (fun i => z (Sum.inl i)) a := by
    have hh := sameType_of_elementaryEmbedding ((constChain mp hs hm).toLimitElementary γ)
      fun i => z (Sum.inl i)
    simp only [toLimitElementary_apply] at hh
    rwa [funext hz1] at hh
  obtain ⟨d, hd⟩ := hhom k (fun i => z (Sum.inl i)) a' (h1.trans hst) (z (Sum.inr ()))
  refine ⟨d, ?_⟩
  have hsn := sameType_of_elementaryEmbedding ((constChain mp hs hm).toLimitElementary γ)
    (Fin.snoc (fun i => z (Sum.inl i)) (z (Sum.inr ())) : Fin (k + 1) → A)
  have heq : (fun t => (constChain mp hs hm).toLimitElementary γ
      ((Fin.snoc (fun i => z (Sum.inl i)) (z (Sum.inr ())) : Fin (k + 1) → A) t))
      = Fin.snoc a m := by
    funext t
    refine Fin.lastCases ?_ (fun t => ?_) t
    · simp only [toLimitElementary_apply, Fin.snoc_last]
      exact hz2
    · simp only [toLimitElementary_apply, Fin.snoc_castSucc]
      exact hz1 t
  rw [heq] at hsn
  exact hsn.symm.trans hd

end ConstChain

/-! ## Partial towers of elementary self-embeddings -/

section Tower

variable {A : Type} [L.Structure A] {n : ℕ}

/-- The set of indices at which a partial tower is defined. -/
def towerDom (F : Set (Om × Om × (A ↪ₑ[L] A))) : Set Om := {α | ∃ e, (α, α, e) ∈ F}

theorem towerDom_mono {F G : Set (Om × Om × (A ↪ₑ[L] A))} (h : F ⊆ G) :
    towerDom F ⊆ towerDom G := fun _ ⟨e, he⟩ => ⟨e, h he⟩

/-- The invariants carried through the transfinite construction of the `ω₁`-chain: `F` is the
graph of a coherent family of elementary self-embeddings of `A`, indexed by an initial segment of
the countable ordinals, fixing the parameter tuple `b`, whose ranges contain the set defined by
`χ` and are proper at strict inequalities. -/
structure IsTower (b : Fin n → A) (χ : L.BoundedFormula (Fin n) 1)
    (F : Set (Om × Om × (A ↪ₑ[L] A))) : Prop where
  /-- Indices are ordered. -/
  le : ∀ p ∈ F, p.1 ≤ p.2.1
  /-- The left index lies in the domain. -/
  dom_left : ∀ p ∈ F, p.1 ∈ towerDom F
  /-- The right index lies in the domain. -/
  dom_right : ∀ p ∈ F, p.2.1 ∈ towerDom F
  /-- The family is well defined. -/
  functional : ∀ (α β : Om) (e e' : A ↪ₑ[L] A), (α, β, e) ∈ F → (α, β, e') ∈ F → ∀ x, e x = e' x
  /-- The family is defined at every comparable pair from the domain. -/
  exists_mem : ∀ α ∈ towerDom F, ∀ β ∈ towerDom F, α ≤ β → ∃ e, (α, β, e) ∈ F
  /-- The domain is an initial segment. -/
  downward : ∀ α ∈ towerDom F, ∀ γ, γ ≤ α → γ ∈ towerDom F
  /-- The diagonal maps are the identity. -/
  self_apply : ∀ (α : Om) (e : A ↪ₑ[L] A), (α, α, e) ∈ F → ∀ x, e x = x
  /-- The cocycle condition. -/
  comp_apply : ∀ (α β γ : Om) (e e' e'' : A ↪ₑ[L] A), (α, β, e) ∈ F → (β, γ, e') ∈ F →
    (α, γ, e'') ∈ F → ∀ x, e'' x = e' (e x)
  /-- The parameter tuple is fixed. -/
  fixes : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → ∀ i, e (b i) = b i
  /-- The definable set is contained in every range. -/
  def_subset : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → ∀ a : A,
    χ.Realize b (fun _ => a) → a ∈ Set.range (e : A → A)
  /-- Strict steps are not surjective. -/
  proper : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → α < β →
    ∃ w : A, w ∉ Set.range (e : A → A)

theorem chain_pair {X : Type} {c : Set (Set X)} (hc : IsChain (· ⊆ ·) c) {x y : X}
    (hx : x ∈ ⋃₀ c) (hy : y ∈ ⋃₀ c) : ∃ F ∈ c, x ∈ F ∧ y ∈ F := by
  obtain ⟨F₁, hF₁, hx⟩ := hx
  obtain ⟨F₂, hF₂, hy⟩ := hy
  rcases eq_or_ne F₁ F₂ with rfl | hne
  · exact ⟨F₁, hF₁, hx, hy⟩
  · rcases hc hF₁ hF₂ hne with h | h
    · exact ⟨F₂, hF₂, h hx, hy⟩
    · exact ⟨F₁, hF₁, hx, h hy⟩

theorem chain_triple {X : Type} {c : Set (Set X)} (hc : IsChain (· ⊆ ·) c) {x y z : X}
    (hx : x ∈ ⋃₀ c) (hy : y ∈ ⋃₀ c) (hz : z ∈ ⋃₀ c) :
    ∃ F ∈ c, x ∈ F ∧ y ∈ F ∧ z ∈ F := by
  obtain ⟨F₁, hF₁, hx, hy⟩ := chain_pair hc hx hy
  obtain ⟨F₂, hF₂, hxy, hz⟩ := chain_pair (x := x) (y := z) hc ⟨F₁, hF₁, hx⟩ hz
  rcases eq_or_ne F₁ F₂ with rfl | hne
  · exact ⟨F₁, hF₁, hx, hy, hz⟩
  · rcases hc hF₁ hF₂ hne with h | h
    · exact ⟨F₂, hF₂, hxy, h hy, hz⟩
    · exact ⟨F₁, hF₁, hx, hy, h hz⟩

theorem mem_towerDom_sUnion {c : Set (Set (Om × Om × (A ↪ₑ[L] A)))} {α : Om} :
    α ∈ towerDom (⋃₀ c) ↔ ∃ F ∈ c, α ∈ towerDom F := by
  constructor
  · rintro ⟨e, F, hF, he⟩
    exact ⟨F, hF, e, he⟩
  · rintro ⟨F, hF, e, he⟩
    exact ⟨e, F, hF, he⟩

theorem isTower_sUnion {b : Fin n → A} {χ : L.BoundedFormula (Fin n) 1}
    {c : Set (Set (Om × Om × (A ↪ₑ[L] A)))} (hcS : ∀ F ∈ c, IsTower b χ F)
    (hc : IsChain (· ⊆ ·) c) : IsTower b χ (⋃₀ c) where
  le := by rintro p ⟨F, hF, hp⟩; exact (hcS F hF).le p hp
  dom_left := by
    rintro p ⟨F, hF, hp⟩
    exact towerDom_mono (Set.subset_sUnion_of_mem hF) ((hcS F hF).dom_left p hp)
  dom_right := by
    rintro p ⟨F, hF, hp⟩
    exact towerDom_mono (Set.subset_sUnion_of_mem hF) ((hcS F hF).dom_right p hp)
  functional := by
    intro α β e e' h h' x
    obtain ⟨F, hF, h1, h2⟩ := chain_pair hc h h'
    exact (hcS F hF).functional α β e e' h1 h2 x
  exists_mem := by
    intro α hα β hβ hab
    obtain ⟨F₁, hF₁, hα⟩ := mem_towerDom_sUnion.1 hα
    obtain ⟨F₂, hF₂, hβ⟩ := mem_towerDom_sUnion.1 hβ
    obtain ⟨e₁, he₁⟩ := hα
    obtain ⟨e₂, he₂⟩ := hβ
    obtain ⟨F, hF, h1, h2⟩ :=
      chain_pair hc (⟨F₁, hF₁, he₁⟩ : (α, α, e₁) ∈ ⋃₀ c) (⟨F₂, hF₂, he₂⟩ : (β, β, e₂) ∈ ⋃₀ c)
    obtain ⟨e, he⟩ := (hcS F hF).exists_mem α ⟨e₁, h1⟩ β ⟨e₂, h2⟩ hab
    exact ⟨e, F, hF, he⟩
  downward := by
    intro α hα γ hγ
    obtain ⟨F, hF, hα⟩ := mem_towerDom_sUnion.1 hα
    exact mem_towerDom_sUnion.2 ⟨F, hF, (hcS F hF).downward α hα γ hγ⟩
  self_apply := by
    rintro α e ⟨F, hF, he⟩ x
    exact (hcS F hF).self_apply α e he x
  comp_apply := by
    intro α β γ e e' e'' h h' h'' x
    obtain ⟨F, hF, h1, h2, h3⟩ := chain_triple hc h h' h''
    exact (hcS F hF).comp_apply α β γ e e' e'' h1 h2 h3 x
  fixes := by rintro α β e ⟨F, hF, he⟩ i; exact (hcS F hF).fixes α β e he i
  def_subset := by rintro α β e ⟨F, hF, he⟩ a ha; exact (hcS F hF).def_subset α β e he a ha
  proper := by rintro α β e ⟨F, hF, he⟩ hlt; exact (hcS F hF).proper α β e he hlt

/-- The one-step extension of a partial tower by a new top index `lam`, glued by the family
`glue`. -/
def extendTower (F : Set (Om × Om × (A ↪ₑ[L] A))) (glue : Om → (A ↪ₑ[L] A)) (lam : Om) :
    Set (Om × Om × (A ↪ₑ[L] A)) :=
  {p | p ∈ F ∨ (p.2.1 = lam ∧ p.1 < lam ∧ p.2.2 = glue p.1) ∨
    (p.1 = lam ∧ p.2.1 = lam ∧ p.2.2 = ElementaryEmbedding.refl L A)}

theorem mem_extendTower {F : Set (Om × Om × (A ↪ₑ[L] A))} {glue : Om → (A ↪ₑ[L] A)} {lam : Om}
    {α β : Om} {e : A ↪ₑ[L] A} :
    (α, β, e) ∈ extendTower F glue lam ↔
      (α, β, e) ∈ F ∨ (β = lam ∧ α < lam ∧ e = glue α) ∨
        (α = lam ∧ β = lam ∧ e = ElementaryEmbedding.refl L A) := Iff.rfl

variable {b : Fin n → A} {χ : L.BoundedFormula (Fin n) 1}

/-- **The generic one-step extension of a partial tower.**  Given a compatible family of gluing
maps out of the stages below `lam`, the tower extends to `lam`. -/
theorem isTower_extendTower {F : Set (Om × Om × (A ↪ₑ[L] A))} (hF : IsTower b χ F) {lam : Om}
    (hdom : towerDom F = Set.Iio lam) (glue : Om → (A ↪ₑ[L] A))
    (hG1 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → ∀ x, glue β (e x) = glue α x)
    (hG2 : ∀ α < lam, ∀ i, glue α (b i) = b i)
    (hG3 : ∀ α < lam, ∀ a : A, χ.Realize b (fun _ => a) → a ∈ Set.range (glue α : A → A))
    (hG4 : ∀ α < lam, ∃ w : A, w ∉ Set.range (glue α : A → A)) :
    IsTower b χ (extendTower F glue lam) ∧ lam ∈ towerDom (extendTower F glue lam) := by
  have hFlt1 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → α < lam := by
    intro α β e h
    have h2 := hF.dom_left (α, β, e) h
    rwa [hdom] at h2
  have hFlt2 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → β < lam := by
    intro α β e h
    have h2 := hF.dom_right (α, β, e) h
    rwa [hdom] at h2
  have hdomG : ∀ α : Om, α ∈ towerDom (extendTower F glue lam) ↔ α ≤ lam := by
    intro α
    constructor
    · rintro ⟨e, he⟩
      rcases mem_extendTower.1 he with h | ⟨-, h2, -⟩ | ⟨h1, -, -⟩
      · exact le_of_lt (hFlt1 α α e h)
      · exact le_of_lt h2
      · exact le_of_eq h1
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hmem : α ∈ towerDom F := by rw [hdom]; exact hlt
        obtain ⟨e, he⟩ := hmem
        exact ⟨e, mem_extendTower.2 (Or.inl he)⟩
      · exact ⟨ElementaryEmbedding.refl L A,
          mem_extendTower.2 (Or.inr (Or.inr ⟨heq, heq, rfl⟩))⟩
  have hleG : ∀ (u v : Om) (w : A ↪ₑ[L] A), (u, v, w) ∈ extendTower F glue lam → u ≤ v := by
    intro u v w h
    rcases mem_extendTower.1 h with h | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact hF.le _ h
    · rw [h1]; exact le_of_lt h2
    · rw [h1, h2]
  have hleLam : ∀ (u v : Om) (w : A ↪ₑ[L] A), (u, v, w) ∈ extendTower F glue lam → v ≤ lam := by
    intro u v w h
    rcases mem_extendTower.1 h with h | ⟨h1, -, -⟩ | ⟨-, h2, -⟩
    · exact le_of_lt (hFlt2 u v w h)
    · exact le_of_eq h1
    · exact le_of_eq h2
  have hinF : ∀ (u v : Om) (w : A ↪ₑ[L] A), (u, v, w) ∈ extendTower F glue lam → v ≠ lam →
      (u, v, w) ∈ F := by
    intro u v w h hv
    rcases mem_extendTower.1 h with h | ⟨h1, -, -⟩ | ⟨-, h2, -⟩
    · exact h
    · exact absurd h1 hv
    · exact absurd h2 hv
  have hkey : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ extendTower F glue lam → β = lam →
      (α < lam ∧ e = glue α) ∨ (α = lam ∧ e = ElementaryEmbedding.refl L A) := by
    intro α β e he hb
    rcases mem_extendTower.1 he with h | ⟨-, h2, h3⟩ | ⟨h1, -, h3⟩
    · exact absurd (hb ▸ hFlt2 α β e h) (lt_irrefl lam)
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h1, h3⟩
  have hfun : ∀ (α β : Om) (e e' : A ↪ₑ[L] A), (α, β, e) ∈ extendTower F glue lam →
      (α, β, e') ∈ extendTower F glue lam → ∀ x, e x = e' x := by
    intro α β e e' he he' x
    by_cases hβ : β = lam
    · rcases hkey α β e he hβ with ⟨h2, h3⟩ | ⟨h1, h3⟩ <;>
        rcases hkey α β e' he' hβ with ⟨h2', h3'⟩ | ⟨h1', h3'⟩
      · rw [h3, h3']
      · exact absurd h1' (ne_of_lt h2)
      · exact absurd h1 (ne_of_lt h2')
      · rw [h3, h3']
    · exact hF.functional α β e e' (hinF α β e he hβ) (hinF α β e' he' hβ) x
  refine ⟨?_, (hdomG lam).2 le_rfl⟩
  refine ⟨?_, ?_, ?_, hfun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨α, β, e⟩ h
    exact hleG α β e h
  · rintro ⟨α, β, e⟩ h
    refine (hdomG α).2 ((hleG α β e h).trans (hleLam α β e h))
  · rintro ⟨α, β, e⟩ h
    exact (hdomG β).2 (hleLam α β e h)
  · intro α hα β hβ hab
    rw [hdomG] at hα hβ
    rcases lt_or_eq_of_le hβ with hlt | heq
    · have hαF : α ∈ towerDom F := by rw [hdom]; exact lt_of_le_of_lt hab hlt
      have hβF : β ∈ towerDom F := by rw [hdom]; exact hlt
      obtain ⟨e, he⟩ := hF.exists_mem α hαF β hβF hab
      exact ⟨e, mem_extendTower.2 (Or.inl he)⟩
    · rcases lt_or_eq_of_le hab with hlt | heq2
      · exact ⟨glue α, mem_extendTower.2 (Or.inr (Or.inl ⟨heq, heq ▸ hlt, rfl⟩))⟩
      · exact ⟨ElementaryEmbedding.refl L A,
          mem_extendTower.2 (Or.inr (Or.inr ⟨heq2 ▸ heq, heq, rfl⟩))⟩
  · intro α hα γ hγ
    rw [hdomG] at hα ⊢
    exact hγ.trans hα
  · intro α e he x
    rcases mem_extendTower.1 he with h | ⟨h1, h2, -⟩ | ⟨-, -, h3⟩
    · exact hF.self_apply α e h x
    · exact absurd (h1 ▸ h2) (lt_irrefl α)
    · rw [h3]; rfl
  · intro α β γ e e' e'' he he' he'' x
    by_cases hγ : γ = lam
    · by_cases hβ : β = lam
      · have hid : ∀ y, e' y = y := by
          intro y
          rcases mem_extendTower.1 he' with h | ⟨-, h2, -⟩ | ⟨-, -, h3⟩
          · exact absurd (hβ ▸ hFlt1 β γ e' h) (lt_irrefl lam)
          · exact absurd (hβ ▸ h2) (lt_irrefl lam)
          · rw [h3]; rfl
        rw [hid]
        have hγβ : γ = β := hγ.trans hβ.symm
        rw [hγβ] at he''
        exact hfun α β e'' e he'' he x
      · have heF : (α, β, e) ∈ F := hinF α β e he hβ
        have hαlt : α < lam := hFlt1 α β e heF
        have hβlt : β < lam := hFlt2 α β e heF
        have he'g : e' = glue β := by
          rcases mem_extendTower.1 he' with h | ⟨-, -, h3⟩ | ⟨h1, -, -⟩
          · exact absurd (hγ ▸ hFlt2 β γ e' h) (lt_irrefl lam)
          · exact h3
          · exact absurd h1 hβ
        have he''g : e'' = glue α := by
          rcases mem_extendTower.1 he'' with h | ⟨-, -, h3⟩ | ⟨h1, -, -⟩
          · exact absurd (hγ ▸ hFlt2 α γ e'' h) (lt_irrefl lam)
          · exact h3
          · exact absurd (h1 ▸ hαlt) (lt_irrefl lam)
        rw [he'g, he''g]
        exact (hG1 α β e heF x).symm
    · have hγlt : γ < lam := lt_of_le_of_ne (hleLam β γ e' he') hγ
      have hβγ : β ≤ γ := hleG β γ e' he'
      have hβne : β ≠ lam := ne_of_lt (lt_of_le_of_lt hβγ hγlt)
      exact hF.comp_apply α β γ e e' e'' (hinF α β e he hβne) (hinF β γ e' he' hγ)
        (hinF α γ e'' he'' hγ) x
  · intro α β e he i
    rcases mem_extendTower.1 he with h | ⟨-, h2, h3⟩ | ⟨-, -, h3⟩
    · exact hF.fixes α β e h i
    · rw [h3]; exact hG2 α h2 i
    · rw [h3]; rfl
  · intro α β e he a ha
    rcases mem_extendTower.1 he with h | ⟨-, h2, h3⟩ | ⟨-, -, h3⟩
    · exact hF.def_subset α β e h a ha
    · rw [h3]; exact hG3 α h2 a ha
    · exact ⟨a, by rw [h3]; rfl⟩
  · intro α β e he hlt
    rcases mem_extendTower.1 he with h | ⟨-, h2, h3⟩ | ⟨h1, h2, -⟩
    · exact hF.proper α β e h hlt
    · obtain ⟨w, hw⟩ := hG4 α h2
      exact ⟨w, by rw [h3]; exact hw⟩
    · exact absurd (h1.trans h2.symm) (ne_of_lt hlt)

/-- An elementary self-embedding fixing `b` preserves and reflects the set defined by `χ`. -/
theorem realize_of_selfEmb (j : A ↪ₑ[L] A) (hjb : ∀ i, j (b i) = b i) (y : A) :
    χ.Realize b (fun _ => j y) ↔ χ.Realize b (fun _ => y) := by
  have h := j.map_boundedFormula χ b (fun _ : Fin 1 => y)
  rw [show (j : A → A) ∘ b = b from funext hjb,
    show (j : A → A) ∘ (fun _ : Fin 1 => y) = (fun _ : Fin 1 => j y) from rfl] at h
  exact h

/-- **The successor step.** -/
theorem exists_tower_succ {F : Set (Om × Om × (A ↪ₑ[L] A))} (hF : IsTower b χ F) {lam mu : Om}
    (hdom : towerDom F = Set.Iio lam) (hmu : mu < lam) (hmax : ∀ α < lam, α ≤ mu)
    (j : A ↪ₑ[L] A) (hjb : ∀ i, j (b i) = b i) (x₀ : A) (hx₀ : x₀ ∉ Set.range (j : A → A))
    (hDj : ∀ a : A, χ.Realize b (fun _ => a) → a ∈ Set.range (j : A → A)) :
    ∃ G, F ⊆ G ∧ IsTower b χ G ∧ lam ∈ towerDom G := by
  classical
  have hmuF : mu ∈ towerDom F := by rw [hdom]; exact hmu
  have hchoice : ∀ α : Om, ∃ e : A ↪ₑ[L] A, α < lam → (α, mu, e) ∈ F := by
    intro α
    by_cases h : α < lam
    · have hαF : α ∈ towerDom F := by rw [hdom]; exact h
      obtain ⟨e, he⟩ := hF.exists_mem α hαF mu hmuF (hmax α h)
      exact ⟨e, fun _ => he⟩
    · exact ⟨ElementaryEmbedding.refl L A, fun hc => absurd hc h⟩
  choose em hem using hchoice
  have hFlt1 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → α < lam := by
    intro α β e h
    have h2 := hF.dom_left (α, β, e) h
    rwa [hdom] at h2
  have hFlt2 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → β < lam := by
    intro α β e h
    have h2 := hF.dom_right (α, β, e) h
    rwa [hdom] at h2
  have hG1 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → ∀ x,
      (j.comp (em β)) (e x) = (j.comp (em α)) x := by
    intro α β e he x
    have hα : α < lam := hFlt1 α β e he
    have hβ : β < lam := hFlt2 α β e he
    have hc := hF.comp_apply α β mu e (em β) (em α) he (hem β hβ) (hem α hα) x
    simp only [ElementaryEmbedding.comp_apply]
    rw [hc]
  have hG2 : ∀ α < lam, ∀ i, (j.comp (em α)) (b i) = b i := by
    intro α hα i
    simp only [ElementaryEmbedding.comp_apply]
    rw [hF.fixes α mu (em α) (hem α hα) i, hjb i]
  have hG3 : ∀ α < lam, ∀ a : A, χ.Realize b (fun _ => a) →
      a ∈ Set.range ((j.comp (em α)) : A → A) := by
    intro α hα a ha
    obtain ⟨y, rfl⟩ := hDj a ha
    have hy : χ.Realize b (fun _ => y) := (realize_of_selfEmb j hjb y).1 ha
    obtain ⟨z, hz⟩ := hF.def_subset α mu (em α) (hem α hα) y hy
    exact ⟨z, by simp only [ElementaryEmbedding.comp_apply]; rw [hz]⟩
  have hG4 : ∀ α < lam, ∃ w : A, w ∉ Set.range ((j.comp (em α)) : A → A) := by
    intro α _
    refine ⟨x₀, fun hcon => hx₀ ?_⟩
    obtain ⟨z, hz⟩ := hcon
    exact ⟨em α z, by rw [← hz]; rfl⟩
  obtain ⟨h1, h2⟩ := isTower_extendTower hF hdom (fun α => j.comp (em α)) hG1 hG2 hG3 hG4
  exact ⟨_, fun p hp => Or.inl hp, h1, h2⟩

/-- **The limit step.** -/
theorem exists_tower_limit [Countable A] [Nonempty A] (hhom : IsTypeExtensionPair L A A)
    {F : Set (Om × Om × (A ↪ₑ[L] A))} (hF : IsTower b χ F) {lam : Om}
    (hdom : towerDom F = Set.Iio lam) (hne : (Set.Iio lam).Nonempty)
    (hnomax : ∀ α < lam, ∃ β, β < lam ∧ α < β) :
    ∃ G, F ⊆ G ∧ IsTower b χ G ∧ lam ∈ towerDom G := by
  classical
  haveI : Nonempty ↥(Set.Iio lam) := hne.to_subtype
  have hmemF : ∀ α : ↥(Set.Iio lam), (α : Om) ∈ towerDom F := by
    intro α; rw [hdom]; exact α.2
  have hchoice : ∀ (α β : ↥(Set.Iio lam)), α ≤ β →
      ∃ e : A ↪ₑ[L] A, ((α : Om), (β : Om), e) ∈ F :=
    fun α β hab => hF.exists_mem _ (hmemF α) _ (hmemF β) hab
  choose em hem using hchoice
  have hself : ∀ (i : ↥(Set.Iio lam)) (x : A), em i i le_rfl x = x :=
    fun i x => hF.self_apply _ _ (hem i i le_rfl) x
  have hcp : ∀ (i j k : ↥(Set.Iio lam)) (hij : i ≤ j) (hjk : j ≤ k) (x : A),
      em j k hjk (em i j hij x) = em i k (hij.trans hjk) x :=
    fun i j k hij hjk x =>
      (hF.comp_apply _ _ _ _ _ _ (hem i j hij) (hem j k hjk) (hem i k (hij.trans hjk)) x).symm
  haveI : Countable (constChain em hself hcp).Limit :=
    Cardinal.mk_le_aleph0_iff.1 (mk_constChain_limit_le em hself hcp (mk_Iio_Om_le lam))
  obtain ⟨α₀, hα₀⟩ := hne
  have hbconst : ∀ (α : ↥(Set.Iio lam)) (i : Fin n),
      (constChain em hself hcp).toLimit α (b i)
        = (constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i) := by
    intro α i
    obtain ⟨γ, hγ1, hγ2⟩ := exists_ge_ge α (⟨α₀, hα₀⟩ : ↥(Set.Iio lam))
    rw [← constChain_toLimit_map em hself hcp α γ hγ1 (b i),
      ← constChain_toLimit_map em hself hcp ⟨α₀, hα₀⟩ γ hγ2 (b i),
      hF.fixes _ _ _ (hem α γ hγ1) i, hF.fixes _ _ _ (hem ⟨α₀, hα₀⟩ γ hγ2) i]
  have hsameB : SameType L (fun i => (constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i)) b := by
    have h := sameType_of_elementaryEmbedding
      ((constChain em hself hcp).toLimitElementary ⟨α₀, hα₀⟩) b
    simp only [toLimitElementary_apply] at h
    exact h.symm
  obtain ⟨g, hg⟩ := nonempty_equiv_of_same_types_of_countable
    (fun i => (constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i)) b hsameB
    (constChain_isTypeExtensionPair_right em hself hcp hhom)
    (constChain_isTypeExtensionPair_left em hself hcp hhom)
  have hsymm : ∀ i, (g.symm : A → _) (b i)
      = (constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i) := by
    intro i
    have h : (g.symm : A → _) (g ((constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i)))
        = (constChain em hself hcp).toLimit ⟨α₀, hα₀⟩ (b i) := by simp
    rw [hg i] at h
    exact h
  obtain ⟨glue, hglue⟩ : ∃ glue : Om → (A ↪ₑ[L] A), ∀ (α : ↥(Set.Iio lam)) (x : A),
      glue (α : Om) x = g ((constChain em hself hcp).toLimit α x) := by
    have hex : ∀ β : Om, ∃ e : A ↪ₑ[L] A, ∀ (h : β ∈ Set.Iio lam) (x : A),
        e x = g ((constChain em hself hcp).toLimit ⟨β, h⟩ x) := by
      intro β
      by_cases h : β ∈ Set.Iio lam
      · exact ⟨g.toElementaryEmbedding.comp ((constChain em hself hcp).toLimitElementary ⟨β, h⟩),
          fun _ _ => rfl⟩
      · exact ⟨ElementaryEmbedding.refl L A, fun h' _ => absurd h' h⟩
    choose glue hglue using hex
    exact ⟨glue, fun α x => hglue (α : Om) α.2 x⟩
  have hG1 : ∀ (α β : Om) (e : A ↪ₑ[L] A), (α, β, e) ∈ F → ∀ x, glue β (e x) = glue α x := by
    intro α β e he x
    have hα : α < lam := by have h := hF.dom_left (α, β, e) he; rwa [hdom] at h
    have hβ : β < lam := by have h := hF.dom_right (α, β, e) he; rwa [hdom] at h
    have hab : (⟨α, hα⟩ : ↥(Set.Iio lam)) ≤ ⟨β, hβ⟩ := hF.le (α, β, e) he
    rw [hglue ⟨β, hβ⟩ (e x), hglue ⟨α, hα⟩ x,
      hF.functional α β e (em ⟨α, hα⟩ ⟨β, hβ⟩ hab) he (hem ⟨α, hα⟩ ⟨β, hβ⟩ hab) x,
      constChain_toLimit_map]
  have hG2 : ∀ α < lam, ∀ i, glue α (b i) = b i := by
    intro α hα i
    rw [hglue ⟨α, hα⟩ (b i), hbconst ⟨α, hα⟩ i]
    exact hg i
  have hG3 : ∀ α < lam, ∀ a : A, χ.Realize b (fun _ => a) →
      a ∈ Set.range (glue α : A → A) := by
    intro α hα a ha
    obtain ⟨γ, y, hy⟩ := (constChain em hself hcp).exists_toLimit (g.symm a)
    obtain ⟨δ, hδ1, hδ2⟩ := exists_ge_ge γ (⟨α, hα⟩ : ↥(Set.Iio lam))
    have hu : (constChain em hself hcp).toLimit δ (em γ δ hδ1 y) = g.symm a := by
      rw [constChain_toLimit_map]; exact hy
    have hchi : χ.Realize b (fun _ => em γ δ hδ1 y) := by
      have h1 := (g.symm.toElementaryEmbedding.map_boundedFormula χ b (fun _ : Fin 1 => a)).2 ha
      have h4 := ((constChain em hself hcp).toLimitElementary δ).map_boundedFormula χ b
        (fun _ : Fin 1 => em γ δ hδ1 y)
      refine h4.1 ?_
      have e2 : ((constChain em hself hcp).toLimitElementary δ : A → _) ∘ b
          = (g.symm : A → _) ∘ b := by
        funext i
        simp only [Function.comp_apply, toLimitElementary_apply]
        rw [hsymm i, hbconst δ i]
      have e3 : ((constChain em hself hcp).toLimitElementary δ : A → _) ∘
          (fun _ : Fin 1 => em γ δ hδ1 y) = (g.symm : A → _) ∘ (fun _ : Fin 1 => a) := by
        funext i
        simp only [Function.comp_apply, toLimitElementary_apply]
        rw [hu]
      rw [e2, e3]
      exact h1
    obtain ⟨w, hw⟩ := hF.def_subset α δ (em ⟨α, hα⟩ δ hδ2) (hem ⟨α, hα⟩ δ hδ2) _ hchi
    refine ⟨w, ?_⟩
    rw [hglue ⟨α, hα⟩ w,
      ← constChain_toLimit_map em hself hcp ⟨α, hα⟩ δ hδ2 w, hw, hu]
    simp
  have hG4 : ∀ α < lam, ∃ w : A, w ∉ Set.range (glue α : A → A) := by
    intro α hα
    obtain ⟨β, hβlt, hαβ⟩ := hnomax α hα
    have hle : (⟨α, hα⟩ : ↥(Set.Iio lam)) ≤ ⟨β, hβlt⟩ := le_of_lt hαβ
    obtain ⟨v, hv⟩ := hF.proper α β (em ⟨α, hα⟩ ⟨β, hβlt⟩ hle) (hem ⟨α, hα⟩ ⟨β, hβlt⟩ hle) hαβ
    refine ⟨g ((constChain em hself hcp).toLimit ⟨β, hβlt⟩ v), ?_⟩
    rintro ⟨w, hw⟩
    rw [hglue ⟨α, hα⟩ w] at hw
    have h1 : (constChain em hself hcp).toLimit ⟨α, hα⟩ w
        = (constChain em hself hcp).toLimit ⟨β, hβlt⟩ v := EquivLike.injective g hw
    rw [← constChain_toLimit_map em hself hcp ⟨α, hα⟩ ⟨β, hβlt⟩ hle w] at h1
    exact hv ⟨w, ((constChain em hself hcp).toLimit ⟨β, hβlt⟩).injective h1⟩
  obtain ⟨h1, h2⟩ := isTower_extendTower hF hdom glue hG1 hG2 hG3 hG4
  exact ⟨_, fun p hp => Or.inl hp, h1, h2⟩

/-- **Zorn's lemma produces a tower defined at every countable ordinal.** -/
theorem exists_full_tower [Countable A] [Nonempty A] (hhom : IsTypeExtensionPair L A A)
    (j : A ↪ₑ[L] A) (hjb : ∀ i, j (b i) = b i) (x₀ : A) (hx₀ : x₀ ∉ Set.range (j : A → A))
    (hDj : ∀ a : A, χ.Realize b (fun _ => a) → a ∈ Set.range (j : A → A)) :
    ∃ F, IsTower b χ F ∧ towerDom F = Set.univ := by
  classical
  have hmem1 : ∀ (α β : Om) (e : A ↪ₑ[L] A),
      (α, β, e) ∈ ({(omBot, omBot, ElementaryEmbedding.refl L A)} :
        Set (Om × Om × (A ↪ₑ[L] A))) ↔
      (α = omBot ∧ β = omBot ∧ e = ElementaryEmbedding.refl L A) := by
    intro α β e
    simp [Prod.ext_iff]
  have hdom1 : towerDom ({(omBot, omBot, ElementaryEmbedding.refl L A)} :
      Set (Om × Om × (A ↪ₑ[L] A))) = {omBot} := by
    ext α
    constructor
    · rintro ⟨e, he⟩
      exact ((hmem1 α α e).1 he).1
    · rintro rfl
      exact ⟨ElementaryEmbedding.refl L A, (hmem1 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩
  have hstart : IsTower b χ ({(omBot, omBot, ElementaryEmbedding.refl L A)} :
      Set (Om × Om × (A ↪ₑ[L] A))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨α, β, e⟩ he
      obtain ⟨h1, h2, -⟩ := (hmem1 α β e).1 he
      rw [h1, h2]
    · rintro ⟨α, β, e⟩ he
      obtain ⟨h1, -, -⟩ := (hmem1 α β e).1 he
      rw [hdom1, h1]; rfl
    · rintro ⟨α, β, e⟩ he
      obtain ⟨-, h2, -⟩ := (hmem1 α β e).1 he
      rw [hdom1, h2]; rfl
    · intro α β e e' he he' x
      obtain ⟨-, -, h3⟩ := (hmem1 α β e).1 he
      obtain ⟨-, -, h3'⟩ := (hmem1 α β e').1 he'
      rw [h3, h3']
    · intro α hα β hβ _
      rw [hdom1] at hα hβ
      exact ⟨ElementaryEmbedding.refl L A, (hmem1 _ _ _).2 ⟨hα, hβ, rfl⟩⟩
    · intro α hα γ hγ
      rw [hdom1] at hα ⊢
      have : γ = omBot := le_antisymm (hα ▸ hγ) (omBot_le γ)
      exact this
    · intro α e he x
      obtain ⟨-, -, h3⟩ := (hmem1 α α e).1 he
      rw [h3]; rfl
    · intro α β γ e e' e'' he he' he'' x
      obtain ⟨-, -, h3⟩ := (hmem1 α β e).1 he
      obtain ⟨-, -, h3'⟩ := (hmem1 β γ e').1 he'
      obtain ⟨-, -, h3''⟩ := (hmem1 α γ e'').1 he''
      rw [h3, h3', h3'']
      rfl
    · intro α β e he i
      obtain ⟨-, -, h3⟩ := (hmem1 α β e).1 he
      rw [h3]; rfl
    · intro α β e he a _
      obtain ⟨-, -, h3⟩ := (hmem1 α β e).1 he
      exact ⟨a, by rw [h3]; rfl⟩
    · intro α β e he hlt
      obtain ⟨h1, h2, -⟩ := (hmem1 α β e).1 he
      exact absurd (h1.trans h2.symm) (ne_of_lt hlt)
  obtain ⟨M, hMsub, hMmax⟩ :=
    zorn_subset_nonempty {F : Set (Om × Om × (A ↪ₑ[L] A)) | IsTower b χ F}
      (fun c hcS hc _ => ⟨⋃₀ c, isTower_sUnion hcS hc, fun s hs => Set.subset_sUnion_of_mem hs⟩)
      _ hstart
  have hM : IsTower b χ M := hMmax.1
  refine ⟨M, hM, ?_⟩
  by_contra hne
  obtain ⟨z, hz⟩ : ((towerDom M)ᶜ).Nonempty := Set.nonempty_compl.2 hne
  set lam := wellFounded_lt.min (towerDom M)ᶜ ⟨z, hz⟩ with hlamdef
  have hlamnot : lam ∉ towerDom M := wellFounded_lt.min_mem (towerDom M)ᶜ ⟨z, hz⟩
  have hlt : ∀ γ, γ < lam → γ ∈ towerDom M := by
    intro γ hγ
    by_contra hcon
    exact wellFounded_lt.not_lt_min (towerDom M)ᶜ hcon hγ
  have hdomM : towerDom M = Set.Iio lam := by
    ext α
    constructor
    · intro hα
      by_contra hcon
      exact hlamnot (hM.downward α hα lam (not_lt.1 hcon))
    · exact hlt α
  have hbotM : omBot ∈ towerDom M :=
    towerDom_mono hMsub (by rw [hdom1]; rfl)
  have hbotlt : omBot < lam := by
    rcases lt_or_eq_of_le (omBot_le lam) with h | h
    · exact h
    · exact absurd (h ▸ hbotM) hlamnot
  have hIone : (Set.Iio lam).Nonempty := ⟨omBot, hbotlt⟩
  have hcontra : ∃ G, M ⊆ G ∧ IsTower b χ G ∧ lam ∈ towerDom G := by
    by_cases hmax : ∃ mu, mu < lam ∧ ∀ α < lam, α ≤ mu
    · obtain ⟨mu, hmu, hmu'⟩ := hmax
      exact exists_tower_succ hM hdomM hmu hmu' j hjb x₀ hx₀ hDj
    · refine exists_tower_limit hhom hM hdomM hIone ?_
      simp only [not_exists, not_and, not_forall] at hmax
      intro α hα
      obtain ⟨β, hβ1, hβ2⟩ := hmax α hα
      exact ⟨β, hβ1, not_le.1 hβ2⟩
  obtain ⟨G, hMG, hG, hlamG⟩ := hcontra
  exact hlamnot (towerDom_mono (hMmax.2 hG hMG) hlamG)

/-- **The `ω₁`-chain.**  From a self-embedding as above, a model of cardinality `ℵ₁` whose
`χ`-definable set over `b` is the image of the one in `A`. -/
theorem exists_omega1_model [Countable A] [Nonempty A] (hhom : IsTypeExtensionPair L A A)
    (j : A ↪ₑ[L] A) (hjb : ∀ i, j (b i) = b i) (x₀ : A) (hx₀ : x₀ ∉ Set.range (j : A → A))
    (hDj : ∀ a : A, χ.Realize b (fun _ => a) → a ∈ Set.range (j : A → A)) :
    ∃ (M : Type) (_ : L.Structure M) (f : A ↪ₑ[L] M),
      #M = ℵ₁ ∧
        {z : M | χ.Realize (fun i => f (b i)) fun _ => z}
          = (f : A → M) '' {a : A | χ.Realize b fun _ => a} := by
  classical
  obtain ⟨F, hF, hdom⟩ := exists_full_tower hhom j hjb x₀ hx₀ hDj
  have hmemF : ∀ α : Om, α ∈ towerDom F := by intro α; rw [hdom]; trivial
  have hchoice : ∀ (α β : Om), α ≤ β → ∃ e : A ↪ₑ[L] A, (α, β, e) ∈ F :=
    fun α β hab => hF.exists_mem _ (hmemF α) _ (hmemF β) hab
  choose em hem using hchoice
  have hself : ∀ (i : Om) (x : A), em i i le_rfl x = x :=
    fun i x => hF.self_apply _ _ (hem i i le_rfl) x
  have hcp : ∀ (i j' k : Om) (hij : i ≤ j') (hjk : j' ≤ k) (x : A),
      em j' k hjk (em i j' hij x) = em i k (hij.trans hjk) x :=
    fun i j' k hij hjk x =>
      (hF.comp_apply _ _ _ _ _ _ (hem i j' hij) (hem j' k hjk) (hem i k (hij.trans hjk)) x).symm
  have hcard : #((constChain em hself hcp).Limit) = ℵ₁ := by
    refine le_antisymm ?_ ?_
    · refine (constChain em hself hcp).mk_limit_le_of_lift_mk_le aleph0_lt_aleph_one.le
        (le_of_eq (by rw [Cardinal.lift_id]; exact mk_Om)) fun i => ?_
      rw [Cardinal.lift_id]
      exact (Cardinal.mk_le_aleph0 (α := A)).trans aleph0_lt_aleph_one.le
    · have hw : ∀ α : Om, ∃ w : A, w ∉ Set.range (em α (omSucc α) (le_of_lt (lt_omSucc α))) :=
        fun α => hF.proper α (omSucc α) _ (hem α (omSucc α) (le_of_lt (lt_omSucc α)))
          (lt_omSucc α)
      choose w hwspec using hw
      have hnot : ∀ (α : Om) (y : A),
          (constChain em hself hcp).toLimit (omSucc α) (w α)
            ≠ (constChain em hself hcp).toLimit α y := by
        intro α y hcon
        rw [← constChain_toLimit_map em hself hcp α (omSucc α) (le_of_lt (lt_omSucc α)) y] at hcon
        exact hwspec α ⟨y, ((constChain em hself hcp).toLimit (omSucc α)).injective hcon.symm⟩
      have hinj : Function.Injective
          fun α : Om => (constChain em hself hcp).toLimit (omSucc α) (w α) := by
        intro α β hab
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · refine hnot β ((em (omSucc α) β (omSucc_le h)) (w α)) ?_
          rw [constChain_toLimit_map]
          exact hab.symm
        · refine hnot α ((em (omSucc β) α (omSucc_le h)) (w β)) ?_
          rw [constChain_toLimit_map]
          exact hab
      have hle := Cardinal.mk_le_of_injective hinj
      rwa [mk_Om] at hle
  have hbconst : ∀ (γ : Om) (i : Fin n),
      (constChain em hself hcp).toLimit γ (b i)
        = (constChain em hself hcp).toLimit omBot (b i) := by
    intro γ i
    rw [← constChain_toLimit_map em hself hcp omBot γ (omBot_le γ) (b i),
      hF.fixes _ _ _ (hem omBot γ (omBot_le γ)) i]
  have hdefset : {z : (constChain em hself hcp).Limit |
      χ.Realize (fun i => (constChain em hself hcp).toLimit omBot (b i)) fun _ => z}
      = ((constChain em hself hcp).toLimit omBot : A → _) ''
        {a : A | χ.Realize b fun _ => a} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hzchi
      obtain ⟨γ, y, rfl⟩ := (constChain em hself hcp).exists_toLimit z
      have hy : χ.Realize b (fun _ => y) := by
        have h4 := ((constChain em hself hcp).toLimitElementary γ).map_boundedFormula χ b
          (fun _ : Fin 1 => y)
        refine h4.1 ?_
        have e2 : ((constChain em hself hcp).toLimitElementary γ : A → _) ∘ b
            = fun i => (constChain em hself hcp).toLimit omBot (b i) := by
          funext i
          simp only [Function.comp_apply, toLimitElementary_apply]
          exact hbconst γ i
        rw [e2]
        exact hzchi
      obtain ⟨u, hu⟩ := hF.def_subset omBot γ (em omBot γ (omBot_le γ))
        (hem omBot γ (omBot_le γ)) y hy
      refine ⟨u, ?_, ?_⟩
      · refine (realize_of_selfEmb (em omBot γ (omBot_le γ))
          (hF.fixes _ _ _ (hem omBot γ (omBot_le γ))) u).1 ?_
        rw [hu]
        exact hy
      · rw [← constChain_toLimit_map em hself hcp omBot γ (omBot_le γ) u, hu]
    · rintro ⟨a, ha, rfl⟩
      exact (((constChain em hself hcp).toLimitElementary omBot).map_boundedFormula χ b
        (fun _ : Fin 1 => a)).2 ha
  exact ⟨(constChain em hself hcp).Limit, inferInstance,
    (constChain em hself hcp).toLimitElementary omBot, hcard, hdefset⟩

end Tower

/-! ## Assembly -/

/-- The pair-language sentence scheme saying that the set defined by `χ` over the parameters is
contained in the predicate. -/
def defSubsetFormula (L : FirstOrder.Language.{0, 0}) {n : ℕ} (χ : L.BoundedFormula (Fin n) 1) :
    (L.sum predLang).BoundedFormula (Fin n) 0 :=
  ∀' (((pairInl L).onBoundedFormula χ) ⟹ predVarF L (0 : Fin 1))

theorem realize_defSubsetFormula {M : Type} [L.Structure M] [(L.sum predLang).Structure M]
    [(pairInl L).IsExpansionOn M] {n : ℕ} (χ : L.BoundedFormula (Fin n) 1) (v : Fin n → M) :
    (defSubsetFormula L χ).Realize v default ↔
      ∀ a : M, χ.Realize v (fun _ => a) → a ∈ predSet L M := by
  rw [defSubsetFormula, BoundedFormula.realize_all]
  refine forall_congr' fun a => ?_
  have hsn : (Fin.snoc (default : Fin 0 → M) a : Fin 1 → M) = fun _ => a := by
    funext i
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    rw [Fin.snoc_last]
  rw [BoundedFormula.realize_imp, LHom.realize_onBoundedFormula, realize_predVarF, hsn]

/-- **Vaught's two-cardinal theorem.** -/
theorem vaughtTwoCardinal (L : FirstOrder.Language.{0, 0}) : VaughtTwoCardinal L := by
  classical
  intro T hL _ hVP
  obtain ⟨V⟩ := nonempty_countableVPair hL hVP
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin V.paramType
  set χF : L.BoundedFormula (Fin n) 1 := BoundedFormula.relabelEquiv eq V.defFormula with hχF
  set bV : Fin n → V.carrier := V.params ∘ eq.symm with hbV
  have hrel : ∀ (M : Type) [L.Structure M] (v : V.paramType → M) (a : M),
      χF.Realize (v ∘ eq.symm) (fun _ => a) ↔ V.defFormula.Realize v (fun _ => a) := by
    intro M _ v a
    rw [hχF, BoundedFormula.realize_relabelEquiv]
    congr! 1
    funext i
    simp
  -- pass to a countable homogeneous pair
  obtain ⟨H, hfne⟩ :=
    exists_homogPair hL ({ carrier := V.carrier, models_pair := V.models_pair } : VStage L)
  obtain ⟨f0⟩ := hfne
  have f : V.carrier ↪ₑ[L.sum predLang] H.carrier := f0
  set bH : Fin n → H.carrier := fun i => f (bV i) with hbH
  have hbHmem : ∀ i, bH i ∈ predSet L H.carrier := by
    intro i
    exact (mem_predSet_pairEmbedding f (bV i)).2 (V.params_mem _)
  -- the definable set of the homogeneous pair
  have hdefsub : ∀ a : H.carrier, χF.Realize bH (fun _ => a) → a ∈ predSet L H.carrier := by
    have hV : (defSubsetFormula L χF).Realize bV (default : Fin 0 → V.carrier) := by
      rw [realize_defSubsetFormula]
      intro a ha
      exact V.defSet_subset a ((hrel V.carrier V.params a).1 ha)
    have htr := f.map_boundedFormula (defSubsetFormula L χF) bV (default : Fin 0 → V.carrier)
    rw [Subsingleton.elim ((f : V.carrier → H.carrier) ∘ (default : Fin 0 → V.carrier))
      (default : Fin 0 → H.carrier)] at htr
    have := htr.2 hV
    rwa [realize_defSubsetFormula] at this
  have hdefinf : {a : H.carrier | χF.Realize bH fun _ => a}.Infinite := by
    have himg := V.defSet_infinite.image (f.injective).injOn
    refine Set.Infinite.mono ?_ himg
    rintro _ ⟨a, ha, rfl⟩
    show χF.Realize bH fun _ => f a
    have h1 := realize_comp_pairEmbedding f χF bV (fun _ : Fin 1 => a)
    have h2 : ((f : V.carrier → H.carrier) ∘ bV) = bH := rfl
    have h3 : ((f : V.carrier → H.carrier) ∘ fun _ : Fin 1 => a) = fun _ => f a := rfl
    rw [h2, h3] at h1
    exact h1.2 ((hrel V.carrier V.params a).2 ha)
  -- a point outside the predicate
  obtain ⟨c, hc⟩ := Set.ne_univ_iff_exists_notMem _ |>.1 V.proper
  have hx₀ : f c ∉ predSet L H.carrier := fun hcon =>
    hc ((mem_predSet_pairEmbedding f c).1 hcon)
  -- the self-embedding
  obtain ⟨jj, hjjrange, hjjb⟩ := H.exists_selfEmb bH hbHmem
  have hDj : ∀ a : H.carrier, χF.Realize bH (fun _ => a) →
      a ∈ Set.range (jj : H.carrier → H.carrier) := by
    intro a ha
    rw [hjjrange]
    exact hdefsub a ha
  have hx₀' : f c ∉ Set.range (jj : H.carrier → H.carrier) := by rw [hjjrange]; exact hx₀
  -- the `ω₁`-chain
  obtain ⟨M, instM, fM, hMcard, hMdef⟩ :=
    exists_omega1_model H.isTypeExtensionPair_self jj hjjb (f c) hx₀' hDj
  letI : L.Structure M := instM
  haveI : Nonempty M := ⟨fM (Classical.arbitrary H.carrier)⟩
  -- `M` is a model of `T`
  have hVT : V.carrier ⊨ (pairInl L).onTheory T :=
    (LHom.onTheory_model (pairInl L) T).2 V.models_T
  have hHT : H.carrier ⊨ T :=
    (LHom.onTheory_model (pairInl L) T).1 ((f.theory_model_iff _).1 hVT)
  haveI : M ⊨ T := (fM.theory_model_iff T).1 hHT
  refine hasTwoCardinalModel_of_boundedFormula (T := T) M χF (fun i => fM (bH i)) hMcard ?_
  rw [hMdef]
  haveI : Countable ↥{a : H.carrier | χF.Realize bH fun _ => a} := Subtype.countable
  rw [Cardinal.mk_image_eq (fM.injective)]
  refine le_antisymm Cardinal.mk_le_aleph0 ?_
  rw [← Cardinal.infinite_iff, Set.infinite_coe_iff]
  exact hdefinf

end Submission.Morley
