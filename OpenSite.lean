import Init

/-!
# Open Sites, from compossibility
-/

namespace OpenSite

universe u v

/-! ## 0. Ontology: kinds as types of values -/

structure Ontology where
  Kind : Type u
  Value : Kind → Type v
  decEqKind : DecidableEq Kind

namespace Ontology

variable (O : Ontology.{u,v})

/-- A determination: a kind together with a value of it.  Single-valuedness
needs no axiom, since an assignment maps each kind to at most one value. -/
structure Det where
  kind : O.Kind
  value : O.Value kind

end Ontology

/-! ## 1. Assignments -/

def Assignment (O : Ontology.{u,v}) :=
  (k : O.Kind) → Option (O.Value k)

namespace Assignment

variable {O : Ontology.{u,v}}

def empty : Assignment O := fun _ => none

def set (σ : Assignment O) (k : O.Kind) (v : O.Value k) : Assignment O :=
  fun k' =>
    haveI := O.decEqKind
    if h : k' = k then some (h.symm ▸ v) else σ k'

theorem set_self (σ : Assignment O) (k : O.Kind) (v : O.Value k) :
    set σ k v k = some v := by
  unfold set
  rw [dif_pos rfl]

theorem set_ne (σ : Assignment O) (k : O.Kind) (v : O.Value k)
    (k' : O.Kind) (h : k' ≠ k) :
    set σ k v k' = σ k' := by
  unfold set
  rw [dif_neg h]

theorem set_comm {σ : Assignment O} {k ℓ : O.Kind}
    (hne : k ≠ ℓ) (v : O.Value k) (w : O.Value ℓ) :
    set (set σ k v) ℓ w = set (set σ ℓ w) k v := by
  funext k'
  haveI := O.decEqKind
  by_cases hℓ : k' = ℓ
  · rw [hℓ, set_self, set_ne (set σ ℓ w) k v ℓ (Ne.symm hne), set_self]
  · by_cases hk : k' = k
    · rw [hk, set_ne (set σ k v) ℓ w k hne, set_self, set_self]
    · rw [set_ne _ _ _ _ hℓ, set_ne _ _ _ _ hk,
          set_ne _ _ _ _ hk, set_ne _ _ _ _ hℓ]

theorem set_set_left {σ : Assignment O} {k ℓ : O.Kind}
    (hne : k ≠ ℓ) (v : O.Value k) (w : O.Value ℓ) :
    set (set σ k v) ℓ w k = some v := by
  rw [set_ne _ _ _ _ hne, set_self]

theorem set_set_right {σ : Assignment O} {k ℓ : O.Kind}
    (v : O.Value k) (w : O.Value ℓ) :
    set (set σ k v) ℓ w ℓ = some w :=
  set_self _ _ _

theorem set_set_same {σ : Assignment O} {k : O.Kind} (v w : O.Value k) :
    set (set σ k v) k w = set σ k w := by
  funext k'
  haveI := O.decEqKind
  by_cases hk : k' = k
  · subst hk; rw [set_self, set_self]
  · rw [set_ne _ _ _ _ hk, set_ne _ _ _ _ hk, set_ne _ _ _ _ hk]

theorem set_set_other {σ : Assignment O} {k ℓ k' : O.Kind}
    (hk : k' ≠ k) (hℓ : k' ≠ ℓ) (v : O.Value k) (w : O.Value ℓ) :
    set (set σ k v) ℓ w k' = σ k' := by
  rw [set_ne _ _ _ _ hℓ, set_ne _ _ _ _ hk]

/-- Dependent case split on a realised cell of `set`. -/
theorem realised_set_cases {σ : Assignment O} {k k' : O.Kind}
    {v : O.Value k} {v' : O.Value k'}
    (h : set σ k v k' = some v') {P : Prop}
    (self : (eq : k' = k) → (eq.symm ▸ v) = v' → P)
    (other : k' ≠ k → σ k' = some v' → P) : P := by
  haveI := O.decEqKind
  by_cases hk' : k' = k
  · subst hk'
    have h' := h
    rw [set_self] at h'
    exact self rfl (Option.some.inj h')
  · rw [set_ne _ _ _ _ hk'] at h
    exact other hk' h

end Assignment

/-! ## 2. Coherence: pairwise compossibility -/

/-- Pairwise compatibility of determinations.  Higher-order (Borromean)
constraints are declined: with those, locality would again be a
stipulation.  Binary compatibility is the weakest primitive from which
amalgamation of independent regions is a theorem. -/
structure Coherence (O : Ontology.{u,v}) where
  compat : O.Det → O.Det → Prop
  refl : ∀ d, compat d d
  symm : ∀ {d e}, compat d e → compat e d

namespace Coherence

variable {O : Ontology.{u,v}} (C : Coherence O)

def PairwiseOk (σ : Assignment O) : Prop :=
  ∀ k ℓ vk vl,
    σ k = some vk → σ ℓ = some vl →
      C.compat ⟨k, vk⟩ ⟨ℓ, vl⟩

theorem pairwise_down {σ τ : Assignment O}
    (h : C.PairwiseOk σ)
    (hsub : ∀ k v, τ k = some v → σ k = some v) :
    C.PairwiseOk τ :=
  fun k ℓ vk vl hk hl => h k ℓ vk vl (hsub k vk hk) (hsub ℓ vl hl)

theorem empty_ok : C.PairwiseOk Assignment.empty :=
  fun _ _ _ _ hk => by cases hk

/-- Two kinds are independent when every pair of values is compatible.
That is the spatial primitive: not a bag of locations, but the product
structure of the coherence complex. -/
def Independent (k ℓ : O.Kind) : Prop :=
  k ≠ ℓ ∧ ∀ (v : O.Value k) (w : O.Value ℓ), C.compat ⟨k, v⟩ ⟨ℓ, w⟩

theorem independent_symm {k ℓ : O.Kind} :
    C.Independent k ℓ → C.Independent ℓ k := by
  intro ⟨hne, hall⟩
  refine ⟨hne.symm, ?_⟩
  intro w v
  exact C.symm (hall v w)

def Interacts (k ℓ : O.Kind) : Prop :=
  k ≠ ℓ ∧ ¬ C.Independent k ℓ

/-- **Load-bearing locality.**  Independent coherent settlements amalgamate.
A change at `k` does not constrain `ℓ`, and the joint assignment is
admissible.  This is derived from compatibility, not stipulated as
"an act disturbs one kind". -/
theorem independent_amalgamate {k ℓ : O.Kind}
    (hI : C.Independent k ℓ)
    {σ : Assignment O} {v : O.Value k} {w : O.Value ℓ}
    (hσk : σ k = none) (_hσℓ : σ ℓ = none)
    (hk : C.PairwiseOk (Assignment.set σ k v))
    (hℓ : C.PairwiseOk (Assignment.set σ ℓ w)) :
    C.PairwiseOk (Assignment.set (Assignment.set σ k v) ℓ w) := by
  intro k1 k2 v1 v2 h1 h2
  have hσ : C.PairwiseOk σ :=
    C.pairwise_down hk (fun k' v' hs => by
      haveI := O.decEqKind
      by_cases hk' : k' = k
      · subst hk'
        rw [hσk] at hs
        cases hs
      · rw [Assignment.set_ne _ _ _ _ hk']
        exact hs)
  refine Assignment.realised_set_cases h1 ?_ ?_
  · intro eq1 heq1
    cases eq1
    cases heq1
    refine Assignment.realised_set_cases h2 ?_ ?_
    · intro eq2 heq2
      cases eq2
      cases heq2
      exact C.refl _
    · intro h2neL h2mid
      refine Assignment.realised_set_cases h2mid ?_ ?_
      · intro eqk heqk
        cases eqk
        cases heqk
        exact C.symm (hI.2 v w)
      · intro h2neK hs2
        have : Assignment.set σ ℓ w k2 = some v2 := by
          rwa [Assignment.set_ne _ _ _ _ h2neL]
        exact hℓ ℓ k2 w v2 (Assignment.set_self _ _ _) this
  · intro h1neL h1mid
    refine Assignment.realised_set_cases h1mid ?_ ?_
    · intro eqk heqk
      cases eqk
      cases heqk
      refine Assignment.realised_set_cases h2 ?_ ?_
      · intro eq2 heq2
        cases eq2
        cases heq2
        exact hI.2 v w
      · intro h2neL h2mid
        refine Assignment.realised_set_cases h2mid ?_ ?_
        · intro eqk2 heqk2
          cases eqk2
          cases heqk2
          exact C.refl _
        · intro h2neK hs2
          have : Assignment.set σ k v k2 = some v2 := by
            rwa [Assignment.set_ne _ _ _ _ h2neK]
          exact hk k k2 v v2 (Assignment.set_self _ _ _) this
    · intro h1neK hs1
      refine Assignment.realised_set_cases h2 ?_ ?_
      · intro eq2 heq2
        cases eq2
        cases heq2
        have : Assignment.set σ ℓ w k1 = some v1 := by
          rwa [Assignment.set_ne _ _ _ _ h1neL]
        exact hℓ k1 ℓ v1 w this (Assignment.set_self _ _ _)
      · intro h2neL h2mid
        refine Assignment.realised_set_cases h2mid ?_ ?_
        · intro eqk2 heqk2
          cases eqk2
          cases heqk2
          have : Assignment.set σ k v k1 = some v1 := by
            rwa [Assignment.set_ne _ _ _ _ h1neK]
          exact hk k1 k v1 v this (Assignment.set_self _ _ _)
        · intro h2neK hs2
          exact hσ k1 k2 v1 v2 hs1 hs2

/-- Independent updates commute as assignments *and* as admissible
configurations: the diamond is a theorem. -/
theorem independent_commute {k ℓ : O.Kind}
    (hI : C.Independent k ℓ)
    {σ : Assignment O} {v : O.Value k} {w : O.Value ℓ}
    (hσk : σ k = none) (hσℓ : σ ℓ = none)
    (hk : C.PairwiseOk (Assignment.set σ k v))
    (hℓ : C.PairwiseOk (Assignment.set σ ℓ w)) :
    Assignment.set (Assignment.set σ k v) ℓ w =
      Assignment.set (Assignment.set σ ℓ w) k v ∧
    C.PairwiseOk (Assignment.set (Assignment.set σ k v) ℓ w) :=
  ⟨Assignment.set_comm hI.1 v w,
    C.independent_amalgamate hI hσk hσℓ hk hℓ⟩

def Settable (σ : Assignment O) (k : O.Kind) (v : O.Value k) : Prop :=
  C.PairwiseOk (Assignment.set σ k v)

/-- Constraint-locality: settling an independent kind does not change
what remains settable at `ℓ`. -/
theorem independent_settable_iff {k ℓ : O.Kind}
    (hI : C.Independent k ℓ)
    {σ : Assignment O} {v : O.Value k} {w : O.Value ℓ}
    (hσk : σ k = none) (hσℓ : σ ℓ = none)
    (hk : C.Settable σ k v) :
    C.Settable σ ℓ w ↔ C.Settable (Assignment.set σ k v) ℓ w := by
  constructor
  · intro hℓ
    exact C.independent_amalgamate hI hσk hσℓ hk hℓ
  · intro hjoint
    exact C.pairwise_down hjoint (fun k' v' hs =>
      Assignment.realised_set_cases hs
        (fun eq heq => by
          cases eq
          cases heq
          exact Assignment.set_set_right v w)
        (fun hne hsσ => by
          haveI := O.decEqKind
          by_cases h'k : k' = k
          · subst h'k
            rw [hσk] at hsσ
            cases hsσ
          · rw [Assignment.set_set_other h'k hne v w]
            exact hsσ))

/-- A two-point assignment is admissible exactly when its one cross pair is
compatible. -/
theorem pairwise_pair {k ℓ : O.Kind} (v : O.Value k)
    (w : O.Value ℓ) (h : C.compat ⟨k, v⟩ ⟨ℓ, w⟩) :
    C.PairwiseOk (Assignment.set (Assignment.set Assignment.empty k v) ℓ w) := by
  intro k1 k2 v1 v2 h1 h2
  refine Assignment.realised_set_cases h1 ?_ ?_
  · intro e1 q1
    cases e1; cases q1
    refine Assignment.realised_set_cases h2 ?_ ?_
    · intro e2 q2; cases e2; cases q2; exact C.refl _
    · intro _ hm2
      refine Assignment.realised_set_cases hm2 ?_ ?_
      · intro e2 q2; cases e2; cases q2; exact C.symm h
      · intro _ hs2; cases hs2
  · intro _ hm1
    refine Assignment.realised_set_cases hm1 ?_ ?_
    · intro e1 q1
      cases e1; cases q1
      refine Assignment.realised_set_cases h2 ?_ ?_
      · intro e2 q2; cases e2; cases q2; exact h
      · intro _ hm2
        refine Assignment.realised_set_cases hm2 ?_ ?_
        · intro e2 q2; cases e2; cases q2; exact C.refl _
        · intro _ hs2; cases hs2
    · intro _ hs1; cases hs1

theorem settable_empty (k : O.Kind) (v : O.Value k) :
    C.Settable Assignment.empty k v := by
  intro k1 k2 v1 v2 h1 h2
  refine Assignment.realised_set_cases h1 ?_ ?_
  · intro eq1 heq1
    cases eq1
    cases heq1
    refine Assignment.realised_set_cases h2 ?_ ?_
    · intro eq2 heq2
      cases eq2
      cases heq2
      exact C.refl _
    · intro _ hs
      cases hs
  · intro _ hs
    cases hs

end Coherence

/-! ## 3. Configurations: admissible partial settlements

Articulation and assignment are two structures, not one.  Articulation
accumulates (the archive).  Values vary (oscillation).  The arrow of time
and the swirl therefore do not compete for the same relation.
-/

structure Config {O : Ontology.{u,v}} (C : Coherence O) where
  articulated : O.Kind → Prop
  assign : Assignment O
  realised_articulated : ∀ k v, assign k = some v → articulated k
  ok : C.PairwiseOk assign

namespace Config

variable {O : Ontology.{u,v}} {C : Coherence O}

def Open (s : Config C) (k : O.Kind) : Prop :=
  s.articulated k ∧ s.assign k = none

def Settled (s : Config C) (k : O.Kind) : Prop :=
  ∃ v, s.assign k = some v

def Undrawn (s : Config C) (k : O.Kind) : Prop :=
  ¬ s.articulated k

def Remainder (s : Config C) : Prop :=
  ∃ k, Open s k

def Null (s : Config C) : Prop :=
  ∀ k, s.assign k = none

def Settles (s t : Config C) (k : O.Kind) (v : O.Value k) : Prop :=
  Open s k ∧
    t.assign = Assignment.set s.assign k v ∧
    (∀ ℓ, t.articulated ℓ ↔ s.articulated ℓ)

def Grows (s t : Config C) : Prop :=
  (∀ k, s.articulated k → t.articulated k) ∧
    (∃ k, t.articulated k ∧ ¬ s.articulated k) ∧
    t.assign = s.assign

def Revises (s t : Config C) (k : O.Kind) (v : O.Value k) : Prop :=
  (∀ ℓ, t.articulated ℓ ↔ s.articulated ℓ) ∧
    t.assign = Assignment.set s.assign k v ∧
    ∃ w, s.assign k = some w ∧ w ≠ v

def settle (s : Config C) (k : O.Kind) (v : O.Value k)
    (ho : Open s k)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) : Config C where
  articulated := s.articulated
  assign := Assignment.set s.assign k v
  realised_articulated := by
    intro k' v' hv'
    haveI := O.decEqKind
    by_cases hk' : k' = k
    · subst hk'
      exact ho.1
    · rw [Assignment.set_ne s.assign k v k' hk'] at hv'
      exact s.realised_articulated k' v' hv'
  ok := hok

theorem settle_settles (s : Config C) (k : O.Kind) (v : O.Value k)
    (ho : Open s k)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) :
    Settles s (settle s k v ho hok) k v :=
  ⟨ho, rfl, fun _ => Iff.rfl⟩

/-- Revise a settled kind to a different value.  Articulation is untouched,
so this is the swirl and not the arrow. -/
def revise (s : Config C) (k : O.Kind) (v : O.Value k)
    (hset : ∃ w, s.assign k = some w ∧ w ≠ v)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) : Config C where
  articulated := s.articulated
  assign := Assignment.set s.assign k v
  realised_articulated := by
    intro k' v' hv'
    haveI := O.decEqKind
    by_cases hk' : k' = k
    · subst hk'
      obtain ⟨w, hw, _⟩ := hset
      exact s.realised_articulated k' w hw
    · rw [Assignment.set_ne s.assign k v k' hk'] at hv'
      exact s.realised_articulated k' v' hv'
  ok := hok

theorem revise_revises (s : Config C) (k : O.Kind) (v : O.Value k)
    (hset : ∃ w, s.assign k = some w ∧ w ≠ v)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) :
    Revises s (revise s k v hset hok) k v :=
  ⟨fun _ => Iff.rfl, rfl, hset⟩

/-! ### The arrow

Both moves that add something advance the archive: drawing a kind, and settling
an open one.  Revision adds nothing and so leaves the arrow untouched, which is
how oscillation and succession avoid competing for one relation. -/

/-- One configuration advances on another: nothing drawn is undrawn, nothing
settled is unsettled, and something is newly drawn or newly settled. -/
def Advances (s t : Config C) : Prop :=
  (∀ k, s.articulated k → t.articulated k) ∧
  (∀ k v, s.assign k = some v → t.assign k = some v) ∧
  (∃ k, (t.articulated k ∧ ¬ s.articulated k) ∨ (Settled t k ∧ ¬ Settled s k))

theorem advances_of_grows {s t : Config C} (h : Grows s t) : Advances s t := by
  obtain ⟨hart, ⟨k, hk, hnk⟩, hassign⟩ := h
  exact ⟨hart, fun k' v hv => by rw [hassign]; exact hv, ⟨k, Or.inl ⟨hk, hnk⟩⟩⟩

theorem advances_of_settles {s t : Config C} {k : O.Kind} {v : O.Value k}
    (h : Settles s t k v) : Advances s t := by
  obtain ⟨ho, hassign, hart⟩ := h
  refine ⟨fun ℓ hℓ => (hart ℓ).mpr hℓ, ?_, ⟨k, Or.inr ⟨?_, ?_⟩⟩⟩
  · intro ℓ w hw
    haveI := O.decEqKind
    by_cases hℓ : ℓ = k
    · subst hℓ; rw [ho.2] at hw; cases hw
    · rw [hassign, Assignment.set_ne _ _ _ _ hℓ]; exact hw
  · exact ⟨v, by rw [hassign]; exact Assignment.set_self _ _ _⟩
  · intro ⟨w, hw⟩; rw [ho.2] at hw; cases hw

theorem advances_trans {s t u : Config C}
    (h₁ : Advances s t) (h₂ : Advances t u) : Advances s u := by
  refine ⟨fun k hk => h₂.1 k (h₁.1 k hk), fun k v hv => h₂.2.1 k v (h₁.2.1 k v hv), ?_⟩
  obtain ⟨k, hk⟩ := h₁.2.2
  cases hk with
  | inl hd => exact ⟨k, Or.inl ⟨h₂.1 k hd.1, hd.2⟩⟩
  | inr hd =>
      obtain ⟨v, hv⟩ := hd.1
      exact ⟨k, Or.inr ⟨⟨v, h₂.2.1 k v hv⟩, hd.2⟩⟩

theorem advances_irrefl (s : Config C) : ¬ Advances s s := by
  intro h
  obtain ⟨k, hk⟩ := h.2.2
  cases hk with
  | inl hd => exact hd.2 hd.1
  | inr hd => exact hd.2 hd.1

/-- Time's arrow: the ancestral of drawing and settling.  Revision does not
enter this relation. -/
inductive Earlier : Config C → Config C → Prop
  | draw {s t} : Grows s t → Earlier s t
  | settle {s t k v} : Settles s t k v → Earlier s t
  | trans {s t u} : Earlier s t → Earlier t u → Earlier s u

theorem earlier_advances {s t : Config C} (h : Earlier s t) : Advances s t := by
  induction h with
  | draw hg => exact advances_of_grows hg
  | settle hs => exact advances_of_settles hs
  | trans _ _ ih₁ ih₂ => exact advances_trans ih₁ ih₂

/-- **No return.**  Nothing is ever earlier than itself. -/
theorem earlier_irrefl (s : Config C) : ¬ Earlier s s :=
  fun h => advances_irrefl s (earlier_advances h)

theorem earlier_asymm {s t : Config C} (h : Earlier s t) : ¬ Earlier t s :=
  fun h' => earlier_irrefl s (Earlier.trans h h')

/-- Settling now moves the archive.  Under the previous definition, in which
only drawing counted, a settlement and its result were unordered in both
directions, and everything that happened to values happened outside time. -/
theorem settles_earlier {s t : Config C} {k : O.Kind} {v : O.Value k}
    (h : Settles s t k v) : Earlier s t := Earlier.settle h

/-- **Oscillation does not compete with the arrow.**  A revision draws nothing
and settles nothing that was open, so it is no advance, in either direction. -/
theorem revises_not_advances {s t : Config C} {k : O.Kind} {v : O.Value k}
    (h : Revises s t k v) : ¬ Advances s t ∧ ¬ Advances t s := by
  obtain ⟨hart, hassign, w, hw, hne⟩ := h
  have hts : ∀ ℓ, Settled t ℓ ↔ Settled s ℓ := by
    intro ℓ
    haveI := O.decEqKind
    by_cases hℓ : ℓ = k
    · subst hℓ
      exact ⟨fun _ => ⟨w, hw⟩,
        fun _ => ⟨v, by rw [hassign]; exact Assignment.set_self _ _ _⟩⟩
    · constructor
      · intro ⟨u, hu⟩
        rw [hassign, Assignment.set_ne _ _ _ _ hℓ] at hu
        exact ⟨u, hu⟩
      · intro ⟨u, hu⟩
        exact ⟨u, by rw [hassign, Assignment.set_ne _ _ _ _ hℓ]; exact hu⟩
  constructor
  · intro ha
    obtain ⟨ℓ, hl⟩ := ha.2.2
    cases hl with
    | inl hd => exact hd.2 ((hart ℓ).mp hd.1)
    | inr hd => exact hd.2 ((hts ℓ).mp hd.1)
  · intro ha
    obtain ⟨ℓ, hl⟩ := ha.2.2
    cases hl with
    | inl hd => exact hd.2 ((hart ℓ).mpr hd.1)
    | inr hd => exact hd.2 ((hts ℓ).mpr hd.1)

end Config

/-! ## 4. Possibility: the one existential -/

/-- A coherent configuration need not have a successor.  The inert
passage relation is empty; seriality is not a coherence-level fact. -/
def InertPossible {O : Ontology.{u,v}} {C : Coherence O} :
    Config C → Config C → Prop :=
  fun _ _ => False

theorem inert_not_serial {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) :
    ¬ ∃ t, InertPossible (C := C) s t :=
  fun ⟨_, h⟩ => h

theorem productivity_is_not_coherence_level {O : Ontology.{u,v}}
    {C : Coherence O} (s : Config C) :
    ¬ (∀ p : Config C, ∃ t, InertPossible (C := C) p t) :=
  fun h => inert_not_serial s (h s)

/-- Plenitude at an open kind: every pairwise-ok value is realised as a
settle.  The configuration `settle` constructs the witness; plenitude is
the decision to count every such witness as possible. -/
def PlenitudeAt {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) : Prop :=
  s.Open k ∧ ∀ v, C.Settable s.assign k v →
    ∃ t, Config.Settles s t k v

theorem plenitudeAt_of_open {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) (ho : s.Open k) :
    PlenitudeAt s k :=
  ⟨ho, fun v hok => ⟨s.settle k v ho hok, s.settle_settles k v ho hok⟩⟩

structure Selector (O : Ontology.{u,v}) where
  choose : (k : O.Kind) → O.Value k

def RespectsSettles {O : Ontology.{u,v}} (C : Coherence O)
    (sel : Selector O) : Prop :=
  ∀ {s t : Config C} {k v}, Config.Settles s t k v → v = sel.choose k

theorem plenitude_exceeds_selector {O : Ontology.{u,v}} {C : Coherence O}
    {s : Config C} {k : O.Kind}
    (hP : PlenitudeAt s k)
    {v w : O.Value k} (hne : v ≠ w)
    (hv : C.Settable s.assign k v)
    (hw : C.Settable s.assign k w)
    (sel : Selector O) :
    ¬ RespectsSettles (C := C) sel := by
  intro hres
  obtain ⟨t, ht⟩ := hP.2 v hv
  obtain ⟨t', ht'⟩ := hP.2 w hw
  exact hne ((hres ht).trans (hres ht').symm)

/-! ## 4b. Forcing: how far coherence determines what is settled

The one thing coherence can do about actualisation is narrow it.  Where what
has already been settled leaves exactly one admissible value at an open kind,
that kind is *forced*, and nothing further is needed to say what happens there.
Where two values remain, the kind is *free*.

Two results below, and together they are a dichotomy.

* At a forced kind, any respected selection is pinned to the forced value:
  the coherence structure has already decided, and the selector merely records
  it (`forced_pins_selector`).
* At a free kind, no selection function is respected at all — and not merely no
  *uniform* one.  Plenitude supplies two settlements from the very same
  configuration, so even a policy reading the whole configuration is refuted
  (`free_refutes_policy`).

Hence `selection_is_redundant_or_refuted`: if a selection is respected anywhere
that anything is settleable, that place was forced already.  A gradient is
never doing independent work.  Actualisation is determined exactly as far as
coherence forces it, and the residue is provably not fillable by any function
of the configuration. -/

namespace Forcing

open Config

variable {O : Ontology.{u,v}} {C : Coherence O}

/-- Exactly one value remains admissible here. -/
def Forced (s : Config C) (k : O.Kind) (v : O.Value k) : Prop :=
  s.Open k ∧ C.Settable s.assign k v ∧
    ∀ w, C.Settable s.assign k w → w = v

/-- Two or more remain. -/
def Free (s : Config C) (k : O.Kind) : Prop :=
  s.Open k ∧ ∃ v w, v ≠ w ∧
    C.Settable s.assign k v ∧ C.Settable s.assign k w

theorem forced_not_free {s : Config C} {k : O.Kind} {v : O.Value k}
    (hF : Forced s k v) : ¬ Free s k := by
  intro ⟨_, x, y, hne, hx, hy⟩
  exact hne ((hF.2.2 x hx).trans (hF.2.2 y hy).symm)

/-- A forced kind can be settled, and only one way. -/
theorem forced_settles {s : Config C} {k : O.Kind} {v : O.Value k}
    (hF : Forced s k v) :
    (∃ t, Settles s t k v) ∧ ∀ w, (∃ t, Settles s t k w) → w = v := by
  refine ⟨(plenitudeAt_of_open s k hF.1).2 v hF.2.1, ?_⟩
  intro w ⟨t, ht⟩
  refine hF.2.2 w ?_
  have hw : C.PairwiseOk (Assignment.set s.assign k w) := by
    rw [← ht.2.1]; exact t.ok
  exact hw

/-- **Where coherence forces, selection is redundant.**  A respected selector
must choose the value the constraints had already left. -/
theorem forced_pins_selector {s : Config C} {k : O.Kind} {v : O.Value k}
    (hF : Forced s k v) (sel : Selector O)
    (hres : RespectsSettles C sel) : sel.choose k = v := by
  obtain ⟨t, ht⟩ := (plenitudeAt_of_open s k hF.1).2 v hF.2.1
  exact (hres ht).symm

/-- A selection function allowed to read the whole configuration, not merely
the kind.  This is the uniform gradient's natural strengthening. -/
structure Policy (C : Coherence O) where
  choose : Config C → (k : O.Kind) → O.Value k

def RespectsPolicy (pol : Policy C) : Prop :=
  ∀ {s t : Config C} {k v}, Settles s t k v → v = pol.choose s k

/-- **Where coherence does not force, no selection survives.**  Plenitude
supplies two settlements from the same configuration, so configuration
dependence buys nothing: the policy is evaluated at the same `s` both times. -/
theorem free_refutes_policy {s : Config C} {k : O.Kind}
    (hFree : Free s k) (pol : Policy C) : ¬ RespectsPolicy pol := by
  intro hres
  obtain ⟨ho, v, w, hne, hv, hw⟩ := hFree
  obtain ⟨t, ht⟩ := (plenitudeAt_of_open s k ho).2 v hv
  obtain ⟨t', ht'⟩ := (plenitudeAt_of_open s k ho).2 w hw
  exact hne ((hres ht).trans (hres ht').symm)

theorem free_refutes_selector {s : Config C} {k : O.Kind}
    (hFree : Free s k) (sel : Selector O) : ¬ RespectsSettles C sel := by
  intro hres
  obtain ⟨ho, v, w, hne, hv, hw⟩ := hFree
  obtain ⟨t, ht⟩ := (plenitudeAt_of_open s k ho).2 v hv
  obtain ⟨t', ht'⟩ := (plenitudeAt_of_open s k ho).2 w hw
  exact hne ((hres ht).trans (hres ht').symm)

/-- **The dichotomy.**  If a selection is respected, then wherever anything is
settleable at an open kind, that kind was forced and the selection is pinned to
what coherence left.  Selection is therefore never an independent posit: it is
either implied by the constraints or refuted by plenitude. -/
theorem selection_is_redundant_or_refuted {s : Config C} {k : O.Kind}
    {v : O.Value k} (ho : s.Open k) (hv : C.Settable s.assign k v)
    (sel : Selector O) (hres : RespectsSettles C sel) :
    Forced s k v ∧ sel.choose k = v := by
  have hforced : Forced s k v := by
    refine ⟨ho, hv, ?_⟩
    intro w hw
    obtain ⟨t, ht⟩ := (plenitudeAt_of_open s k ho).2 v hv
    obtain ⟨t', ht'⟩ := (plenitudeAt_of_open s k ho).2 w hw
    exact (hres ht').trans (hres ht).symm
  exact ⟨hforced, forced_pins_selector hforced sel hres⟩

end Forcing

/-! ## 5. Observation as restricted access

A region is a predicate on kinds.  The restriction of a configuration to a
region is a sub-configuration.  That is veridical access, not consciousness.
Illusion is a further primitive and is not derived from restriction.
-/

def Region (O : Ontology.{u,v}) := O.Kind → Bool

def restrict {O : Ontology.{u,v}} (σ : Assignment O) (r : Region O) :
    Assignment O :=
  fun k => if r k then σ k else none

theorem restrict_sub {O : Ontology.{u,v}} {C : Coherence O}
    {σ : Assignment O} (h : C.PairwiseOk σ) (r : Region O) :
    C.PairwiseOk (restrict σ r) :=
  C.pairwise_down h (fun k v hv => by
    unfold restrict at hv
    split at hv
    · exact hv
    · cases hv)

theorem restrict_agrees {O : Ontology.{u,v}}
    (σ : Assignment O) (r : Region O) (k : O.Kind) (hr : r k = true) :
    restrict σ r k = σ k := by
  unfold restrict
  rw [hr]
  rfl

/-! ## 5b. What pairwise coherence buys

`independent_amalgamate` is the load-bearing theorem, and it is worth being
exact about why it holds.  Admissibility here is generated by pairs, so a joint
settlement is admissible as soon as every pair in it is, and independent
settlements amalgamate almost by construction.

The question is therefore whether pairwise generation is a real restriction.
It is.  Below, a downward-closed admissibility that is not pairwise-generated,
in which two kinds are pairwise compatible on every pair of values and their
settlements nevertheless fail to amalgamate over a third.  A Borromean triple
does it: any two of the three hold together, all three do not.

So the honest form of the claim is not "locality is derived" but **locality is
equivalent to coherence being pairwise**.  That is a thesis, and it is
falsifiable: a world with irreducibly three-way constraints has no locality in
this sense, and no amount of care about acts would restore it. -/

/-- Admissibility in general: any downward-closed condition on assignments. -/
structure Admissibility (O : Ontology.{u,v}) where
  Adm : Assignment O → Prop
  down : ∀ {σ τ : Assignment O},
    (∀ k v, τ k = some v → σ k = some v) → Adm σ → Adm τ

/-- Pairwise coherence induces one. -/
def Coherence.toAdmissibility {O : Ontology.{u,v}} (C : Coherence O) :
    Admissibility O where
  Adm := C.PairwiseOk
  down := fun hsub h => C.pairwise_down h hsub

namespace Borromean

inductive K where
  | a | b | c
  deriving DecidableEq

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := fun _ => Bool
  decEqKind := inferInstance

/-- Any two of the three may be settled positively; all three may not. -/
abbrev adm : Admissibility ont where
  Adm := fun σ => ¬ (σ K.a = some true ∧ σ K.b = some true ∧ σ K.c = some true)
  down := by
    intro σ τ hsub h hbad
    exact h ⟨hsub K.a true hbad.1, hsub K.b true hbad.2.1,
      hsub K.c true hbad.2.2⟩

open Assignment

/-- `a` and `b` are compatible on every pair of values, taken by themselves. -/
theorem pairwise_independent (v w : Bool) :
    adm.Adm (set (set (empty : Assignment ont) K.a v) K.b w) := by
  intro hbad
  have hc : set (set (empty : Assignment ont) K.a v) K.b w K.c = none := by
    rw [set_ne _ _ _ _ (by decide : K.c ≠ K.b),
      set_ne _ _ _ _ (by decide : K.c ≠ K.a)]
    rfl
  rw [hc] at hbad
  exact Option.noConfusion hbad.2.2

/-- A third kind already settled. -/
def σ : Assignment ont := set empty K.c true

theorem a_settleable : adm.Adm (set σ K.a true) := by
  intro hbad
  have hb : set σ K.a true K.b = none := by
    rw [set_ne _ _ _ _ (by decide : K.b ≠ K.a)]
    show set (empty : Assignment ont) K.c true K.b = none
    rw [set_ne _ _ _ _ (by decide : K.b ≠ K.c)]
    rfl
  rw [hb] at hbad
  exact Option.noConfusion hbad.2.1

theorem b_settleable : adm.Adm (set σ K.b true) := by
  intro hbad
  have ha : set σ K.b true K.a = none := by
    rw [set_ne _ _ _ _ (by decide : K.a ≠ K.b)]
    show set (empty : Assignment ont) K.c true K.a = none
    rw [set_ne _ _ _ _ (by decide : K.a ≠ K.c)]
    rfl
  rw [ha] at hbad
  exact Option.noConfusion hbad.1

theorem no_amalgamation :
    ¬ adm.Adm (set (set σ K.a true) K.b true) := by
  intro hgood
  refine hgood ⟨?_, ?_, ?_⟩
  · rw [set_ne _ _ _ _ (by decide : K.a ≠ K.b)]
    exact set_self _ _ _
  · exact set_self _ _ _
  · rw [set_ne _ _ _ _ (by decide : K.c ≠ K.b),
      set_ne _ _ _ _ (by decide : K.c ≠ K.a)]
    exact set_self _ _ _

end Borromean

/-- **Locality is exactly pairwise coherence.**  Where admissibility is not
generated by pairs, two kinds can be compatible on every pair of values, each
separately settleable, and still fail to amalgamate.  So the amalgamation
theorem is not a free lunch: it is the content of taking compossibility to be
pairwise. -/
theorem locality_needs_pairwise :
    ∃ (O : Ontology.{0,0}) (A : Admissibility O) (a b : O.Kind)
      (va : O.Value a) (vb : O.Value b) (σ : Assignment O),
      (∀ (v : O.Value a) (w : O.Value b),
        A.Adm (Assignment.set (Assignment.set Assignment.empty a v) b w)) ∧
      A.Adm (Assignment.set σ a va) ∧
      A.Adm (Assignment.set σ b vb) ∧
      ¬ A.Adm (Assignment.set (Assignment.set σ a va) b vb) :=
  ⟨Borromean.ont, Borromean.adm, Borromean.K.a, Borromean.K.b, true, true,
    Borromean.σ, Borromean.pairwise_independent, Borromean.a_settleable,
    Borromean.b_settleable, Borromean.no_amalgamation⟩

/-! ## 6. The void -/

namespace Void

inductive K where
  | star
  deriving DecidableEq

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := fun _ => Bool
  decEqKind := inferInstance

def compat : ont.Det → ont.Det → Prop
  | ⟨.star, a⟩, ⟨.star, b⟩ => a = b

abbrev coh : Coherence ont where
  compat := compat
  refl := by intro d; cases d with | mk k v => cases k; exact rfl
  symm := by
    intro d e h
    cases d with | mk k₁ v₁ =>
    cases e with | mk k₂ v₂ =>
    cases k₁; cases k₂
    exact h.symm

def emptyCfg : Config coh where
  articulated := fun _ => True
  assign := Assignment.empty
  realised_articulated := fun _ _ h => by cases h
  ok := coh.empty_ok

theorem null : emptyCfg.Null := fun _ => rfl

theorem remainder : emptyCfg.Remainder :=
  ⟨K.star, trivial, rfl⟩

theorem nullity_coherent : emptyCfg.Null ∧ emptyCfg.Remainder :=
  ⟨null, remainder⟩

end Void

theorem nullity_not_derivable :
    ∃ (O : Ontology.{0,0}) (C : Coherence O) (s : Config C),
      s.Null ∧ s.Remainder :=
  ⟨Void.ont, Void.coh, Void.emptyCfg, Void.nullity_coherent⟩

/-! ## 7. A world: independence, interaction, amalgamation -/

namespace World

inductive K where
  | sw | lamp | hue | gap
  deriving DecidableEq

inductive Hue where
  | red | green | blue
  deriving DecidableEq

def Val : K → Type
  | .sw => Bool
  | .lamp => Bool
  | .hue => Hue
  | .gap => Bool

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := Val
  decEqKind := inferInstance

def compat (d e : ont.Det) : Prop :=
  match d.kind, e.kind, d.value, e.value with
  | .sw, .sw, a, b => a = b
  | .lamp, .lamp, a, b => a = b
  | .hue, .hue, a, b => a = b
  | .gap, .gap, a, b => a = b
  | .sw, .lamp, a, b => ¬ (a = false ∧ b = true)
  | .lamp, .sw, a, b => ¬ (b = false ∧ a = true)
  | .sw, .hue, _, _ => True
  | .hue, .sw, _, _ => True
  | .sw, .gap, _, _ => True
  | .gap, .sw, _, _ => True
  | .lamp, .hue, _, _ => True
  | .hue, .lamp, _, _ => True
  | .lamp, .gap, _, _ => True
  | .gap, .lamp, _, _ => True
  | .hue, .gap, _, _ => True
  | .gap, .hue, _, _ => True

abbrev coh : Coherence ont where
  compat := compat
  refl := by
    intro d
    cases d with | mk k v =>
    cases k <;> exact rfl
  symm := by
    intro d e h
    cases d with | mk k₁ v₁ =>
    cases e with | mk k₂ v₂ =>
    cases k₁ <;> cases k₂ <;> first | exact h.symm | exact h

def vacant : Assignment ont := Assignment.empty

def allArt : K → Prop := fun _ => True

def origin : Config coh where
  articulated := allArt
  assign := vacant
  realised_articulated := fun _ _ h => by cases h
  ok := coh.empty_ok

theorem origin_open (k : K) : origin.Open k :=
  ⟨trivial, rfl⟩

theorem independent_hue_sw : coh.Independent K.hue K.sw := by
  constructor
  · intro h; cases h
  · intro _ _; exact trivial

theorem independent_hue_lamp : coh.Independent K.hue K.lamp := by
  constructor
  · intro h; cases h
  · intro _ _; exact trivial

theorem not_independent_sw_lamp : ¬ coh.Independent K.sw K.lamp := by
  intro ⟨_, hall⟩
  have : compat ⟨K.sw, false⟩ ⟨K.lamp, true⟩ := hall false true
  exact this ⟨rfl, rfl⟩

/-- Adjacency: switch and lamp interact, hue is elsewhere. -/
theorem sw_interacts_lamp : coh.Interacts K.sw K.lamp :=
  ⟨by decide, not_independent_sw_lamp⟩

theorem hue_not_interacts_sw : ¬ coh.Interacts K.hue K.sw :=
  fun h => h.2 independent_hue_sw

theorem settable_sw_off : coh.Settable vacant K.sw false :=
  coh.settable_empty K.sw false

theorem settable_lamp_on : coh.Settable vacant K.lamp true :=
  coh.settable_empty K.lamp true

theorem settable_hue (h : Hue) : coh.Settable vacant K.hue h :=
  coh.settable_empty K.hue h

theorem hue_sw_amalgamate :
    coh.PairwiseOk
      (Assignment.set (Assignment.set vacant K.hue Hue.red) K.sw true) :=
  coh.independent_amalgamate independent_hue_sw rfl rfl
    (settable_hue Hue.red) (coh.settable_empty K.sw true)

theorem hue_sw_diamond :
    Assignment.set (Assignment.set vacant K.hue Hue.red) K.sw true =
      Assignment.set (Assignment.set vacant K.sw true) K.hue Hue.red ∧
    coh.PairwiseOk
      (Assignment.set (Assignment.set vacant K.hue Hue.red) K.sw true) :=
  coh.independent_commute independent_hue_sw rfl rfl
    (settable_hue Hue.red) (coh.settable_empty K.sw true)

theorem sw_lamp_refuse :
    ¬ coh.PairwiseOk
      (Assignment.set (Assignment.set vacant K.sw false) K.lamp true) := by
  intro h
  have hs :
      Assignment.set (Assignment.set vacant K.sw false) K.lamp true K.sw =
        some false := by
    rw [Assignment.set_ne (Assignment.set vacant K.sw false) K.lamp true K.sw
      (by decide)]
    exact Assignment.set_self vacant K.sw false
  have hl :
      Assignment.set (Assignment.set vacant K.sw false) K.lamp true K.lamp =
        some true :=
    Assignment.set_self _ _ _
  have : compat ⟨K.sw, false⟩ ⟨K.lamp, true⟩ :=
    h K.sw K.lamp false true hs hl
  exact this ⟨rfl, rfl⟩

/-- Interaction, not independence: each settlement is admissible, the
joint is not.  Space here is a constraint, not a bag of locations. -/
theorem interaction_blocks_amalgamation :
    coh.Settable vacant K.sw false ∧
      coh.Settable vacant K.lamp true ∧
      ¬ coh.PairwiseOk
        (Assignment.set (Assignment.set vacant K.sw false) K.lamp true) :=
  ⟨settable_sw_off, settable_lamp_on, sw_lamp_refuse⟩

/-! ### Does constraint propagation actually determine anything? -/

theorem red_ne_green : Hue.red ≠ Hue.green := fun h => Hue.noConfusion h

/-- Settle the lamp on. -/
def lampOn : Config coh :=
  origin.settle K.lamp true (origin_open K.lamp) settable_lamp_on

theorem lampOn_assign : lampOn.assign = Assignment.set vacant K.lamp true := rfl

theorem sw_open_at_lampOn : lampOn.Open K.sw := by
  refine ⟨trivial, ?_⟩
  show Assignment.set vacant K.lamp true K.sw = none
  rw [Assignment.set_ne _ _ _ _ (by decide : K.sw ≠ K.lamp)]
  rfl

theorem sw_true_settleable : coh.Settable lampOn.assign K.sw true :=
  coh.pairwise_pair (k := K.lamp) (ℓ := K.sw) true true (by
    show ¬ (true = false ∧ true = true)
    intro h; exact Bool.noConfusion h.1)

theorem sw_false_not_settleable : ¬ coh.Settable lampOn.assign K.sw false := by
  intro h
  have hl : Assignment.set lampOn.assign K.sw false K.lamp = some true := by
    rw [Assignment.set_ne _ _ _ _ (by decide : K.lamp ≠ K.sw)]
    exact Assignment.set_self vacant K.lamp true
  have hs : Assignment.set lampOn.assign K.sw false K.sw = some false :=
    Assignment.set_self _ _ _
  have : compat ⟨K.lamp, true⟩ ⟨K.sw, false⟩ := h K.lamp K.sw true false hl hs
  exact this ⟨rfl, rfl⟩

/-- **Constraint propagation determines a value.**  With the lamp on, the
switch is forced: only one setting of it remains admissible, and nothing
outside the coherence structure was consulted. -/
theorem sw_forced_by_lamp : Forcing.Forced lampOn K.sw true := by
  refine ⟨sw_open_at_lampOn, sw_true_settleable, ?_⟩
  intro w hw
  cases w with
  | true => rfl
  | false => exact absurd hw sw_false_not_settleable

/-- The forced value is the only one that can be settled there. -/
theorem sw_settles_only_true :
    (∃ t, Config.Settles lampOn t K.sw true) ∧
      ∀ w, (∃ t, Config.Settles lampOn t K.sw w) → w = true :=
  Forcing.forced_settles sw_forced_by_lamp

/-- **And the boundary.**  Nothing forces the hue at the origin: three values
remain, so the constraint structure says nothing about which is settled, and by
the dichotomy no selection function can be respected there either. -/
theorem hue_free_at_origin : Forcing.Free origin K.hue :=
  ⟨origin_open K.hue, Hue.red, Hue.green, red_ne_green,
    settable_hue Hue.red, settable_hue Hue.green⟩

theorem no_policy_at_hue (pol : Forcing.Policy coh) :
    ¬ Forcing.RespectsPolicy pol :=
  Forcing.free_refutes_policy hue_free_at_origin pol

def seen : Region ont
  | .hue => true
  | .lamp => true
  | .sw => false
  | .gap => false

theorem restrict_origin_ok :
    coh.PairwiseOk (restrict origin.assign seen) :=
  restrict_sub origin.ok seen

theorem plenitude_hue : PlenitudeAt origin K.hue :=
  plenitudeAt_of_open origin K.hue (origin_open K.hue)

def sel : Selector ont where
  choose := fun k =>
    match k with
    | .sw => true
    | .lamp => true
    | .hue => Hue.red
    | .gap => false

theorem exceeds :
    ¬ RespectsSettles (C := coh) sel :=
  plenitude_exceeds_selector plenitude_hue
    (show Hue.red ≠ Hue.green from fun h => nomatch h)
    (settable_hue Hue.red) (settable_hue Hue.green) sel

/-- Settling the hue at the origin. -/
def hueRed : Config coh :=
  origin.settle K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red)

theorem hue_settled : hueRed.assign K.hue = some Hue.red :=
  Assignment.set_self vacant K.hue Hue.red

theorem hue_revisable :
    coh.PairwiseOk (Assignment.set hueRed.assign K.hue Hue.green) := by
  show coh.PairwiseOk
    (Assignment.set (Assignment.set vacant K.hue Hue.red) K.hue Hue.green)
  rw [Assignment.set_set_same]
  exact settable_hue Hue.green

/-- **Oscillation.**  The hue is revised from red to green: articulation is
untouched, the value changes, and the arrow is indifferent in both directions.
Succession and the swirl no longer compete for one relation. -/
theorem hue_oscillates :
    Config.Revises hueRed
      (hueRed.revise K.hue Hue.green ⟨Hue.red, hue_settled, red_ne_green⟩
        hue_revisable) K.hue Hue.green ∧
    ¬ Config.Advances hueRed
      (hueRed.revise K.hue Hue.green ⟨Hue.red, hue_settled, red_ne_green⟩
        hue_revisable) := by
  refine ⟨hueRed.revise_revises K.hue Hue.green ⟨Hue.red, hue_settled, red_ne_green⟩
    hue_revisable, ?_⟩
  exact (Config.revises_not_advances (hueRed.revise_revises K.hue Hue.green
    ⟨Hue.red, hue_settled, red_ne_green⟩ hue_revisable)).1

/-- And settling does move the archive, which it did not before. -/
theorem settling_advances : Config.Earlier origin hueRed :=
  Config.settles_earlier
    (origin.settle_settles K.hue Hue.red (origin_open K.hue)
      (settable_hue Hue.red))

def seed : Config coh where
  articulated := fun k => k = K.gap
  assign := vacant
  realised_articulated := fun _ _ h => by cases h
  ok := coh.empty_ok

theorem seed_grows_origin : Config.Grows seed origin := by
  refine ⟨fun _ _ => trivial, ⟨K.hue, trivial, ?_⟩, rfl⟩
  intro h
  cases h

theorem earlier_seed_origin : Config.Earlier seed origin :=
  Config.Earlier.draw seed_grows_origin

end World

/-! ## Axiom regression -/

/--
info: 'OpenSite.Forcing.selection_is_redundant_or_refuted' does not depend on any axioms
-/
#guard_msgs in
#print axioms Forcing.selection_is_redundant_or_refuted

/--
info: 'OpenSite.World.sw_forced_by_lamp' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.sw_forced_by_lamp


/--
info: 'OpenSite.World.hue_sw_diamond' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms World.hue_sw_diamond

/--
info: 'OpenSite.World.interaction_blocks_amalgamation' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.interaction_blocks_amalgamation

/--
info: 'OpenSite.World.exceeds' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.exceeds

/--
info: 'OpenSite.productivity_is_not_coherence_level' does not depend on any axioms
-/
#guard_msgs in
#print axioms productivity_is_not_coherence_level

/--
info: 'OpenSite.locality_needs_pairwise' does not depend on any axioms
-/
#guard_msgs in
#print axioms locality_needs_pairwise

/--
info: 'OpenSite.Config.earlier_irrefl' does not depend on any axioms
-/
#guard_msgs in
#print axioms Config.earlier_irrefl

/--
info: 'OpenSite.World.hue_oscillates' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms World.hue_oscillates

/--
info: 'OpenSite.World.settling_advances' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.settling_advances

end OpenSite
