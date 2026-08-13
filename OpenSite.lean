import Init

/-!
# Open Sites, from compossibility

The first draft of this file still took a *step* as primitive.  A step is
already ordinal, so time came almost free and extension had nowhere to
come from: `Continues.persists` stipulated that an act disturbs one kind,
and `Coexistence` was bolted on as a second relation between sites.  That
is the same square peg as seed, cadence, and offer.

**Start from which determinations can be settled together.**  A field of
kinds plus a coherence structure of pairwise compatibility.  Configurations
are admissible partial settlements.  Everything else is defined from that.

| Target | Completes as | Out of scope |
| --- | --- | --- |
| Latency | settled for, settled against, or unset | powers, degrees |
| Space | independence / interaction in the coherence structure | dimension, metric, signature |
| Locality | independent settlements amalgamate | a stipulated one-kind act |
| Time | chains of *articulative* growth | metric or lived duration |
| Oscillation | revision of a value at fixed articulation | competing with the arrow |
| Possibility | the one existential: every coherent settle/revise | possible worlds |
| Observation | restriction to a region of kinds | consciousness; illusion is extra |
| Concurrency | commuting updates on independent kinds | relativistic spacetime |

What is absorbed from the sequential diagnosis: unlabelled (now un-n-ary)
kinds, plenitude as the unique existential, internal articulation from the
start, and the impossibility results as design constraints.  What is
rejected: reverting to a binary-only field; identifying observation with
restriction so tightly that illusion becomes inexpressible; claiming
dimension or metric.

The load-bearing claim, tested below: **locality is a theorem.**  If two
kinds are independent, coherent settlements of each amalgamate to a
coherent joint settlement, and the two orders of update agree.
Remainder and independence are not theorems of having a coherence:
countermodels `Closed` and `Locked` show each can fail.
-/

namespace OpenSite

universe u v

/-! ## 0. Ontology: kinds as types of values -/

structure Ontology where
  Kind : Type u
  Value : Kind → Type v
  Exclusive : Kind → Prop
  decEqKind : DecidableEq Kind

namespace Ontology

variable (O : Ontology.{u,v})

structure Det where
  kind : O.Kind
  value : O.Value kind

def Dichotomous (k : O.Kind) : Prop :=
  ∃ a b : O.Value k, a ≠ b ∧ ∀ c, c = a ∨ c = b

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

theorem set_set_other {σ : Assignment O} {k ℓ k' : O.Kind}
    (hk : k' ≠ k) (hℓ : k' ≠ ℓ) (v : O.Value k) (w : O.Value ℓ) :
    set (set σ k v) ℓ w k' = σ k' := by
  rw [set_ne _ _ _ _ hℓ, set_ne _ _ _ _ hk]

theorem set_overwrite (σ : Assignment O) (k : O.Kind)
    (v w : O.Value k) :
    set (set σ k v) k w = set σ k w := by
  funext k'
  haveI := O.decEqKind
  by_cases hk : k' = k
  · subst hk
    rw [set_self, set_self]
  · rw [set_ne _ _ _ _ hk, set_ne _ _ _ _ hk, set_ne _ _ _ _ hk]

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
  exclusive_incompat :
    ∀ {k v w}, O.Exclusive k → v ≠ w →
      ¬ compat ⟨k, v⟩ ⟨k, w⟩

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

/-- Overwriting a cell is replacement, not joint realisation. -/
theorem settable_overwrite {σ : Assignment O} {k : O.Kind}
    {v w : O.Value k} (h : C.Settable σ k w) :
    C.Settable (Assignment.set σ k v) k w := by
  have e := Assignment.set_overwrite σ k v w
  intro k1 k2 v1 v2 h1 h2
  rw [e] at h1 h2
  exact h k1 k2 v1 v2 h1 h2

/-- Three pairwise-independent settlements amalgamate.  Finite-region
locality, from the binary theorem, not a new primitive. -/
theorem independent_amalgamate3 {k ℓ m : O.Kind}
    (hkl : C.Independent k ℓ)
    (hkm : C.Independent k m)
    (hlm : C.Independent ℓ m)
    {σ : Assignment O}
    {v : O.Value k} {w : O.Value ℓ} {u : O.Value m}
    (hσk : σ k = none) (hσℓ : σ ℓ = none) (hσm : σ m = none)
    (hk : C.Settable σ k v)
    (hℓ : C.Settable σ ℓ w)
    (hm : C.Settable σ m u) :
    C.PairwiseOk
      (Assignment.set (Assignment.set (Assignment.set σ k v) ℓ w) m u) := by
  have hσℓ' : Assignment.set σ k v ℓ = none := by
    rw [Assignment.set_ne _ _ _ _ hkl.1.symm]
    exact hσℓ
  have hσm' : Assignment.set σ k v m = none := by
    rw [Assignment.set_ne _ _ _ _ hkm.1.symm]
    exact hσm
  have hℓ' : C.Settable (Assignment.set σ k v) ℓ w :=
    (C.independent_settable_iff hkl hσk hσℓ hk).mp hℓ
  have hm' : C.Settable (Assignment.set σ k v) m u :=
    (C.independent_settable_iff hkm hσk hσm hk).mp hm
  exact C.independent_amalgamate hlm hσℓ' hσm' hℓ' hm'

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

def Excluded (s : Config C) (k : O.Kind) (v : O.Value k) : Prop :=
  ∃ w, s.assign k = some w ∧ w ≠ v

theorem settled_not_open {s : Config C} {k : O.Kind}
    (h : Settled s k) : ¬ Open s k := by
  intro ⟨_, hnone⟩
  obtain ⟨v, hv⟩ := h
  rw [hv] at hnone
  cases hnone

theorem settled_not_undrawn {s : Config C} {k : O.Kind}
    (h : Settled s k) : ¬ Undrawn s k := by
  intro hund
  obtain ⟨v, hv⟩ := h
  exact hund (s.realised_articulated k v hv)

theorem open_not_undrawn {s : Config C} {k : O.Kind}
    (h : Open s k) : ¬ Undrawn s k :=
  fun hund => hund h.1

/-- Every kind is undrawn, open, or settled, once articulation is
decidable.  The three are pairwise exclusive without that hypothesis. -/
theorem kind_status (s : Config C) (k : O.Kind)
    [Decidable (s.articulated k)] :
    Undrawn s k ∨ Open s k ∨ Settled s k := by
  cases h : s.assign k with
  | some v => exact Or.inr (Or.inr ⟨v, h⟩)
  | none =>
    by_cases hart : s.articulated k
    · exact Or.inr (Or.inl ⟨hart, h⟩)
    · exact Or.inl hart

/-- Settled-against: a different value at an exclusive kind is excluded
and incompatible.  This is synchronic; it does not freeze the cell. -/
theorem exclusive_excludes {s : Config C} {k : O.Kind}
    {v w : O.Value k}
    (hE : O.Exclusive k) (hv : s.assign k = some v) (hne : v ≠ w) :
    Excluded s k w ∧ ¬ C.compat ⟨k, v⟩ ⟨k, w⟩ :=
  ⟨⟨v, hv, hne⟩, C.exclusive_incompat hE hne⟩

/-- On a dichotomous kind, settlement orients one value and excludes the
other.  The old `resolution_orients`, recovered as a special case. -/
theorem dichotomous_orients {s : Config C} {k : O.Kind}
    (hd : O.Dichotomous k) (h : Settled s k) :
    ∃ a b : O.Value k,
      a ≠ b ∧ s.assign k = some a ∧ s.assign k ≠ some b ∧
        ∀ c, c = a ∨ c = b := by
  obtain ⟨a, b, hne, hall⟩ := hd
  obtain ⟨v, hv⟩ := h
  cases hall v with
  | inl hva =>
      cases hva
      refine ⟨a, b, hne, hv, ?_, hall⟩
      intro hb
      exact hne (Option.some.inj (hv.symm.trans hb))
  | inr hvb =>
      cases hvb
      refine ⟨b, a, Ne.symm hne, hv, ?_, ?_⟩
      · intro ha
        exact hne (Option.some.inj (ha.symm.trans hv))
      · intro c
        cases hall c with
        | inl hca => exact Or.inr hca
        | inr hcb => exact Or.inl hcb

def settle (s : Config C) (k : O.Kind) (v : O.Value k)
    (ho : Open s k) (hok : C.PairwiseOk (Assignment.set s.assign k v)) :
    Config C where
  articulated := s.articulated
  assign := Assignment.set s.assign k v
  realised_articulated := fun k' v' hv' =>
    Assignment.realised_set_cases hv'
      (fun eq _ => by cases eq; exact ho.1)
      (fun _ hs => s.realised_articulated k' v' hs)
  ok := hok

theorem settle_settles (s : Config C) (k : O.Kind) (v : O.Value k)
    (ho : Open s k) (hok : C.PairwiseOk (Assignment.set s.assign k v)) :
    Settles s (settle s k v ho hok) k v :=
  ⟨ho, rfl, fun _ => Iff.rfl⟩

def revise (s : Config C) (k : O.Kind) (v : O.Value k)
    {w : O.Value k} (hw : s.assign k = some w) (_hne : w ≠ v)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) : Config C where
  articulated := s.articulated
  assign := Assignment.set s.assign k v
  realised_articulated := fun k' v' hv' =>
    Assignment.realised_set_cases hv'
      (fun eq _ => by
        cases eq
        exact s.realised_articulated k w hw)
      (fun _ hs => s.realised_articulated k' v' hs)
  ok := hok

theorem revise_revises (s : Config C) (k : O.Kind) (v : O.Value k)
    {w : O.Value k} (hw : s.assign k = some w) (hne : w ≠ v)
    (hok : C.PairwiseOk (Assignment.set s.assign k v)) :
    Revises s (revise s k v hw hne hok) k v :=
  ⟨fun _ => Iff.rfl, rfl, ⟨w, hw, hne⟩⟩

def grow (s : Config C) (k : O.Kind) (_hund : Undrawn s k) : Config C where
  articulated := fun k' => s.articulated k' ∨ k' = k
  assign := s.assign
  realised_articulated := fun k' v' hv' =>
    Or.inl (s.realised_articulated k' v' hv')
  ok := s.ok

theorem grow_grows (s : Config C) (k : O.Kind) (hund : Undrawn s k) :
    Grows s (grow s k hund) :=
  ⟨fun _ h => Or.inl h, ⟨k, Or.inr rfl, hund⟩, rfl⟩

theorem undrawn_unassigned {s : Config C} {k : O.Kind}
    (h : Undrawn s k) : s.assign k = none := by
  cases h' : s.assign k with
  | none => rfl
  | some v => exact False.elim (h (s.realised_articulated k v h'))

theorem grow_remainder (s : Config C) (k : O.Kind) (hund : Undrawn s k) :
    Remainder (grow s k hund) :=
  ⟨k, Or.inr rfl, by
    change s.assign k = none
    exact undrawn_unassigned hund⟩

theorem open_after_settle {s : Config C} {k : O.Kind} {v : O.Value k}
    {ℓ : O.Kind}
    (ho : Open s k) (hok : C.PairwiseOk (Assignment.set s.assign k v))
    (hne : ℓ ≠ k) (hoℓ : Open s ℓ) :
    Open (settle s k v ho hok) ℓ :=
  ⟨hoℓ.1, by
    change Assignment.set s.assign k v ℓ = none
    rw [Assignment.set_ne _ _ _ _ hne]
    exact hoℓ.2⟩

/-- Settling one open kind does not close a different open kind.  Remainder
after a settle is this local fact, not a global law. -/
theorem settle_preserves_other_open {s : Config C} {k ℓ : O.Kind}
    {v : O.Value k}
    (ho : Open s k) (hok : C.PairwiseOk (Assignment.set s.assign k v))
    (hne : ℓ ≠ k) (hoℓ : Open s ℓ) :
    Remainder (settle s k v ho hok) :=
  ⟨ℓ, open_after_settle ho hok hne hoℓ⟩

/-- Independent settlements commute at configuration level. -/
theorem independent_settle_diamond {s : Config C} {k ℓ : O.Kind}
    {v : O.Value k} {w : O.Value ℓ}
    (hI : C.Independent k ℓ)
    (hok : Open s k) (hoℓ : Open s ℓ)
    (hsv : C.Settable s.assign k v) (hsw : C.Settable s.assign ℓ w) :
    Assignment.set (settle s k v hok hsv).assign ℓ w =
      Assignment.set (settle s ℓ w hoℓ hsw).assign k v ∧
    C.PairwiseOk (Assignment.set (settle s k v hok hsv).assign ℓ w) :=
  C.independent_commute hI hok.2 hoℓ.2 hsv hsw

/-- Time's arrow: the ancestral of archive growth.  Revision does not
enter this relation. -/
inductive Earlier : Config C → Config C → Prop
  | step {s t} : Grows s t → Earlier s t
  | trans {s t u} : Earlier s t → Earlier t u → Earlier s u

theorem earlier_mono {s t : Config C} (h : Earlier s t) :
    ∀ k, s.articulated k → t.articulated k := by
  induction h with
  | step g => exact g.1
  | trans _ _ ih1 ih2 =>
      intro k hk
      exact ih2 k (ih1 k hk)

theorem earlier_strict {s t : Config C} (h : Earlier s t) :
    ∃ k, t.articulated k ∧ ¬ s.articulated k := by
  induction h with
  | step g => exact g.2.1
  | trans h1 _ ih1 ih2 =>
      obtain ⟨ℓ, hu, hnt⟩ := ih2
      exact ⟨ℓ, hu, fun hs => hnt (earlier_mono h1 ℓ hs)⟩

theorem earlier_irrefl (s : Config C) : ¬ Earlier s s := by
  intro h
  obtain ⟨k, hk, hnk⟩ := earlier_strict h
  exact hnk hk

theorem earlier_asymm {s t : Config C} (h : Earlier s t) : ¬ Earlier t s :=
  fun h' => earlier_irrefl s (Earlier.trans h h')

theorem settles_not_earlier {s t : Config C} {k : O.Kind} {v : O.Value k}
    (h : Settles s t k v) : ¬ Earlier s t := by
  intro he
  obtain ⟨ℓ, ht, hs⟩ := earlier_strict he
  exact hs ((h.2.2 ℓ).mp ht)

theorem revises_not_earlier {s t : Config C} {k : O.Kind} {v : O.Value k}
    (h : Revises s t k v) : ¬ Earlier s t := by
  intro he
  obtain ⟨ℓ, ht, hs⟩ := earlier_strict he
  exact hs ((h.1 ℓ).mp ht)

/-- Optional: every configuration leaves some articulated kind unset.
Permanent latency is this law, not a theorem of coherence. -/
def RemainderLaw : Prop := ∀ s : Config C, Remainder s

theorem remainderLaw_of {s t : Config C} {k : O.Kind} {v : O.Value k}
    (hR : RemainderLaw (O := O) (C := C)) (_h : Settles s t k v) :
    Remainder t :=
  hR t

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

/-- Unused coherence at an undrawn kind is growth. -/
theorem possible_grow_of_undrawn {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) (hund : s.Undrawn k) :
    ∃ t, Config.Grows s t :=
  ⟨s.grow k hund, s.grow_grows k hund⟩

/-- Unused coherence at a settled kind is revision, when the new value
is settable.  Exclusivity does not block this: `set` replaces. -/
theorem possible_revise_of_settled {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) {w v : O.Value k}
    (hw : s.assign k = some w) (hne : w ≠ v)
    (hok : C.Settable s.assign k v) :
    ∃ t, Config.Revises s t k v :=
  ⟨s.revise k v hw hne hok, s.revise_revises k v hw hne hok⟩

/-- The one possibility relation: coherent settle, grow, or revise. -/
inductive Possible {O : Ontology.{u,v}} {C : Coherence O} :
    Config C → Config C → Prop
  | of_settle {s t : Config C} {k : O.Kind} {v : O.Value k} :
      Config.Settles s t k v → Possible s t
  | of_grow {s t : Config C} :
      Config.Grows s t → Possible s t
  | of_revise {s t : Config C} {k : O.Kind} {v : O.Value k} :
      Config.Revises s t k v → Possible s t

theorem possible_of_open {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) (ho : s.Open k)
    (v : O.Value k) (hok : C.Settable s.assign k v) :
    Possible s (s.settle k v ho hok) :=
  Possible.of_settle (s.settle_settles k v ho hok)

theorem possible_of_undrawn {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) (hund : s.Undrawn k) :
    Possible s (s.grow k hund) :=
  Possible.of_grow (s.grow_grows k hund)

theorem possible_of_settled {O : Ontology.{u,v}} {C : Coherence O}
    (s : Config C) (k : O.Kind) {w v : O.Value k}
    (hw : s.assign k = some w) (hne : w ≠ v)
    (hok : C.Settable s.assign k v) :
    Possible s (s.revise k v hw hne hok) :=
  Possible.of_revise (s.revise_revises k v hw hne hok)

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

/-- Actuality is a selector on values, not a second dynamics.  Which kind
is settled remains a choice; the selector only orients the value. -/
def Actual {O : Ontology.{u,v}} {C : Coherence O} (sel : Selector O)
    (s t : Config C) (k : O.Kind) (v : O.Value k) : Prop :=
  Config.Settles s t k v ∧ v = sel.choose k

theorem actual_value_determinate {O : Ontology.{u,v}} {C : Coherence O}
    {sel : Selector O} {s t t' : Config C} {k : O.Kind}
    {v w : O.Value k}
    (h : Actual (C := C) sel s t k v)
    (h' : Actual (C := C) sel s t' k w) : v = w :=
  h.2.trans h'.2.symm

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

theorem restrict_hides {O : Ontology.{u,v}}
    (σ : Assignment O) (r : Region O) (k : O.Kind) (hr : r k = false) :
    restrict σ r k = none := by
  unfold restrict
  rw [hr]
  rfl

namespace Config

variable {O : Ontology.{u,v}} {C : Coherence O}

def restrict (s : Config C) (r : Region O) : Config C where
  articulated := fun k => r k = true ∧ s.articulated k
  assign := OpenSite.restrict s.assign r
  realised_articulated := fun k v hv => by
    unfold OpenSite.restrict at hv
    split at hv
    · next htrue => exact ⟨htrue, s.realised_articulated k v hv⟩
    · cases hv
  ok := restrict_sub s.ok r

theorem restrict_keeps {s : Config C} {r : Region O} {k : O.Kind}
    (hr : r k = true) :
    (restrict s r).assign k = s.assign k ∧
      ((restrict s r).articulated k ↔ s.articulated k) :=
  ⟨restrict_agrees s.assign r k hr, ⟨fun h => h.2, fun ha => ⟨hr, ha⟩⟩⟩

theorem restrict_hides_kind {s : Config C} {r : Region O} {k : O.Kind}
    (hr : r k = false) :
    (restrict s r).assign k = none ∧ ¬ (restrict s r).articulated k :=
  ⟨restrict_hides s.assign r k hr, fun h => nomatch hr.symm.trans h.1⟩

end Config

/-! ## 6. The void -/

namespace Void

inductive K where
  | star
  deriving DecidableEq

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := fun _ => Bool
  Exclusive := fun _ => True
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
  exclusive_incompat := by
    intro k v w _ hne h
    cases k
    exact hne h

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

/-! ## 6b. Closed: remainder is not a theorem of coherence

A fully settled exclusive kind has no open cell.  Permanent latency is
`RemainderLaw`, optional, not derived from pairwise compatibility. -/

namespace Closed

inductive K where
  | only
  deriving DecidableEq

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := fun _ => Bool
  Exclusive := fun _ => True
  decEqKind := inferInstance

def compat : ont.Det → ont.Det → Prop
  | ⟨.only, a⟩, ⟨.only, b⟩ => a = b

abbrev coh : Coherence ont where
  compat := compat
  refl := by intro d; cases d with | mk k v => cases k; exact rfl
  symm := by
    intro d e h
    cases d with | mk k₁ v₁ =>
    cases e with | mk k₂ v₂ =>
    cases k₁; cases k₂
    exact h.symm
  exclusive_incompat := by
    intro k v w _ hne h
    cases k
    exact hne h

def fullAssign : Assignment ont
  | .only => some true

def full : Config coh where
  articulated := fun _ => True
  assign := fullAssign
  realised_articulated := fun _ _ _ => trivial
  ok := by
    intro k ℓ vk vl hk hl
    cases k; cases ℓ
    simp only [fullAssign] at hk hl
    cases hk; cases hl
    exact rfl

theorem settled : full.Settled K.only :=
  ⟨true, rfl⟩

theorem not_remainder : ¬ full.Remainder := by
  intro ⟨k, _, hnone⟩
  cases k
  exact Option.noConfusion (hnone : fullAssign K.only = none)

theorem not_remainderLaw : ¬ Config.RemainderLaw (C := coh) :=
  fun h => not_remainder (h full)

end Closed

theorem remainder_not_coherence_level :
    ∃ (O : Ontology.{0,0}) (C : Coherence O),
      ¬ Config.RemainderLaw (C := C) :=
  ⟨Closed.ont, Closed.coh, Closed.not_remainderLaw⟩

/-! ## 6c. Locked: independence is not forced

Two interacting kinds, no independent pair.  Space as independence is a
structure some coherences have, not a consequence of having kinds. -/

namespace Locked

inductive K where
  | sw | lamp
  deriving DecidableEq

def Val : K → Type
  | .sw => Bool
  | .lamp => Bool

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := Val
  Exclusive := fun _ => True
  decEqKind := inferInstance

def compat (d e : ont.Det) : Prop :=
  match d.kind, e.kind, d.value, e.value with
  | .sw, .sw, a, b => a = b
  | .lamp, .lamp, a, b => a = b
  | .sw, .lamp, a, b => ¬ (a = false ∧ b = true)
  | .lamp, .sw, a, b => ¬ (b = false ∧ a = true)

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
  exclusive_incompat := by
    intro k v w _ hne h
    cases k <;> exact hne h

theorem no_independent_pair (k ℓ : K) : ¬ coh.Independent k ℓ := by
  intro ⟨hne, hall⟩
  cases k <;> cases ℓ
  · exact hne rfl
  · exact hall false true ⟨rfl, rfl⟩
  · exact hall true false ⟨rfl, rfl⟩
  · exact hne rfl

end Locked

theorem independence_not_forced :
    ∃ (O : Ontology.{0,0}) (C : Coherence O),
      ∀ k ℓ : O.Kind, ¬ C.Independent k ℓ :=
  ⟨Locked.ont, Locked.coh, Locked.no_independent_pair⟩

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
  Exclusive := fun _ => True
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
  exclusive_incompat := by
    intro k v w _ hne h
    cases k <;> exact hne h

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

theorem independent_hue_gap : coh.Independent K.hue K.gap := by
  constructor
  · intro h; cases h
  · intro _ _; exact trivial

theorem independent_sw_gap : coh.Independent K.sw K.gap := by
  constructor
  · intro h; cases h
  · intro _ _; exact trivial

theorem not_independent_sw_lamp : ¬ coh.Independent K.sw K.lamp := by
  intro ⟨_, hall⟩
  have : compat ⟨K.sw, false⟩ ⟨K.lamp, true⟩ := hall false true
  exact this ⟨rfl, rfl⟩

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

theorem hue_gap_sw_amalgamate :
    coh.PairwiseOk
      (Assignment.set
        (Assignment.set (Assignment.set vacant K.hue Hue.red) K.sw true)
        K.gap false) :=
  coh.independent_amalgamate3
    independent_hue_sw independent_hue_gap independent_sw_gap
    rfl rfl rfl
    (settable_hue Hue.red) (coh.settable_empty K.sw true)
    (coh.settable_empty K.gap false)

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
  Config.Earlier.step seed_grows_origin

theorem origin_not_earlier_self : ¬ Config.Earlier origin origin :=
  Config.earlier_irrefl origin

theorem origin_not_earlier_seed : ¬ Config.Earlier origin seed :=
  Config.earlier_asymm earlier_seed_origin

theorem origin_remainder : origin.Remainder :=
  ⟨K.gap, origin_open K.gap⟩

theorem origin_status (k : K) :
    origin.Undrawn k ∨ origin.Open k ∨ origin.Settled k :=
  haveI : Decidable (origin.articulated k) := isTrue trivial
  Config.kind_status origin k

theorem seed_undrawn_hue : seed.Undrawn K.hue := by
  intro h
  cases h

theorem possible_seed_grows : Possible seed origin :=
  Possible.of_grow seed_grows_origin

theorem possible_origin_hue :
    Possible origin
      (origin.settle K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red)) :=
  possible_of_open origin K.hue (origin_open K.hue) Hue.red (settable_hue Hue.red)

theorem dichotomous_sw : ont.Dichotomous K.sw :=
  ⟨true, false, And.intro (fun h => nomatch h) (fun c =>
    match c with
    | true => Or.inl rfl
    | false => Or.inr rfl)⟩

theorem not_dichotomous_hue : ¬ ont.Dichotomous K.hue := by
  intro ⟨a, b, hne, hall⟩
  cases a with
  | red =>
    cases b with
    | red => exact hne rfl
    | green =>
      cases hall Hue.blue with
      | inl h => nomatch h
      | inr h => nomatch h
    | blue =>
      cases hall Hue.green with
      | inl h => nomatch h
      | inr h => nomatch h
  | green =>
    cases b with
    | red =>
      cases hall Hue.blue with
      | inl h => nomatch h
      | inr h => nomatch h
    | green => exact hne rfl
    | blue =>
      cases hall Hue.red with
      | inl h => nomatch h
      | inr h => nomatch h
  | blue =>
    cases b with
    | red =>
      cases hall Hue.green with
      | inl h => nomatch h
      | inr h => nomatch h
    | green =>
      cases hall Hue.red with
      | inl h => nomatch h
      | inr h => nomatch h
    | blue => exact hne rfl

def switched : Config coh :=
  origin.settle K.sw true (origin_open K.sw) (coh.settable_empty K.sw true)

theorem switched_orients :
    ∃ a b : Val K.sw,
      a ≠ b ∧ switched.assign K.sw = some a ∧
        switched.assign K.sw ≠ some b ∧ ∀ c, c = a ∨ c = b :=
  Config.dichotomous_orients (s := switched) dichotomous_sw ⟨true, rfl⟩

theorem switched_excludes_off :
    Config.Excluded switched K.sw false ∧
      ¬ compat ⟨K.sw, true⟩ ⟨K.sw, false⟩ :=
  Config.exclusive_excludes (by trivial)
    (show switched.assign K.sw = some true from rfl)
    (fun h => nomatch h)

theorem switched_not_open : ¬ switched.Open K.sw :=
  Config.settled_not_open ⟨true, rfl⟩

theorem remainder_after_hue :
    Config.Remainder
      (origin.settle K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red)) :=
  Config.settle_preserves_other_open
    (origin_open K.hue) (settable_hue Hue.red)
    (by decide) (origin_open K.sw)

theorem origin_hue_sw_cfg_diamond :
    Assignment.set
        (origin.settle K.hue Hue.red (origin_open K.hue)
          (settable_hue Hue.red)).assign
        K.sw true =
      Assignment.set
        (origin.settle K.sw true (origin_open K.sw)
          (coh.settable_empty K.sw true)).assign
        K.hue Hue.red ∧
    coh.PairwiseOk
      (Assignment.set
        (origin.settle K.hue Hue.red (origin_open K.hue)
          (settable_hue Hue.red)).assign
        K.sw true) :=
  Config.independent_settle_diamond independent_hue_sw
    (origin_open K.hue) (origin_open K.sw)
    (settable_hue Hue.red) (coh.settable_empty K.sw true)

theorem actual_hue_red :
    Actual sel origin
      (origin.settle K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red))
      K.hue Hue.red :=
  ⟨origin.settle_settles K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red),
    rfl⟩

def hued : Config coh :=
  origin.settle K.hue Hue.red (origin_open K.hue) (settable_hue Hue.red)

theorem hued_red : hued.assign K.hue = some Hue.red :=
  Assignment.set_self origin.assign K.hue Hue.red

theorem hued_revise_green_ok :
    coh.Settable hued.assign K.hue Hue.green :=
  coh.settable_overwrite (k := K.hue) (v := Hue.red) (settable_hue Hue.green)

def huedGreen : Config coh :=
  hued.revise K.hue Hue.green hued_red (fun h => nomatch h) hued_revise_green_ok

theorem hue_oscillates :
    Config.Revises hued huedGreen K.hue Hue.green ∧
      ¬ Config.Earlier hued huedGreen :=
  ⟨hued.revise_revises K.hue Hue.green hued_red (fun h => nomatch h)
      hued_revise_green_ok,
    Config.revises_not_earlier
      (hued.revise_revises K.hue Hue.green hued_red (fun h => nomatch h)
        hued_revise_green_ok)⟩

theorem possible_hue_revise : Possible hued huedGreen :=
  possible_of_settled (v := Hue.green) hued K.hue hued_red
    (fun h => nomatch h) hued_revise_green_ok

def saturatedAssign : Assignment ont
  | .sw => some true
  | .lamp => some true
  | .hue => some Hue.red
  | .gap => some false

def saturated : Config coh where
  articulated := allArt
  assign := saturatedAssign
  realised_articulated := fun _ _ _ => trivial
  ok := by
    intro k ℓ vk vl hk hl
    cases k <;> cases ℓ <;>
      simp only [saturatedAssign] at hk hl <;>
      cases Option.some.inj hk <;>
      cases Option.some.inj hl <;>
      first | exact rfl | trivial | (intro h; exact nomatch h.1) | (intro h; exact nomatch h.2)

theorem saturated_not_remainder : ¬ saturated.Remainder := by
  intro ⟨k, _, hnone⟩
  cases k with
  | sw => exact Option.noConfusion (hnone : saturatedAssign K.sw = none)
  | lamp => exact Option.noConfusion (hnone : saturatedAssign K.lamp = none)
  | hue => exact Option.noConfusion (hnone : saturatedAssign K.hue = none)
  | gap => exact Option.noConfusion (hnone : saturatedAssign K.gap = none)

/-- The same world that is open at the origin can be fully settled.
Remainder is a property of configurations, not of the coherence. -/
theorem world_not_remainderLaw : ¬ Config.RemainderLaw (C := coh) :=
  fun h => saturated_not_remainder (h saturated)

theorem seen_hides_saturated :
    (Config.restrict saturated seen).assign K.sw = none ∧
      ¬ (Config.restrict saturated seen).articulated K.sw ∧
      (Config.restrict saturated seen).assign K.hue = some Hue.red ∧
      (Config.restrict saturated seen).assign K.lamp = some true ∧
      (Config.restrict saturated seen).assign K.gap = none :=
  let hs := Config.restrict_hides_kind (s := saturated) (r := seen) (k := K.sw) rfl
  let hh := Config.restrict_keeps (s := saturated) (r := seen) (k := K.hue) rfl
  let hl := Config.restrict_keeps (s := saturated) (r := seen) (k := K.lamp) rfl
  let hg := Config.restrict_hides_kind (s := saturated) (r := seen) (k := K.gap) rfl
  ⟨hs.1, hs.2, hh.1, hl.1, hg.1⟩

end World

/-! ## Axiom regression -/

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
info: 'OpenSite.remainder_not_coherence_level' does not depend on any axioms
-/
#guard_msgs in
#print axioms remainder_not_coherence_level

/--
info: 'OpenSite.independence_not_forced' does not depend on any axioms
-/
#guard_msgs in
#print axioms independence_not_forced

/--
info: 'OpenSite.World.origin_not_earlier_self' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.origin_not_earlier_self

/--
info: 'OpenSite.World.world_not_remainderLaw' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.world_not_remainderLaw

/--
info: 'OpenSite.World.origin_hue_sw_cfg_diamond' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms World.origin_hue_sw_cfg_diamond

/--
info: 'OpenSite.World.hue_gap_sw_amalgamate' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.hue_gap_sw_amalgamate

/--
info: 'OpenSite.World.hue_oscillates' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms World.hue_oscillates

/--
info: 'OpenSite.World.seen_hides_saturated' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.seen_hides_saturated

/--
info: 'OpenSite.World.switched_excludes_off' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.switched_excludes_off

/--
info: 'OpenSite.World.possible_hue_revise' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms World.possible_hue_revise

end OpenSite
