import Init

/-!
# Open Sites

A successor schema, not a patch of `LatentActual`.  The binary development
asked one \(\mathbb{Z}/2\)-torsor to be determinacy, change, latency, time,
reversal, and (in prospect) space, causation, and observation.  Those are
different jobs.  Lean will hold a metaphysics that *gives each job its own
primitive* and then proves only what those primitives actually yield.

**Do not encode. Stratify.**

| Job | Primitive here | What is *not* claimed |
| --- | --- | --- |
| Determinacy | a value of a kind (`Value k`) | that every kind has two poles |
| Exclusivity | a property of *some* kinds | that all determination is exclusive |
| Latency | non-realization, stratified by articulation | powers, propensities, degrees |
| Remainder | every site has an unsettled articulated kind | that this is phenomenology |
| Becoming | acts that settle a value at a kind | a unique successor |
| Time | the ancestral of acts, ranked | metric, continuous, or lived duration |
| Possibility | the act relation | possible worlds |
| Actuality | a strand (a function of steps) | that seriality *is* that function |
| Space | coexistence of sites | geometry, metric, embodiment |
| Causation | one-step acting | counterfactuals, prehension |
| Observation | appearance, not implied by realization | consciousness, givenness |

The intended philosophical remainder of the old project is kept, and
detached from binary opposition: actuality can be locally determinate
without exhausting what a site leaves open; the possible can exceed a
single selection whenever some open kind has two values; time is not
space; a completed infinite history is extra data, not a synonym of
one-step productivity.

No `axiom`, no `sorry`, no `native_decide`.  Binary kinds remain as a
*special case* (`Dichotomous`), not as the engine of the cosmos.
-/

namespace OpenSite

universe u v w

/-! ## 0. Ontology: kinds as types of values -/

/-- A kind is a determinable.  Its values are its determinates.
Exclusivity is optional: an exclusive kind realises at most one value at a
site; a non-exclusive kind may realise several (a chord, a mixture). -/
structure Ontology where
  Kind : Type u
  Value : Kind → Type v
  Exclusive : Kind → Prop

namespace Ontology

variable (O : Ontology.{u,v})

def Incompatible {k : O.Kind} (x y : O.Value k) : Prop :=
  O.Exclusive k ∧ x ≠ y

/-- Two values, no third: the old binary schema, as a *property of a kind*. -/
def Dichotomous (k : O.Kind) : Prop :=
  ∃ a b : O.Value k, a ≠ b ∧ ∀ c, c = a ∨ c = b

end Ontology

/-! ## 1. Sites -/

/-- A site is a local presentation of kinds.  Articulation is not
realisation.  Remainder is a site law, not a theorem of logic: nothing in
the kind/value distinction forces an unsettled kind to exist. -/
structure Sites (O : Ontology.{u,v}) where
  Carrier : Type w
  articulated : Carrier → O.Kind → Prop
  realises : (s : Carrier) → (k : O.Kind) → O.Value k → Prop
  realises_articulates :
    ∀ {s k v}, realises s k v → articulated s k
  exclusive_unique :
    ∀ {s k v w}, O.Exclusive k →
      realises s k v → realises s k w → v = w
  remainder :
    ∀ s, ∃ k, articulated s k ∧ ∀ v, ¬ realises s k v

namespace Sites

variable {O : Ontology.{u,v}} (S : Sites.{u,v,w} O)

def Open (s : S.Carrier) (k : O.Kind) : Prop :=
  S.articulated s k ∧ ∀ v, ¬ S.realises s k v

def Settled (s : S.Carrier) (k : O.Kind) : Prop :=
  ∃ v, S.realises s k v

def Undrawn (s : S.Carrier) (k : O.Kind) : Prop :=
  ¬ S.articulated s k

def Latent (s : S.Carrier) (k : O.Kind) (v : O.Value k) : Prop :=
  ¬ S.realises s k v

def Null (s : S.Carrier) : Prop :=
  ∀ k v, ¬ S.realises s k v

theorem open_of_remainder (s : S.Carrier) : ∃ k, S.Open s k :=
  S.remainder s

theorem open_not_settled {s k} (h : S.Open s k) : ¬ S.Settled s k := by
  intro ⟨v, hv⟩
  exact h.2 v hv

theorem settled_articulated {s k} (h : S.Settled s k) : S.articulated s k := by
  obtain ⟨v, hv⟩ := h
  exact S.realises_articulates hv

theorem exclusive_settled_unique {s k}
    (hex : O.Exclusive k) (h : S.Settled s k) :
    ∃ v, S.realises s k v ∧ ∀ w, S.realises s k w → w = v := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact (S.exclusive_unique hex hv hw).symm

/-- On a dichotomous exclusive kind, settlement orients one value and
excludes the other.  This is the old `resolution_orients`, localised. -/
theorem dichotomous_orients {s k}
    (hex : O.Exclusive k) (hd : O.Dichotomous k) (h : S.Settled s k) :
    ∃ a b : O.Value k,
      a ≠ b ∧ S.realises s k a ∧ ¬ S.realises s k b ∧
        ∀ c, c = a ∨ c = b := by
  obtain ⟨a, b, hne, hall⟩ := hd
  obtain ⟨v, hv, huniq⟩ := S.exclusive_settled_unique hex h
  cases hall v with
  | inl hva =>
      refine ⟨a, b, hne, ?_, ?_, hall⟩
      · rw [← hva]; exact hv
      · intro hb
        have : b = v := huniq b hb
        exact hne (hva.symm.trans this.symm)
  | inr hvb =>
      refine ⟨b, a, hne.symm, ?_, ?_, ?_⟩
      · rw [← hvb]; exact hv
      · intro ha
        have : a = v := huniq a ha
        exact hne (this.trans hvb)
      · intro c
        cases hall c with
        | inl hca => exact Or.inr hca
        | inr hcb => exact Or.inl hcb

end Sites

/-! ## 2. Acts, rank, and time as ancestry -/

/-- An act settles one value at one kind, keeps other kinds' realisations,
and does not delete prior articulation.  Time is *not* a field of this
structure; it will be the ancestral of acts, once a rank forbids cycles. -/
structure Continues {O : Ontology.{u,v}} (S : Sites.{u,v,w} O)
    (s t : S.Carrier) (k : O.Kind) (v : O.Value k) : Prop where
  settles : S.realises t k v
  persists : ∀ k' v', k' ≠ k →
    (S.realises s k' v' ↔ S.realises t k' v')
  art_mono : ∀ k', S.articulated s k' → S.articulated t k'

namespace Continues

variable {O : Ontology.{u,v}} {S : Sites.{u,v,w} O}

theorem off_target {s t k v k' v'}
    (h : Continues S s t k v) (hne : k' ≠ k)
    (hs : S.realises s k' v') : S.realises t k' v' :=
  (h.persists k' v' hne).mp hs

theorem exclusive_target {s t k v w}
    (h : Continues S s t k v) (hex : O.Exclusive k)
    (hw : S.realises t k w) : w = v :=
  S.exclusive_unique hex hw h.settles

end Continues

/-- Dynamics: a lawful act relation together with a rank that every act
advances.  The rank is an honest historicity premise — a clock, not a
memory, not a phenomenology.  Without it, ancestry need not be acyclic. -/
structure Dynamics {O : Ontology.{u,v}} (S : Sites.{u,v,w} O) where
  Active : S.Carrier → S.Carrier → (k : O.Kind) → O.Value k → Prop
  continues : ∀ {s t k v}, Active s t k v → Continues S s t k v
  rank : S.Carrier → Nat
  advances : ∀ {s t k v}, Active s t k v → rank s < rank t

inductive Chain {O : Ontology.{u,v}} {S : Sites.{u,v,w} O}
    (D : Dynamics S) : Nat → S.Carrier → S.Carrier → Prop
  | refl (s : S.Carrier) : Chain D 0 s s
  | step {n s t u k v} :
      Chain D n s t → D.Active t u k v → Chain D (n + 1) s u

namespace Dynamics

variable {O : Ontology.{u,v}} {S : Sites.{u,v,w} O} (D : Dynamics S)

theorem chain_rank_le {n s t} (h : Chain D n s t) :
    D.rank s ≤ D.rank t := by
  induction h with
  | refl s => exact Nat.le_refl _
  | @step n s t u k v c a ih =>
      exact Nat.le_trans ih (Nat.le_of_lt (D.advances a))

theorem chain_pos_rank {n s t} (h : Chain D n s t) (hn : n ≠ 0) :
    D.rank s < D.rank t := by
  induction h with
  | refl s => exact absurd rfl hn
  | @step n s t u k v c a ih =>
      cases n with
      | zero =>
          cases c
          exact D.advances a
      | succ n =>
          exact Nat.lt_trans (ih (Nat.succ_ne_zero n)) (D.advances a)

/-- Concatenation of finite runs. -/
theorem chain_add {m t u} (h₂ : Chain D m t u) :
    ∀ {n s}, Chain D n s t → Chain D (n + m) s u := by
  induction h₂ with
  | refl t =>
      intro n s h₁
      rw [Nat.add_zero]
      exact h₁
  | @step m t u v k w c a ih =>
      intro n s h₁
      rw [Nat.add_succ]
      exact Chain.step (ih h₁) a

def Earlier (s t : S.Carrier) : Prop :=
  ∃ n, n ≠ 0 ∧ Chain D n s t

theorem earlier_of_active {s t k v} (h : D.Active s t k v) :
    D.Earlier s t :=
  ⟨1, Nat.one_ne_zero, Chain.step (Chain.refl s) h⟩

theorem earlier_irrefl (s : S.Carrier) : ¬ D.Earlier s s := by
  intro ⟨n, hn, hc⟩
  exact Nat.lt_irrefl _ (D.chain_pos_rank hc hn)

theorem earlier_trans {s t u} (h₁ : D.Earlier s t) (h₂ : D.Earlier t u) :
    D.Earlier s u := by
  obtain ⟨n, hn, hc₁⟩ := h₁
  obtain ⟨m, hm, hc₂⟩ := h₂
  refine ⟨n + m, ?_, D.chain_add hc₂ hc₁⟩
  intro hnm
  cases n with
  | zero => exact hn rfl
  | succ n =>
      rw [Nat.succ_add] at hnm
      exact Nat.succ_ne_zero _ hnm

theorem earlier_asymm {s t} (h : D.Earlier s t) : ¬ D.Earlier t s :=
  fun h' => D.earlier_irrefl s (D.earlier_trans h h')

/-- Off-target realised content persists through one act.  Persistence, not
observation. -/
theorem persists {s t k v k' v'}
    (h : D.Active s t k v) (hne : k' ≠ k)
    (hs : S.realises s k' v') : S.realises t k' v' :=
  Continues.off_target (D.continues h) hne hs

/-- One-step seriality.  This is productivity.  It is not a completed
infinite history. -/
def Productive : Prop :=
  ∀ s, ∃ t k v, D.Active s t k v

/-- Seriality yields arbitrarily long *finite* runs, as a `Prop`-level
existence.  No function `Nat → Carrier` is constructed. -/
theorem productive_unbounded (h : D.Productive) :
    ∀ n s, ∃ t, Chain D n s t := by
  intro n
  induction n with
  | zero =>
      intro s
      exact ⟨s, Chain.refl s⟩
  | succ n ih =>
      intro s
      obtain ⟨t, ht⟩ := ih s
      obtain ⟨u, k, v, ha⟩ := h t
      exact ⟨u, Chain.step ht ha⟩

/-- A completed ω-history is extra data: a chosen successor at every
index.  From `Productive` this would be countable dependent choice, which
this file does not assume.  Models may still *supply* a history. -/
structure History where
  nth : Nat → S.Carrier
  step : ∀ n, ∃ k v, D.Active (nth n) (nth (n + 1)) k v

theorem history_chain (H : History D) :
    ∀ n, Chain D n (H.nth 0) (H.nth n) := by
  intro n
  induction n with
  | zero => exact Chain.refl (H.nth 0)
  | succ n ih =>
      obtain ⟨k, v, ha⟩ := H.step n
      exact Chain.step ih ha

theorem history_earlier (H : History D) (n : Nat) :
    D.Earlier (H.nth n) (H.nth (n + 1)) := by
  obtain ⟨k, v, ha⟩ := H.step n
  exact D.earlier_of_active ha

/-- Direct causation is one act.  Temporal precedence is ancestry.
Every cause precedes; not every precedence is a direct cause. -/
def Direct (s t : S.Carrier) : Prop :=
  ∃ k v, D.Active s t k v

theorem direct_earlier {s t} (h : D.Direct s t) : D.Earlier s t := by
  obtain ⟨k, v, ha⟩ := h
  exact D.earlier_of_active ha

end Dynamics

/-! ## 3. Selection, and when the possible exceeds it -/

structure Selector {O : Ontology.{u,v}} (S : Sites.{u,v,w} O) where
  choose : (s : S.Carrier) → (k : O.Kind) → O.Value k

namespace Dynamics

variable {O : Ontology.{u,v}} {S : Sites.{u,v,w} O} (D : Dynamics S)

def Respects (sel : Selector S) : Prop :=
  ∀ {s t k v}, D.Active s t k v → v = sel.choose s k

/-- Plenitude *at a kind and site*: every value of that open kind heads
some act.  This is not required of the remainder kind.  Remainder may be
reserved and unsettleable; workable openness is a different kind. -/
def RichAt (s : S.Carrier) (k : O.Kind) : Prop :=
  S.Open s k ∧ ∀ v, ∃ t, D.Active s t k v

/-- If an open kind has two values and both are possible targets, no
selector is respected.  Binarity of the *whole field* is not required. -/
theorem richAt_exceeds_selector {s k}
    (hR : D.RichAt s k) {v w : O.Value k} (hne : v ≠ w)
    (sel : Selector S) : ¬ D.Respects sel := by
  intro hres
  obtain ⟨t, htv⟩ := hR.2 v
  obtain ⟨t', htw⟩ := hR.2 w
  exact hne ((hres htv).trans (hres htw).symm)

end Dynamics

/-! ## 4. Coexistence (the spatial primitive, without geometry) -/

/-- Joint actuality.  Coexistent sites are not temporally ordered.
This is the distinction the archive-incomparability of the old development
could not make: modal branching, temporal incomparability, and
co-presence are different relations.  Here only co-presence is primitive;
geometry would be a further structure on it. -/
structure Coexistence {O : Ontology.{u,v}} {S : Sites.{u,v,w} O}
    (D : Dynamics S) where
  together : S.Carrier → S.Carrier → Prop
  refl : ∀ s, together s s
  symm : ∀ {s t}, together s t → together t s
  not_time : ∀ {s t}, together s t → ¬ D.Earlier s t

namespace Coexistence

variable {O : Ontology.{u,v}} {S : Sites.{u,v,w} O} {D : Dynamics S}
variable (C : Coexistence D)

theorem time_not_together {s t} (h : D.Earlier s t) : ¬ C.together s t :=
  fun ht => C.not_time ht h

theorem irrefl_of_earlier (s : S.Carrier) : ¬ D.Earlier s s :=
  D.earlier_irrefl s

end Coexistence

/-! ## 5. Appearance, without co-realization -/

/-- Observation is a relation of appearing, not a synonym of realisation.
Illusion is therefore possible.  The old `ObserverLayer` forbade it by
requiring co-realization. -/
structure Appearance {O : Ontology.{u,v}} (S : Sites.{u,v,w} O) where
  Observer : Type
  appears : Observer → S.Carrier → (k : O.Kind) → O.Value k → Prop

namespace Appearance

variable {O : Ontology.{u,v}} {S : Sites.{u,v,w} O} (A : Appearance S)

def Veridical (o : A.Observer) (s : S.Carrier)
    (k : O.Kind) (v : O.Value k) : Prop :=
  A.appears o s k v ∧ S.realises s k v

def Illusion (o : A.Observer) (s : S.Carrier)
    (k : O.Kind) (v : O.Value k) : Prop :=
  A.appears o s k v ∧ ¬ S.realises s k v

/-- Location constraint, not a body, not a phenomenology. -/
structure Located (A : Appearance S) where
  locOf : A.Observer → S.Carrier → Prop
  only_located : ∀ {o s k v}, A.appears o s k v → locOf o s

end Appearance

/-! ## 6. The void: remainder without actuality -/

namespace Void

inductive K where
  | star

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := fun _ => Bool
  Exclusive := fun _ => True

abbrev sites : Sites.{0,0,0} ont where
  Carrier := Unit
  articulated := fun _ _ => True
  realises := fun _ _ _ => False
  realises_articulates := fun h => False.elim h
  exclusive_unique := fun _ h => False.elim h
  remainder := fun _ => ⟨K.star, trivial, fun _ h => h⟩

theorem null : sites.Null () := fun _ _ h => h

theorem open_star : sites.Open () K.star :=
  ⟨trivial, fun _ h => h⟩

/-- Presentation-level remainder does not force a realised value. -/
theorem nullity_coherent : sites.Null () ∧ ∃ k, sites.Open () k :=
  ⟨null, K.star, open_star⟩

end Void

/-- Absolute nullity is compatible with the site laws. -/
theorem nullity_not_derivable :
    ∃ (O : Ontology.{0,0}) (S : Sites.{0,0,0} O) (s : S.Carrier),
      S.Null s :=
  ⟨Void.ont, Void.sites, (), Void.null⟩

/-! ## 7. A world: plural kinds, two places, a reserved remainder -/

namespace World

inductive K where
  | hue
  | pulse
  | choice
  | gap
  deriving DecidableEq

inductive Hue where
  | red | green | blue
  deriving DecidableEq

inductive Pulse where
  | lo | hi
  deriving DecidableEq

inductive Choice where
  | left | right
  deriving DecidableEq

inductive Gap where
  | west | east
  deriving DecidableEq

def Val : K → Type
  | .hue => Hue
  | .pulse => Pulse
  | .choice => Choice
  | .gap => Gap

abbrev ont : Ontology.{0,0} where
  Kind := K
  Value := Val
  Exclusive := fun _ => True

structure St where
  clock : Nat
  loc : Bool
  hue : Hue
  pulse : Pulse
  choice : Option Choice

def articulated (_s : St) (_k : K) : Prop := True

def realises (s : St) (k : K) (v : Val k) : Prop :=
  match k, v with
  | .hue, v => v = s.hue
  | .pulse, v => v = s.pulse
  | .choice, v => s.choice = some v
  | .gap, _ => False

theorem exclusive_unique {s : St} {k : K} {v w : Val k}
    (hv : realises s k v) (hw : realises s k w) : v = w := by
  cases k with
  | hue =>
      exact hv.trans hw.symm
  | pulse =>
      exact hv.trans hw.symm
  | choice =>
      exact Option.some.inj (hv.symm.trans hw)
  | gap =>
      exact False.elim hv

theorem remainder (s : St) :
    ∃ k, articulated s k ∧ ∀ v, ¬ realises s k v :=
  ⟨K.gap, trivial, fun _ h => h⟩

abbrev sites : Sites.{0,0,0} ont where
  Carrier := St
  articulated := articulated
  realises := realises
  realises_articulates := fun _ => trivial
  exclusive_unique := fun _ => exclusive_unique
  remainder := remainder

def Active (s t : St) (k : K) (v : Val k) : Prop :=
  t.clock = s.clock + 1 ∧ t.loc = s.loc ∧
    match k, v with
    | .hue, v => t.hue = v ∧ t.pulse = s.pulse ∧ t.choice = s.choice
    | .pulse, v => t.pulse = v ∧ t.hue = s.hue ∧ t.choice = s.choice
    | .choice, v => t.choice = some v ∧ t.hue = s.hue ∧ t.pulse = s.pulse
    | .gap, _ => False

theorem active_continues {s t k v} (h : Active s t k v) :
    Continues sites s t k v := by
  cases k with
  | hue =>
      obtain ⟨hclock, hloc, hhue, hpulse, hchoice⟩ := h
      refine ⟨?_, ?_, fun _ _ => trivial⟩
      · exact hhue.symm
      · intro k' v' hne
        cases k' with
        | hue => exact absurd rfl hne
        | pulse =>
            constructor
            · intro hp; exact hp.trans hpulse.symm
            · intro hp; exact hp.trans hpulse
        | choice =>
            constructor
            · intro hc; exact hchoice.trans hc
            · intro hc; exact hchoice.symm.trans hc
        | gap =>
            constructor
            · intro hg; exact False.elim hg
            · intro hg; exact False.elim hg
  | pulse =>
      obtain ⟨hclock, hloc, hpulse, hhue, hchoice⟩ := h
      refine ⟨?_, ?_, fun _ _ => trivial⟩
      · exact hpulse.symm
      · intro k' v' hne
        cases k' with
        | hue =>
            constructor
            · intro hh; exact hh.trans hhue.symm
            · intro hh; exact hh.trans hhue
        | pulse => exact absurd rfl hne
        | choice =>
            constructor
            · intro hc; exact hchoice.trans hc
            · intro hc; exact hchoice.symm.trans hc
        | gap =>
            constructor
            · intro hg; exact False.elim hg
            · intro hg; exact False.elim hg
  | choice =>
      obtain ⟨hclock, hloc, hch, hhue, hpulse⟩ := h
      refine ⟨?_, ?_, fun _ _ => trivial⟩
      · exact hch
      · intro k' v' hne
        cases k' with
        | hue =>
            constructor
            · intro hh; exact hh.trans hhue.symm
            · intro hh; exact hh.trans hhue
        | pulse =>
            constructor
            · intro hp; exact hp.trans hpulse.symm
            · intro hp; exact hp.trans hpulse
        | choice => exact absurd rfl hne
        | gap =>
            constructor
            · intro hg; exact False.elim hg
            · intro hg; exact False.elim hg
  | gap =>
      exact False.elim h.2.2

theorem active_advances {s t k v} (h : Active s t k v) :
    s.clock < t.clock := by
  have hc := h.1
  rw [hc]
  exact Nat.lt_succ_self _

abbrev dyn : Dynamics sites where
  Active := Active
  continues := active_continues
  rank := fun s => s.clock
  advances := active_advances

def stepPulse (s : St) (p : Pulse) : St :=
  { clock := s.clock + 1, loc := s.loc, hue := s.hue,
    pulse := p, choice := s.choice }

def stepHue (s : St) (h : Hue) : St :=
  { clock := s.clock + 1, loc := s.loc, hue := h,
    pulse := s.pulse, choice := s.choice }

def stepChoice (s : St) (c : Choice) : St :=
  { clock := s.clock + 1, loc := s.loc, hue := s.hue,
    pulse := s.pulse, choice := some c }

theorem active_pulse (s : St) (p : Pulse) :
    Active s (stepPulse s p) K.pulse p :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem active_hue (s : St) (h : Hue) :
    Active s (stepHue s h) K.hue h :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem active_choice (s : St) (c : Choice) :
    Active s (stepChoice s c) K.choice c :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem productive : dyn.Productive := by
  intro s
  exact ⟨stepPulse s Pulse.hi, K.pulse, Pulse.hi, active_pulse s Pulse.hi⟩

def origin : St :=
  { clock := 0, loc := false, hue := Hue.red, pulse := Pulse.lo,
    choice := none }

def elsewhere : St :=
  { clock := 0, loc := true, hue := Hue.blue, pulse := Pulse.hi,
    choice := none }

theorem origin_open_choice : sites.Open origin K.choice := by
  refine ⟨trivial, ?_⟩
  intro v h
  cases v <;> cases h

theorem origin_open_gap : sites.Open origin K.gap :=
  ⟨trivial, fun _ h => h⟩

theorem trichotomous_hue :
    ∃ a b c : Hue, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  refine ⟨Hue.red, Hue.green, Hue.blue, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h

theorem dichotomous_choice : ont.Dichotomous K.choice := by
  refine ⟨Choice.left, Choice.right, ?_, ?_⟩
  · intro h; cases h
  · intro c; cases c with
    | left => exact Or.inl rfl
    | right => exact Or.inr rfl

theorem richAt_origin_choice : dyn.RichAt origin K.choice := by
  refine ⟨origin_open_choice, ?_⟩
  intro v
  cases v with
  | left => exact ⟨stepChoice origin Choice.left, active_choice origin Choice.left⟩
  | right => exact ⟨stepChoice origin Choice.right, active_choice origin Choice.right⟩

def sel : Selector sites where
  choose := fun _s k =>
    match k with
    | .hue => Hue.red
    | .pulse => Pulse.hi
    | .choice => Choice.left
    | .gap => Gap.west

theorem possible_exceeds_selection :
    ¬ dyn.Respects sel :=
  dyn.richAt_exceeds_selector richAt_origin_choice
    (show Choice.left ≠ Choice.right from fun h => nomatch h) sel

/-- A completed history is supplied by the model, not derived from
productivity in the abstract. -/
def hist : Dynamics.History dyn where
  nth := fun n =>
    { clock := n, loc := false, hue := Hue.red, pulse := Pulse.hi,
      choice := none }
  step := fun n =>
    ⟨K.pulse, Pulse.hi, by
      dsimp [Active]
      refine ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

theorem hist_unbounded (n : Nat) :
    Chain dyn n (hist.nth 0) (hist.nth n) :=
  dyn.history_chain hist n

abbrev coexist : Coexistence dyn where
  together := fun s t => s.clock = t.clock
  refl := fun _ => rfl
  symm := fun h => h.symm
  not_time := by
    intro s t htog hear
    obtain ⟨n, hn, hc⟩ := hear
    have hlt : s.clock < t.clock := dyn.chain_pos_rank hc hn
    exact Nat.ne_of_lt hlt htog

theorem origin_elsewhere_together :
    coexist.together origin elsewhere :=
  rfl

theorem origin_elsewhere_not_earlier :
    ¬ dyn.Earlier origin elsewhere :=
  coexist.not_time origin_elsewhere_together

theorem two_step_earlier_not_direct :
    dyn.Earlier origin (stepPulse (stepPulse origin Pulse.hi) Pulse.lo) ∧
      ¬ dyn.Direct origin (stepPulse (stepPulse origin Pulse.hi) Pulse.lo) := by
  refine ⟨?_, ?_⟩
  · refine ⟨2, Nat.succ_ne_zero 1, ?_⟩
    have a1 : dyn.Active origin (stepPulse origin Pulse.hi) K.pulse Pulse.hi :=
      active_pulse origin Pulse.hi
    have a2 : dyn.Active (stepPulse origin Pulse.hi)
        (stepPulse (stepPulse origin Pulse.hi) Pulse.lo) K.pulse Pulse.lo :=
      active_pulse (stepPulse origin Pulse.hi) Pulse.lo
    have c0 : Chain dyn 0 origin origin := Chain.refl (D := dyn) origin
    have c1 : Chain dyn 1 origin (stepPulse origin Pulse.hi) :=
      Chain.step c0 a1
    exact Chain.step c1 a2
  · intro ⟨k, v, ha⟩
    have hclock : (stepPulse (stepPulse origin Pulse.hi) Pulse.lo).clock =
        origin.clock + 1 := ha.1
    simp [stepPulse, origin] at hclock

def appear : Appearance sites where
  Observer := Bool
  appears := fun o s k v =>
    o = s.loc ∧
      match k, v with
      | .hue, v => v = s.hue
      | .pulse, v => v = Pulse.hi
      | .choice, _ => False
      | .gap, _ => False

theorem veridical_hue :
    appear.Veridical origin.loc origin K.hue Hue.red :=
  ⟨⟨rfl, rfl⟩, rfl⟩

theorem illusory_pulse :
    appear.Illusion origin.loc origin K.pulse Pulse.hi :=
  ⟨⟨rfl, rfl⟩, by intro h; cases h⟩

def located : Appearance.Located appear where
  locOf := fun o s => o = s.loc
  only_located := fun h => h.1

/-- Gap is open at every site and is never a target.  Remainder need not
be the kind that plenitude works. -/
theorem gap_reserved (s : St) :
    sites.Open s K.gap ∧ ∀ t v, ¬ Active s t K.gap v :=
  ⟨⟨trivial, fun _ h => h⟩, fun _ _ h => h.2.2⟩

theorem hue_persists_across_pulse (s : St) (p : Pulse) :
    sites.realises (stepPulse s p) K.hue s.hue :=
  dyn.persists (k := K.pulse) (k' := K.hue) (v := p) (v' := s.hue)
    (active_pulse s p) (fun h => nomatch h) rfl

end World

/-! ## Axiom regression -/

/--
info: 'OpenSite.World.possible_exceeds_selection' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.possible_exceeds_selection

/--
info: 'OpenSite.World.hist' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.hist

/--
info: 'OpenSite.World.two_step_earlier_not_direct' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms World.two_step_earlier_not_direct

/--
info: 'OpenSite.World.illusory_pulse' does not depend on any axioms
-/
#guard_msgs in
#print axioms World.illusory_pulse

/-! ## What this does not close

Continuous magnitude, metric duration, geometry, embodiment as lived body,
and phenomenal character remain outside.  They are outside because they
need further primitives (an ordered field, a metric, a body-kind, a
phenomenological givenness relation), not because a binary field was too
narrow.  The point of the schema is that those primitives can be added
*as themselves*, and then one can see what they prove.

What is closed, relative to the old open list:

* Plural determination: `Hue` has three values; exclusivity still holds.
* Productivity ≠ completed infinite succession: `productive_unbounded`
  versus `History`.
* A formal future is just `Earlier` read in the other direction; it is
  not marked inside the source.
* Space as coexistence, disjoint from time.
* Causation as `Direct`, strictly stronger than `Earlier`.
* Observation that can fail.
-/

end OpenSite
