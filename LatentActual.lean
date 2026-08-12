import Init

/-!
# Latent–Actual, revision 9

Revision 8 discharged open non-exhaustiveness from the offer.  This revision
forces cadence alternation on actual runs (the swirl), replaces the toy void
witness with a full absolutely-null presentation layer, and drops
`native_decide` from the Stage model.

**Opposition-primitive, unlabelled.**  Fibres are `Z/2`-torsors; a gradient is
a choice of section.

**Seed and offer.**  Each act writes `seed q = d` and refreshes the offer to a
fresh open opposition distinct from `d`.  Cadence: `promoteNext q ↔ ¬ OpenIn p d`
— promote then turn, turn then promote.

**Index.**  If `promoteNext p`, select at `offer p`; else select at
`(seed p).opp` (the contrary, under the seeded selector).  Actuality both
reverses and settles new content.

Compiles under plain Lean 4 core (checked on 4.22.0).  No `axiom`, no `sorry`,
and no `native_decide`: `#print axioms` reports at most `propext` and
`Quot.sound`.
-/

namespace LatentActual

universe u v

/-! ## 0. Exclusive disjunction -/

def ExactlyOne (a b : Prop) : Prop := (a ∧ ¬ b) ∨ (b ∧ ¬ a)

namespace ExactlyOne

variable {a b : Prop}

theorem not_both (h : ExactlyOne a b) : ¬ (a ∧ b) := by
  intro hab
  cases h with
  | inl h => exact h.2 hab.2
  | inr h => exact h.2 hab.1

theorem not_right_of_left (h : ExactlyOne a b) (ha : a) : ¬ b := by
  intro hb; exact not_both h ⟨ha, hb⟩

theorem not_left_of_right (h : ExactlyOne a b) (hb : b) : ¬ a := by
  intro ha; exact not_both h ⟨ha, hb⟩

theorem right_of_not_left (h : ExactlyOne a b) (ha : ¬ a) : b := by
  cases h with
  | inl h => exact absurd h.1 ha
  | inr h => exact h.1

end ExactlyOne

/-! ## 1. Field, opposition-primitive and unlabelled -/

structure Field where
  Opposition : Type u
  Pole : Opposition → Type u
  flip : ∀ {o : Opposition}, Pole o → Pole o
  flip_involutive : ∀ {o : Opposition} (p : Pole o), flip (flip p) = p
  flip_free : ∀ {o : Opposition} (p : Pole o), flip p ≠ p
  pole_dichotomy : ∀ {o : Opposition} (p q : Pole o), p = q ∨ p = flip q
  decEqPole : ∀ o, DecidableEq (Pole o)
  decEqOpp : DecidableEq Opposition

namespace Field

variable (F : Field.{u})

structure Determination where
  opp : F.Opposition
  pole : F.Pole opp

instance instDecidableEqDetermination : DecidableEq F.Determination := fun d e =>
  match F.decEqOpp d.opp e.opp with
  | isTrue h =>
      match F.decEqPole e.opp (h ▸ d.pole) e.pole with
      | isTrue h₂ =>
          isTrue (by cases d; cases e; cases h; cases h₂; rfl)
      | isFalse h₂ =>
          isFalse (by intro he; cases d; cases e; cases he; exact h₂ rfl)
  | isFalse h =>
      isFalse (by intro he; cases he; exact h rfl)

def neg (d : F.Determination) : F.Determination :=
  ⟨d.opp, F.flip d.pole⟩

theorem neg_involutive (d : F.Determination) : F.neg (F.neg d) = d := by
  cases d with
  | mk o p =>
      show Determination.mk o (F.flip (F.flip p)) = Determination.mk o p
      rw [F.flip_involutive]

theorem neg_free (d : F.Determination) : F.neg d ≠ d := by
  cases d with
  | mk o p =>
      intro h
      injection h with _ hp
      exact F.flip_free p hp

/-- Same opposition. -/
def Opposed (d e : F.Determination) : Prop := d.opp = e.opp

theorem opposed_iff_opp_eq (d e : F.Determination) :
    F.Opposed d e ↔ d.opp = e.opp := Iff.rfl

theorem opposed_refl (d : F.Determination) : F.Opposed d d := rfl

theorem opposed_neg (d : F.Determination) : F.Opposed d (F.neg d) := rfl

theorem opposed_neg_left {d e : F.Determination} :
    F.Opposed (F.neg d) e ↔ F.Opposed d e := by
  cases d; cases e; exact Iff.rfl

theorem opposed_symm {d e : F.Determination} (h : F.Opposed d e) :
    F.Opposed e d := h.symm

theorem eq_or_neg (d e : F.Determination) (h : F.Opposed d e) :
    e = d ∨ e = F.neg d := by
  cases d with
  | mk o p =>
      cases e with
      | mk o' q =>
          cases h
          cases F.pole_dichotomy q p with
          | inl he => exact Or.inl (by cases he; rfl)
          | inr he => exact Or.inr (by cases he; rfl)

theorem opposed_em (d e : F.Determination) :
    F.Opposed d e ∨ ¬ F.Opposed d e := by
  cases F.decEqOpp d.opp e.opp with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

/-- A gradient is a dependent section — a choice from unlabelled fibres. -/
structure Polarisation where
  choose : ∀ o, F.Pole o

def Orientable : Prop := Nonempty F.Polarisation

namespace Polarisation

variable {F}

def exchange (S : F.Polarisation) : F.Polarisation where
  choose := fun o => F.flip (S.choose o)

theorem exchange_exchange (S : F.Polarisation) :
    S.exchange.exchange = S := by
  cases S; simp only [exchange]; congr; funext o; exact F.flip_involutive _

def atOpp (S : F.Polarisation) (o : F.Opposition) : F.Determination :=
  ⟨o, S.choose o⟩

end Polarisation

theorem fixedPointFree : ∀ d : F.Determination, F.neg d ≠ d :=
  F.neg_free

end Field

/-! ## 2. Articulation, resolution, realisation, trace, seed -/

structure PresentationLayer (F : Field.{u}) where
  Presentation : Type v
  articulates : Presentation → F.Determination → Prop
  Resolves : Presentation → F.Determination → Prop
  realises : Presentation → F.Determination → Prop
  trace : Presentation → F.Determination
  seed : Presentation → F.Determination
  /-- A fresh open opposition offered for promotion into the seed. -/
  offer : Presentation → F.Opposition
  /-- Cadence bit: if true, the next act promotes the offer; if false, it turns
  the seed. -/
  promoteNext : Presentation → Bool
  articulates_neg : ∀ {p d}, articulates p d → articulates p (F.neg d)
  resolves_neg : ∀ {p d}, Resolves p d → Resolves p (F.neg d)
  resolves_articulates : ∀ {p d}, Resolves p d → articulates p d
  realises_resolves : ∀ {p d}, realises p d → Resolves p d
  resolution_orients : ∀ {p d}, Resolves p d →
    ExactlyOne (realises p d) (realises p (F.neg d))
  trace_fresh : ∀ p, ¬ articulates p (trace p)
  /-- The offer is open. -/
  offer_open : ∀ p, ∃ pol, articulates p ⟨offer p, pol⟩ ∧ ¬ Resolves p ⟨offer p, pol⟩
  /-- The offer is not the seed's opposition. -/
  offer_ne_seed : ∀ p, offer p ≠ (seed p).opp

namespace PresentationLayer

variable {F : Field.{u}} (P : PresentationLayer.{u,v} F)

def HasRealisation (p : P.Presentation) : Prop := ∃ d, P.realises p d

def AbsolutelyNull (p : P.Presentation) : Prop := ∀ d, ¬ P.realises p d

theorem realises_articulates {p : P.Presentation} {d : F.Determination}
    (h : P.realises p d) : P.articulates p d :=
  P.resolves_articulates (P.realises_resolves h)

theorem resolves_iff_pole {p : P.Presentation} {d : F.Determination} :
    P.Resolves p d ↔ (P.realises p d ∨ P.realises p (F.neg d)) := by
  constructor
  · intro h
    cases P.resolution_orients h with
    | inl hl => exact Or.inl hl.1
    | inr hr => exact Or.inr hr.1
  · intro h
    cases h with
    | inl hl => exact P.realises_resolves hl
    | inr hr =>
        have := P.resolves_neg (P.realises_resolves hr)
        rw [F.neg_involutive] at this
        exact this

theorem not_realises_neg {p : P.Presentation} {d : F.Determination}
    (h : P.realises p d) : ¬ P.realises p (F.neg d) :=
  (P.resolution_orients (P.realises_resolves h)).not_right_of_left h

def LatentIn (p : P.Presentation) (d : F.Determination) : Prop := ¬ P.realises p d

def ExcludedIn (p : P.Presentation) (d : F.Determination) : Prop :=
  P.realises p (F.neg d)

def OpenIn (p : P.Presentation) (d : F.Determination) : Prop :=
  P.articulates p d ∧ ¬ P.Resolves p d

def UndrawnIn (p : P.Presentation) (d : F.Determination) : Prop :=
  ¬ P.articulates p d

def OpenOpp (p : P.Presentation) (o : F.Opposition) : Prop :=
  ∃ pol : F.Pole o, P.OpenIn p ⟨o, pol⟩

/-- `d` may be settled at `p`: either the opposition is open, or settling `d`
would turn a realised contrary (the seed case). -/
def Available (p : P.Presentation) (d : F.Determination) : Prop :=
  P.OpenIn p d ∨ P.realises p (F.neg d)

theorem available_of_open {p : P.Presentation} {d : F.Determination}
    (h : P.OpenIn p d) : P.Available p d := Or.inl h

theorem available_of_turn {p : P.Presentation} {d : F.Determination}
    (h : P.realises p (F.neg d)) : P.Available p d := Or.inr h

theorem available_neg_of_realises {p : P.Presentation} {d : F.Determination}
    (h : P.realises p d) : P.Available p (F.neg d) := by
  refine Or.inr ?_
  rw [F.neg_involutive]
  exact h

theorem excluded_latent {p : P.Presentation} {d : F.Determination}
    (h : P.ExcludedIn p d) : P.LatentIn p d := by
  intro hr; exact P.not_realises_neg hr h

theorem open_latent {p : P.Presentation} {d : F.Determination}
    (h : P.OpenIn p d) : P.LatentIn p d :=
  fun hr => h.2 (P.realises_resolves hr)

theorem undrawn_latent {p : P.Presentation} {d : F.Determination}
    (h : P.UndrawnIn p d) : P.LatentIn p d :=
  fun hr => h (P.realises_articulates hr)

theorem open_neg {p : P.Presentation} {d : F.Determination}
    (h : P.OpenIn p d) : P.OpenIn p (F.neg d) := by
  refine ⟨P.articulates_neg h.1, ?_⟩
  intro hres
  have := P.resolves_neg hres
  rw [F.neg_involutive] at this
  exact h.2 this

def StatusEqOn (p q : P.Presentation) : Prop :=
  ∀ d, P.articulates p d → (P.realises p d ↔ P.realises q d)

theorem statusEqOn_refl (p : P.Presentation) : P.StatusEqOn p p :=
  fun _ _ => Iff.rfl

def NullityFailure : Prop := ∀ p, P.HasRealisation p

/-- Realising every seed discharges absolute nullity. -/
theorem nullityFailure_of_seed_realised
    (h : ∀ p, P.realises p (P.seed p)) : P.NullityFailure :=
  fun p => ⟨P.seed p, h p⟩

def OpenNonExhaustive : Prop := ∀ p, ∃ d, P.OpenIn p d

/-- The offer is open at every presentation, so openness is never exhausted. -/
theorem openNonExhaustive_of_offer : P.OpenNonExhaustive := by
  intro p
  obtain ⟨pol, ha, hr⟩ := P.offer_open p
  exact ⟨⟨P.offer p, pol⟩, ha, hr⟩

def ArticulativeNonExhaustive : Prop := ∀ p, ∃ d, P.UndrawnIn p d

def FullResolution : Prop := ∀ p d, P.articulates p d → P.Resolves p d

theorem fullResolution_openNonExhaustive_inconsistent
    (p : P.Presentation) (h₁ : P.FullResolution) (h₂ : P.OpenNonExhaustive) :
    False := by
  cases h₂ p with
  | intro d hd => exact hd.2 (h₁ p d hd.1)

theorem fullResolution_inconsistent_of_offer
    (p : P.Presentation) (h : P.FullResolution) : False :=
  P.fullResolution_openNonExhaustive_inconsistent p h P.openNonExhaustive_of_offer

theorem articulativeNonExhaustive : P.ArticulativeNonExhaustive :=
  fun p => ⟨P.trace p, P.trace_fresh p⟩

structure Continues (p q : P.Presentation) (d : F.Determination) : Prop where
  pole : P.realises q d
  off : ∀ (o : F.Opposition), o ≠ d.opp →
    ∀ (pol : F.Pole o),
      P.articulates p ⟨o, pol⟩ →
        (P.realises q ⟨o, pol⟩ ↔ P.realises p ⟨o, pol⟩)
  resolution : ∀ e, P.Resolves p e → P.Resolves q e
  articulation : ∀ e, P.articulates p e → P.articulates q e
  carries : P.realises q (P.trace p)
  seeded : P.seed q = d
  /-- After promoting (settling something open), next turns; after turning,
  next promotes. -/
  cadence : (P.promoteNext q = true) ↔ ¬ P.OpenIn p d
  /-- The refreshed offer avoids the opposition just settled. -/
  offer_avoid : P.offer q ≠ d.opp

namespace Continues

variable {P}

theorem excludes {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : ¬ P.realises q (F.neg d) :=
  P.not_realises_neg h.pole

theorem articulates_trace {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : P.articulates q (P.trace p) :=
  P.realises_articulates h.carries

theorem off_determination {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) (e : F.Determination) (hne : ¬ F.Opposed d e)
    (he : P.articulates p e) :
    P.realises q e ↔ P.realises p e := by
  cases e with
  | mk o pol =>
      have : o ≠ d.opp := fun heq => hne heq.symm
      exact h.off o this pol he

theorem agree_on_drawn {p q q' : P.Presentation} {d : F.Determination}
    (h₁ : Continues P p q d) (h₂ : Continues P p q' d) :
    ∀ e, P.articulates p e → (P.realises q e ↔ P.realises q' e) := by
  intro e he
  cases F.opposed_em d e with
  | inr hne =>
      exact Iff.trans (h₁.off_determination e hne he)
        (h₂.off_determination e hne he).symm
  | inl hopp =>
      cases F.eq_or_neg d e hopp with
      | inl heq =>
          subst heq
          exact ⟨fun _ => h₂.pole, fun _ => h₁.pole⟩
      | inr heq =>
          subst heq
          exact ⟨fun hx => absurd hx h₁.excludes,
                 fun hx => absurd hx h₂.excludes⟩

/-- Weak reading: realising a pole articulates its contrary. Exclusion is not
deletion. -/
theorem seed_articulates_contrary {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : P.articulates q (F.neg d) :=
  P.articulates_neg (P.realises_articulates h.pole)

end Continues

end PresentationLayer

/-! ## 3. Generation -/

structure GenerativeLayer {F : Field.{u}} (P : PresentationLayer.{u,v} F) where
  Active : P.Presentation → P.Presentation → F.Determination → Prop
  active_continues : ∀ {p q d}, Active p q d → P.Continues p q d

inductive Chain {F : Field.{u}} {P : PresentationLayer.{u,v} F}
    (G : GenerativeLayer P) : Nat → P.Presentation → P.Presentation → Prop
  | refl (p : P.Presentation) : Chain G 0 p p
  | step {n : Nat} {p q r : P.Presentation} {d : F.Determination} :
      Chain G n p q → G.Active q r d → Chain G (n + 1) p r

namespace GenerativeLayer

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F}
variable (G : GenerativeLayer P)

def Generates (p q : P.Presentation) : Prop := ∃ d, G.Active p q d

def Productive : Prop := ∀ p, ∃ q, G.Generates p q

theorem two_acts_restore {p q r : P.Presentation} {d : F.Determination}
    (h₁ : G.Active p q (F.neg d)) (h₂ : G.Active q r d)
    (hp : P.realises p d) : P.StatusEqOn p r := by
  have c₁ := G.active_continues h₁
  have c₂ := G.active_continues h₂
  intro e he
  cases F.opposed_em d e with
  | inr hne =>
      have hq : P.articulates q e := c₁.articulation e he
      have s₂ := c₂.off_determination e hne hq
      have s₁ := c₁.off_determination e
        (fun hopp => hne (F.opposed_neg_left.1 hopp)) he
      exact (Iff.trans s₂ s₁).symm
  | inl hopp =>
      cases F.eq_or_neg d e hopp with
      | inl heq => subst heq; exact ⟨fun _ => c₂.pole, fun _ => hp⟩
      | inr heq =>
          subst heq
          exact ⟨fun hx => absurd hx (P.not_realises_neg hp),
                 fun hx => absurd hx c₂.excludes⟩

theorem chain_preserves_articulation :
    ∀ {n : Nat} {p q : P.Presentation}, Chain G n p q →
      ∀ e, P.articulates p e → P.articulates q e := by
  intro n p q h
  induction h with
  | refl p => intro e he; exact he
  | @step n p q r d c a ih =>
      intro e he
      exact (G.active_continues a).articulation e (ih e he)

theorem chain_head : ∀ {n : Nat} {p q : P.Presentation}, Chain G (n + 1) p q →
    ∃ r e, G.Active p r e := by
  intro n
  induction n with
  | zero =>
      intro p q h
      cases h with
      | step c a => cases c with | refl _ => exact ⟨_, _, a⟩
  | succ k ih =>
      intro p q h
      cases h with | step c a => exact ih c

theorem active_seed {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : P.seed q = d :=
  (G.active_continues h).seeded

end GenerativeLayer

/-! ## 4. The archive -/

namespace Archive

variable {F : Field.{u}} (P : PresentationLayer.{u,v} F)

def Precedes (p q : P.Presentation) : Prop :=
  (∀ d, P.articulates p d → P.articulates q d) ∧ P.articulates q (P.trace p)

theorem precedes_irrefl (p : P.Presentation) : ¬ Precedes P p p :=
  fun h => P.trace_fresh p h.2

theorem precedes_trans {p q r : P.Presentation}
    (h₁ : Precedes P p q) (h₂ : Precedes P q r) : Precedes P p r :=
  ⟨fun d hd => h₂.1 d (h₁.1 d hd), h₂.1 _ h₁.2⟩

variable {G : GenerativeLayer P}

theorem active_precedes {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : Precedes P p q :=
  ⟨(G.active_continues h).articulation, (G.active_continues h).articulates_trace⟩

theorem chain_precedes : ∀ {n : Nat} {p q : P.Presentation},
    Chain G (n + 1) p q → Precedes P p q := by
  intro n
  induction n with
  | zero =>
      intro p q h
      cases h with
      | step c a => cases c with | refl _ => exact active_precedes P a
  | succ k ih =>
      intro p q h
      cases h with
      | step c a => exact precedes_trans P (ih c) (active_precedes P a)

theorem no_cycle {n : Nat} {p : P.Presentation} : ¬ Chain G (n + 1) p p :=
  fun h => precedes_irrefl P p (chain_precedes P h)

theorem active_no_return {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : p ≠ q := by
  intro he
  have hp := active_precedes P h
  rw [he] at hp
  exact precedes_irrefl P q hp

theorem trace_distinguishes {p q : P.Presentation} (h : Precedes P p q) :
    P.trace p ≠ P.trace q := by
  intro he
  exact P.trace_fresh q (by rw [← he]; exact h.2)

theorem recurrence_without_return {p q r : P.Presentation} {d : F.Determination}
    (h₁ : G.Active p q (F.neg d)) (h₂ : G.Active q r d) (hp : P.realises p d) :
    P.StatusEqOn p r ∧ Precedes P p r :=
  ⟨G.two_acts_restore h₁ h₂ hp,
    precedes_trans P (active_precedes P h₁) (active_precedes P h₂)⟩

end Archive

/-! ## 5. Observers -/

structure ObserverLayer {F : Field.{u}} (P : PresentationLayer.{u,v} F) where
  IsObserver : F.Determination → Prop
  AppearsTo : P.Presentation → F.Determination → F.Determination → Prop
  observer_is_realised : ∀ {p o d}, AppearsTo p o d → P.realises p o
  observed_is_realised : ∀ {p o d}, AppearsTo p o d → P.realises p d

namespace ObserverLayer

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F} (O : ObserverLayer P)

theorem not_appears_both {p o d}
    (h₁ : O.AppearsTo p o d) (h₂ : O.AppearsTo p o (F.neg d)) : False :=
  P.not_realises_neg (O.observed_is_realised h₁) (O.observed_is_realised h₂)

theorem not_appears_open {p o d} (h : O.AppearsTo p o d) : ¬ P.OpenIn p d :=
  fun ho => ho.2 (P.realises_resolves (O.observed_is_realised h))

def Registers (q p : P.Presentation) : Prop := P.articulates q (P.trace p)

variable {G : GenerativeLayer P}

theorem registers_of_chain {n : Nat} {p q : P.Presentation}
    (h : Chain G (n + 1) p q) : Registers q p := (Archive.chain_precedes P h).2

theorem registers_asymm {p q : P.Presentation}
    (h : Archive.Precedes P p q) : ¬ Registers p q :=
  fun hr => P.trace_fresh q (h.1 _ hr)

end ObserverLayer

/-! ## 6. Selection via the seed -/

structure Selector {F : Field.{u}} (P : PresentationLayer.{u,v} F) where
  select : P.Presentation → F.Opposition → F.Determination
  select_opp : ∀ p o, (select p o).opp = o

namespace Selector

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F} (S : Selector P)

def selectDet (p : P.Presentation) (d : F.Determination) : F.Determination :=
  S.select p d.opp

theorem selectDet_opp (p : P.Presentation) (d : F.Determination) :
    (S.selectDet p d).opp = d.opp :=
  S.select_opp p d.opp

theorem selectDet_pole (p : P.Presentation) (d : F.Determination) :
    S.selectDet p d = d ∨ S.selectDet p d = F.neg d := by
  have hopp : F.Opposed d (S.selectDet p d) := (S.selectDet_opp p d).symm
  cases F.eq_or_neg d (S.selectDet p d) hopp with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

theorem selectDet_coherent (p : P.Presentation) (d : F.Determination) :
    S.selectDet p (F.neg d) = S.selectDet p d := rfl

theorem selectDet_idem (p : P.Presentation) (d : F.Determination) :
    S.selectDet p (S.selectDet p d) = S.selectDet p d := by
  change S.select p (S.select p d.opp).opp = S.select p d.opp
  rw [S.select_opp p d.opp]

theorem open_select {p : P.Presentation} {d : F.Determination}
    (h : P.OpenIn p d) : P.OpenIn p (S.selectDet p d) := by
  cases S.selectDet_pole p d with
  | inl he => rw [he]; exact h
  | inr he => rw [he]; exact P.open_neg h

def ofPolarisation (T : F.Polarisation) : Selector P where
  select := fun _ o => T.atOpp o
  select_opp := fun _ _ => rfl

theorem eq_rec_eq_self {α : Sort u} {a : α} {β : α → Sort v}
    (x : β a) (h : a = a) : h ▸ x = x := rfl

/-- Pole chosen at `o` by reading the seed. -/
def seedSelectPole (T : F.Polarisation) (p : P.Presentation) (o : F.Opposition) :
    F.Pole o :=
  match F.decEqOpp (P.seed p).opp o with
  | isTrue h => h ▸ F.flip (P.seed p).pole
  | isFalse _ => T.choose o

def seedSelect (T : F.Polarisation) (p : P.Presentation) (o : F.Opposition) :
    F.Determination :=
  ⟨o, seedSelectPole T p o⟩

/-- Seeded selector: at the seed's opposition take the contrary; else the base. -/
def ofSeed (T : F.Polarisation) : Selector P where
  select := seedSelect T
  select_opp := fun _ _ => rfl

theorem seedSelectPole_at_seed (T : F.Polarisation) (p : P.Presentation) :
    seedSelectPole T p (P.seed p).opp = F.flip (P.seed p).pole := by
  unfold seedSelectPole
  cases h : F.decEqOpp (P.seed p).opp (P.seed p).opp with
  | isFalse h' => exact absurd rfl h'
  | isTrue h' => exact eq_rec_eq_self (F.flip (P.seed p).pole) h'

theorem seed_turns (T : F.Polarisation) {p q : P.Presentation}
    {d : F.Determination} (h : P.Continues p q d) :
    (ofSeed T : Selector P).select q d.opp = F.neg d := by
  have hs : P.seed q = d := h.seeded
  subst hs
  simp only [ofSeed, seedSelect, Field.neg]
  rw [seedSelectPole_at_seed T q]

theorem seed_turns_det (T : F.Polarisation) {p q : P.Presentation}
    {d : F.Determination} (h : P.Continues p q d) :
    (ofSeed T : Selector P).selectDet q d = F.neg d :=
  seed_turns T h

def Uniform : Prop := ∀ p q o, S.select p o = S.select q o

theorem ofPolarisation_uniform (T : F.Polarisation) :
    (ofPolarisation T : Selector P).Uniform := fun _ _ _ => rfl

def Respected (G : GenerativeLayer P) : Prop :=
  ∀ {p q d}, G.Active p q d → S.selectDet p d = d

end Selector

/-! ## 7. Possibility, plenitude, productivity -/

namespace Possibility

variable {F : Field.{u}} (P : PresentationLayer.{u,v} F)

def inert : GenerativeLayer P where
  Active := fun _ _ _ => False
  active_continues := fun h => False.elim h

theorem inert_not_productive (p₀ : P.Presentation) : ¬ (inert P).Productive := by
  intro h
  cases h p₀ with
  | intro q hq => cases hq with | intro d hd => exact hd

theorem productivity_is_not_presentation_level (p₀ : P.Presentation) :
    ∃ G : GenerativeLayer P, ¬ G.Productive :=
  ⟨inert P, inert_not_productive P p₀⟩

def full : GenerativeLayer P where
  Active := fun p q d => P.Continues p q d
  active_continues := fun h => h

/-- Continuations for open settlements, and always a turn of the seed.  The
seed-turn clause is what focus-as-seed needs; it does not require every
realised pole (e.g. a pure name) to be flippable. -/
structure Rich : Prop where
  open_cont : ∀ p d, P.OpenIn p d → ∃ q, P.Continues p q d
  seed_turn : ∀ p, ∃ q, P.Continues p q (F.neg (P.seed p))

variable {P}

def Extends (G G' : GenerativeLayer P) : Prop :=
  ∀ p q d, G.Active p q d → G'.Active p q d

theorem extends_full (G : GenerativeLayer P) : Extends G (full P) :=
  fun _ _ _ h => G.active_continues h

def Maximal (G : GenerativeLayer P) : Prop :=
  ∀ G', Extends G G' → Extends G' G

theorem full_maximal : Maximal (full P) :=
  fun G' _ p q d h => extends_full G' p q d h

/-- Productivity from plenitude via the seed turn. -/
theorem productive_of_plenitude {G : GenerativeLayer P}
    (hmax : Maximal G) (hrich : Rich P) :
    G.Productive := by
  intro p
  cases hrich.seed_turn p with
  | intro q hq =>
      exact ⟨q, ⟨F.neg (P.seed p),
        hmax (full P) (extends_full G) p q (F.neg (P.seed p)) hq⟩⟩

theorem plenitude_excludes_selection {G : GenerativeLayer P}
    (S : Selector P)
    (hmax : Maximal G) (hrich : Rich P) (hopen : P.OpenNonExhaustive)
    (p₀ : P.Presentation) : ¬ S.Respected G := by
  intro hresp
  cases hopen p₀ with
  | intro d hd =>
      cases hrich.open_cont p₀ d hd with
      | intro q hq =>
          cases hrich.open_cont p₀ (F.neg d) (P.open_neg hd) with
          | intro q' hq' =>
              have a₁ : G.Active p₀ q d :=
                hmax (full P) (extends_full G) p₀ q d hq
              have a₂ : G.Active p₀ q' (F.neg d) :=
                hmax (full P) (extends_full G) p₀ q' (F.neg d) hq'
              have e₁ : S.selectDet p₀ d = d := hresp a₁
              have e₂ : S.selectDet p₀ (F.neg d) = F.neg d := hresp a₂
              have hc : S.selectDet p₀ (F.neg d) = S.selectDet p₀ d :=
                S.selectDet_coherent p₀ d
              rw [e₁, e₂] at hc
              exact F.neg_free d hc

end Possibility

/-! ## 8. Actuality -/

namespace Selector

open Possibility

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F} (S : Selector P)

def actual (G : GenerativeLayer P) : GenerativeLayer P where
  Active := fun p q d => G.Active p q d ∧ S.selectDet p d = d
  active_continues := fun h => G.active_continues h.1

theorem actual_respected (G : GenerativeLayer P) : S.Respected (S.actual G) :=
  fun h => h.2

theorem actual_productive {G : GenerativeLayer P}
    (hmax : Maximal G) (hrich : Rich P)
    (hsel : ∀ p, S.selectDet p (F.neg (P.seed p)) = F.neg (P.seed p)) :
    (S.actual G).Productive := by
  intro p
  cases hrich.seed_turn p with
  | intro q hq =>
      exact ⟨q, ⟨F.neg (P.seed p),
        ⟨hmax (full P) (extends_full G) p q (F.neg (P.seed p)) hq,
         hsel p⟩⟩⟩

theorem actual_pole_determinate {G : GenerativeLayer P}
    {p q q' : P.Presentation} {d e : F.Determination}
    (h₁ : (S.actual G).Active p q d) (h₂ : (S.actual G).Active p q' e)
    (hopp : F.Opposed d e) : d = e := by
  cases F.eq_or_neg d e hopp with
  | inl he => exact he.symm
  | inr he =>
      subst he
      have hc : S.selectDet p (F.neg d) = S.selectDet p d :=
        S.selectDet_coherent p d
      rw [h₂.2, h₁.2] at hc
      exact absurd hc (F.neg_free d)

theorem actual_target_determinate {G : GenerativeLayer P}
    {p q q' : P.Presentation} {d : F.Determination}
    (h₁ : (S.actual G).Active p q d) (h₂ : (S.actual G).Active p q' d) :
    ∀ e, P.articulates p e → (P.realises q e ↔ P.realises q' e) :=
  ((S.actual G).active_continues h₁).agree_on_drawn
    ((S.actual G).active_continues h₂)

end Selector

/-! ### Index: promote the offer, or turn the seed

No free focus map.  The cadence bit chooses the regime; the seed and offer
supply the opposition.  Under the seeded selector, turning yields the contrary
of the seed; promoting yields the gradient's pole at the offer. -/

structure Focus {F : Field.{u}} (P : PresentationLayer.{u,v} F) where
  selector : Selector P
  seed_realised : ∀ p, P.realises p (P.seed p)
  /-- At the seed's opposition, selection is the contrary. -/
  turns : ∀ p, selector.select p (P.seed p).opp = F.neg (P.seed p)

namespace Focus

open Possibility

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F}

/-- The opposition under consideration: offer if promoting, else seed. -/
def focusOpp (Φ : Focus P) (p : P.Presentation) : F.Opposition :=
  if P.promoteNext p then P.offer p else (P.seed p).opp

variable (Φ : Focus P)

/-- The determination an act from `p` settles. -/
def index (p : P.Presentation) : F.Determination :=
  Φ.selector.select p (Φ.focusOpp p)

theorem index_turn (p : P.Presentation) (h : P.promoteNext p = false) :
    Φ.index p = F.neg (P.seed p) := by
  simp only [index, focusOpp, h]
  exact Φ.turns p

theorem index_promote_opp (p : P.Presentation) (h : P.promoteNext p = true) :
    (Φ.index p).opp = P.offer p := by
  simp only [index, focusOpp, h, ↓reduceIte]
  exact Φ.selector.select_opp p (P.offer p)

theorem index_opp (p : P.Presentation) : (Φ.index p).opp = Φ.focusOpp p :=
  Φ.selector.select_opp p (Φ.focusOpp p)

theorem select_index (p : P.Presentation) :
    Φ.selector.selectDet p (Φ.index p) = Φ.index p := by
  simp only [Selector.selectDet, index]
  rw [Φ.selector.select_opp p (Φ.focusOpp p)]

def actual (G : GenerativeLayer P) : GenerativeLayer P where
  Active := fun p q d => G.Active p q d ∧ d = Φ.index p
  active_continues := fun h => G.active_continues h.1

theorem actual_respected (G : GenerativeLayer P) :
    Φ.selector.Respected (Φ.actual G) := by
  intro p q d h
  rw [h.2]
  exact Φ.select_index p

theorem actual_productive {G : GenerativeLayer P}
    (hmax : Maximal G) (hrich : Rich P) :
    (Φ.actual G).Productive := by
  intro p
  cases hp : P.promoteNext p with
  | true =>
      obtain ⟨pol, ha, hr⟩ := P.offer_open p
      have hOpen : P.OpenIn p ⟨P.offer p, pol⟩ := ⟨ha, hr⟩
      have : Φ.index p = Φ.selector.selectDet p ⟨P.offer p, pol⟩ := by
        simp only [Selector.selectDet, index, focusOpp, hp, ↓reduceIte]
      have hOpen' : P.OpenIn p (Φ.index p) := by
        rw [this]; exact Φ.selector.open_select hOpen
      cases hrich.open_cont p (Φ.index p) hOpen' with
      | intro q hq =>
          exact ⟨q, ⟨Φ.index p,
            hmax (full P) (extends_full G) p q (Φ.index p) hq, rfl⟩⟩
  | false =>
      cases hrich.seed_turn p with
      | intro q hq =>
          have hi : Φ.index p = F.neg (P.seed p) := Φ.index_turn p hp
          exact ⟨q, ⟨Φ.index p,
            ⟨by rw [hi]; exact hmax (full P) (extends_full G) p q
                  (F.neg (P.seed p)) hq, rfl⟩⟩⟩

theorem actual_index_unique {G : GenerativeLayer P}
    {p q q' : P.Presentation} {d d' : F.Determination}
    (h₁ : (Φ.actual G).Active p q d) (h₂ : (Φ.actual G).Active p q' d') :
    d = d' := by rw [h₁.2, h₂.2]

theorem actual_target_determinate {G : GenerativeLayer P}
    {p q q' : P.Presentation} {d d' : F.Determination}
    (h₁ : (Φ.actual G).Active p q d) (h₂ : (Φ.actual G).Active p q' d') :
    ∀ e, P.articulates p e → (P.realises q e ↔ P.realises q' e) := by
  have he : d' = d := (Φ.actual_index_unique h₁ h₂).symm
  subst he
  exact ((Φ.actual G).active_continues h₁).agree_on_drawn
    ((Φ.actual G).active_continues h₂)

/-- When the middle presentation is in turn cadence, consecutive actual acts
reverse. -/
theorem actual_reverses_of_turn {G : GenerativeLayer P}
    {p q r : P.Presentation} {d e : F.Determination}
    (h₁ : (Φ.actual G).Active p q d) (h₂ : (Φ.actual G).Active q r e)
    (hturn : P.promoteNext q = false) :
    e = F.neg d := by
  have hs : P.seed q = d := (Φ.actual G).active_continues h₁ |>.seeded
  have he : e = Φ.index q := h₂.2
  have hi : Φ.index q = F.neg (P.seed q) := Φ.index_turn q hturn
  rw [he, hi, hs]

/-- When promoting, the act settles a pole of the offer. -/
theorem actual_promotes {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hp : P.promoteNext p = true) :
    d.opp = P.offer p := by
  have hd : d = Φ.index p := h.2
  rw [hd]
  exact Φ.index_promote_opp p hp

/-- After promoting (settling something open), cadence demands a turn next. -/
theorem actual_cadence_after_promote {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hopen : P.OpenIn p d) :
    P.promoteNext q = false := by
  have hc := (Φ.actual G).active_continues h
  cases hpn : P.promoteNext q with
  | false => rfl
  | true => exact absurd hopen (hc.cadence.mp hpn)

/-- After turning (settling the contrary of a realised pole), cadence demands
promotion next. -/
theorem actual_cadence_after_turn {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hreal : P.realises p (F.neg d)) :
    P.promoteNext q = true := by
  have hc := (Φ.actual G).active_continues h
  refine hc.cadence.mpr ?_
  intro hopen
  have hres : P.Resolves p d := by
    have := P.resolves_neg (P.realises_resolves hreal)
    rw [F.neg_involutive] at this
    exact this
  exact hopen.2 hres

theorem actual_seed {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) : P.seed q = d :=
  (Φ.actual G).active_continues h |>.seeded

/-- Actual acts alternate the cadence: a promotion is always followed by a
turn.  The cadence field of `Continues` is a constraint; on actual runs it is
forced, because the index at a promoting presentation is a pole of the offer,
and the offer is open. -/
theorem actual_alternates_promote {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hp : P.promoteNext p = true) :
    P.promoteNext q = false := by
  obtain ⟨pol, ha, hr⟩ := P.offer_open p
  have hidx : d = Φ.selector.selectDet p ⟨P.offer p, pol⟩ := by
    rw [h.2]
    simp only [Selector.selectDet, index, focusOpp, hp, ↓reduceIte]
  have hOpen : P.OpenIn p d := by
    rw [hidx]; exact Φ.selector.open_select ⟨ha, hr⟩
  cases hpn : P.promoteNext q with
  | false => rfl
  | true => exact absurd hOpen (((Φ.actual G).active_continues h).cadence.mp hpn)

/-- And a turn is always followed by a promotion.  This is where
`seed_realised` does its work: the seed is effective, so its opposition is
settled, so turning it is not the settling of anything open. -/
theorem actual_alternates_turn {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hp : P.promoteNext p = false) :
    P.promoteNext q = true := by
  have hidx : d = F.neg (P.seed p) := by rw [h.2]; exact Φ.index_turn p hp
  refine ((Φ.actual G).active_continues h).cadence.mpr ?_
  intro hopen
  have hres : P.Resolves p d := by
    rw [hidx]
    exact P.resolves_neg (P.realises_resolves (Φ.seed_realised p))
  exact hopen.2 hres

/-- **The swirl.**  Whatever a promoting act settles, the next actual act
reverses.  Actual oscillation, not merely possible oscillation. -/
theorem actual_promote_then_reverse {G : GenerativeLayer P}
    {p q r : P.Presentation} {d e : F.Determination}
    (h₁ : (Φ.actual G).Active p q d) (h₂ : (Φ.actual G).Active q r e)
    (hp : P.promoteNext p = true) : e = F.neg d :=
  Φ.actual_reverses_of_turn h₁ h₂ (Φ.actual_alternates_promote h₁ hp)

end Focus

/-! ## 9. The system -/

structure LatentActualSystem where
  field : Field.{u}
  presentations : PresentationLayer.{u,v} field
  possible : GenerativeLayer presentations
  observers : ObserverLayer presentations
  gradient : field.Polarisation
  /-- Every presentation realises its seed.  Discharges nullity failure. -/
  seed_realised : ∀ p, presentations.realises p (presentations.seed p)
  somePresentation : presentations.Presentation
  rich : Possibility.Rich presentations
  plenitude : Possibility.Maximal possible

namespace LatentActualSystem

variable (S : LatentActualSystem.{u,v})

def selector : Selector S.presentations := Selector.ofSeed S.gradient

theorem selector_turns (p : S.presentations.Presentation) :
    S.selector.select p (S.presentations.seed p).opp =
      S.field.neg (S.presentations.seed p) := by
  change Selector.seedSelect S.gradient p (S.presentations.seed p).opp =
    S.field.neg (S.presentations.seed p)
  simp only [Selector.seedSelect, Field.neg]
  rw [Selector.seedSelectPole_at_seed S.gradient p]

def focusing : Focus S.presentations where
  selector := S.selector
  seed_realised := S.seed_realised
  turns := S.selector_turns

def actual : GenerativeLayer S.presentations := S.focusing.actual S.possible

/-- Absolute nullity fails: the seed is realised at every presentation. -/
theorem nullity_failure : S.presentations.NullityFailure :=
  S.presentations.nullityFailure_of_seed_realised S.seed_realised

/-- Something remains open: the offer is open at every presentation. -/
theorem open_nonexhaustive : S.presentations.OpenNonExhaustive :=
  S.presentations.openNonExhaustive_of_offer

theorem fixedPointFree : ∀ d, S.field.neg d ≠ d :=
  S.field.fixedPointFree

theorem possible_productive : S.possible.Productive :=
  Possibility.productive_of_plenitude S.plenitude S.rich

theorem actual_productive : S.actual.Productive :=
  S.focusing.actual_productive S.plenitude S.rich

theorem actual_respected : S.selector.Respected S.actual :=
  S.focusing.actual_respected S.possible

theorem possible_not_respected : ¬ S.selector.Respected S.possible :=
  Possibility.plenitude_excludes_selection S.selector
    S.plenitude S.rich S.open_nonexhaustive S.somePresentation

theorem actual_determinate {p q q' : S.presentations.Presentation}
    {d d' : S.field.Determination}
    (h₁ : S.actual.Active p q d) (h₂ : S.actual.Active p q' d') :
    d = d' ∧ ∀ e, S.presentations.articulates p e →
      (S.presentations.realises q e ↔ S.presentations.realises q' e) :=
  ⟨S.focusing.actual_index_unique h₁ h₂, S.focusing.actual_target_determinate h₁ h₂⟩

/-- Consecutive actual acts reverse when the middle presentation is in turn
cadence. -/
theorem actual_reverses_of_turn
    {p q r : S.presentations.Presentation} {d e : S.field.Determination}
    (h₁ : S.actual.Active p q d) (h₂ : S.actual.Active q r e)
    (hturn : S.presentations.promoteNext q = false) :
    e = S.field.neg d :=
  S.focusing.actual_reverses_of_turn h₁ h₂ hturn

/-- A promoting actual act settles a pole of the offer. -/
theorem actual_promotes
    {p q : S.presentations.Presentation} {d : S.field.Determination}
    (h : S.actual.Active p q d) (hp : S.presentations.promoteNext p = true) :
    d.opp = S.presentations.offer p :=
  S.focusing.actual_promotes h hp

theorem not_fullResolution : ¬ S.presentations.FullResolution :=
  fun h => S.presentations.fullResolution_inconsistent_of_offer S.somePresentation h

theorem latency_is_permanent (p : S.presentations.Presentation) :
    (∃ d, S.presentations.realises p d) ∧
    (∃ d, S.presentations.ExcludedIn p d) ∧
    (∃ d, S.presentations.OpenIn p d) ∧
    (∃ d, S.presentations.UndrawnIn p d) := by
  refine ⟨S.nullity_failure p, ?_, S.open_nonexhaustive p,
    S.presentations.articulativeNonExhaustive p⟩
  refine ⟨S.field.neg (S.presentations.seed p), ?_⟩
  show S.presentations.realises p (S.field.neg (S.field.neg (S.presentations.seed p)))
  rw [S.field.neg_involutive]
  exact S.seed_realised p

theorem no_return {n : Nat} {p : S.presentations.Presentation} :
    ¬ Chain S.actual (n + 1) p p := Archive.no_cycle _

theorem recurrence_without_return
    {p q r : S.presentations.Presentation} {d : S.field.Determination}
    (h₁ : S.possible.Active p q (S.field.neg d)) (h₂ : S.possible.Active q r d)
    (hp : S.presentations.realises p d) :
    S.presentations.StatusEqOn p r ∧ Archive.Precedes S.presentations p r :=
  Archive.recurrence_without_return S.presentations h₁ h₂ hp

/-- Actual acts alternate the cadence, at system level. -/
theorem actual_alternates_promote
    {p q : S.presentations.Presentation} {d : S.field.Determination}
    (h : S.actual.Active p q d)
    (hp : S.presentations.promoteNext p = true) :
    S.presentations.promoteNext q = false :=
  S.focusing.actual_alternates_promote h hp

theorem actual_alternates_turn
    {p q : S.presentations.Presentation} {d : S.field.Determination}
    (h : S.actual.Active p q d)
    (hp : S.presentations.promoteNext p = false) :
    S.presentations.promoteNext q = true :=
  S.focusing.actual_alternates_turn h hp

/-- **The swirl, at system level.**  Whatever a promoting act settles, the next
actual act reverses, and the archive has still moved on. -/
theorem actual_promote_then_reverse
    {p q r : S.presentations.Presentation} {d e : S.field.Determination}
    (h₁ : S.actual.Active p q d) (h₂ : S.actual.Active q r e)
    (hp : S.presentations.promoteNext p = true) :
    e = S.field.neg d ∧ Archive.Precedes S.presentations p r :=
  ⟨S.focusing.actual_promote_then_reverse h₁ h₂ hp,
    Archive.precedes_trans S.presentations
      (Archive.active_precedes S.presentations h₁.1)
      (Archive.active_precedes S.presentations h₂.1)⟩

end LatentActualSystem

/-! ## 10. The void -/

namespace Void

abbrev field : Field.{0} where
  Opposition := Bool
  Pole := fun _ => Bool
  flip := fun {_} b => !b
  flip_involutive := by intro o p; cases p <;> rfl
  flip_free := by intro o p; cases p <;> intro h <;> exact Bool.noConfusion h
  pole_dichotomy := by
    intro o p q; cases p <;> cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  decEqPole := fun _ => inferInstance
  decEqOpp := inferInstance

/-- A coherent layer that draws one opposition, leaves it open, and realises
nothing at all.  Every field of `PresentationLayer` is satisfied, including
`offer_open`, `offer_ne_seed` and `trace_fresh`. -/
abbrev layer : PresentationLayer.{0,0} field where
  Presentation := Unit
  articulates := fun _ d => d.opp = false
  Resolves := fun _ _ => False
  realises := fun _ _ => False
  trace := fun _ => ⟨true, true⟩
  seed := fun _ => ⟨true, true⟩
  offer := fun _ => false
  promoteNext := fun _ => true
  articulates_neg := fun h => h
  resolves_neg := fun h => h
  resolves_articulates := fun h => False.elim h
  realises_resolves := fun h => h
  resolution_orients := fun h => False.elim h
  trace_fresh := fun _ h => Bool.noConfusion h
  offer_open := fun _ => ⟨true, rfl, fun h => h⟩
  offer_ne_seed := fun _ => fun h => Bool.noConfusion h

/-- Absolute nullity is still coherent as a layer.  What excludes it is the
system premise `seed_realised`, not anything in the definition of a
presentation layer. -/
theorem absolutely_null : layer.AbsolutelyNull () := fun _ h => h

end Void

/-- Absolute nullity is not derivable from presentation structure alone: a
full layer can realise nothing while keeping its offer open.  (With
`seed_realised`, nullity failure is a theorem.) -/
theorem nullity_failure_not_derivable :
    ∃ (F : Field.{0}) (P : PresentationLayer.{0,0} F) (p : P.Presentation),
      P.AbsolutelyNull p :=
  ⟨Void.field, Void.layer, (), Void.absolutely_null⟩

/-! ## 11. A model

Stages carry seed, offer (= clock, always open), and a cadence bit.  Continuations
flip cadence: promote then turn, turn then promote. -/

namespace Stage

inductive Idx where
  | base : Idx
  | opp : Nat → Idx
  | tr : Nat → Idx
  deriving DecidableEq

abbrev field : Field.{0} where
  Opposition := Idx
  Pole := fun _ => Bool
  flip := fun {_} b => !b
  flip_involutive := by intro o p; cases p <;> rfl
  flip_free := by intro o p; cases p <;> intro h <;> exact Bool.noConfusion h
  pole_dichotomy := by
    intro o p q; cases p <;> cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  decEqPole := fun _ => inferInstance
  decEqOpp := inferInstance

structure St where
  base : Bool
  val : Nat → Option Bool
  clock : Nat
  seedOpp : Nat
  seedPole : Bool
  seed_ok : seedOpp < clock ∧ val seedOpp = some seedPole
  /-- Cadence: true means promote the offer next. -/
  promoteNext : Bool

def seedOf (s : St) : field.Determination := ⟨Idx.opp s.seedOpp, s.seedPole⟩

def offerOf (s : St) : Idx := Idx.opp s.clock

def articulates (s : St) : field.Determination → Prop
  | ⟨Idx.base, _⟩ => True
  | ⟨Idx.opp _, _⟩ => True
  | ⟨Idx.tr m, _⟩ => m < s.clock

def resolves (s : St) : field.Determination → Prop
  | ⟨Idx.base, _⟩ => True
  | ⟨Idx.opp k, _⟩ => k < s.clock ∧ s.val k ≠ none
  | ⟨Idx.tr m, _⟩ => m < s.clock

def realises (s : St) : field.Determination → Prop
  | ⟨Idx.base, a⟩ => a = s.base
  | ⟨Idx.opp k, a⟩ => k < s.clock ∧ s.val k = some a
  | ⟨Idx.tr m, a⟩ => a = true ∧ m < s.clock

theorem offer_open_of (s : St) :
    ∃ pol, articulates s ⟨offerOf s, pol⟩ ∧ ¬ resolves s ⟨offerOf s, pol⟩ := by
  refine ⟨true, trivial, ?_⟩
  intro h
  exact absurd h.1 (Nat.lt_irrefl s.clock)

theorem offer_ne_seed_of (s : St) : offerOf s ≠ (seedOf s).opp := by
  intro h
  exact (Nat.ne_of_lt s.seed_ok.1).symm (Idx.opp.inj h)

abbrev layer : PresentationLayer.{0,0} field where
  Presentation := St
  articulates := articulates
  Resolves := resolves
  realises := realises
  trace := fun s => ⟨Idx.tr s.clock, true⟩
  seed := seedOf
  offer := offerOf
  promoteNext := fun s => s.promoteNext
  articulates_neg := by
    intro p d h
    cases d with | mk o a => cases o <;> exact h
  resolves_neg := by
    intro p d h
    cases d with | mk o a => cases o <;> exact h
  resolves_articulates := by
    intro p d h
    cases d with
    | mk o a =>
        cases o with
        | base => trivial
        | opp k => trivial
        | tr m => exact h
  realises_resolves := by
    intro p d h
    cases d with
    | mk o a =>
        cases o with
        | base => trivial
        | opp k => exact ⟨h.1, by rw [h.2]; intro hc; exact Option.noConfusion hc⟩
        | tr m => exact h.2
  resolution_orients := by
    intro p d h
    cases d with
    | mk o a =>
        cases o with
        | base =>
            show ExactlyOne (a = p.base) ((!a) = p.base)
            cases a <;> cases hb : p.base <;> simp [ExactlyOne]
        | opp k =>
            have hk : k < p.clock := h.1
            show ExactlyOne (k < p.clock ∧ p.val k = some a)
              (k < p.clock ∧ p.val k = some (!a))
            cases hv : p.val k with
            | none => exact absurd hv h.2
            | some c => cases a <;> cases c <;> simp [ExactlyOne, hk]
        | tr m =>
            have hm : m < p.clock := h
            show ExactlyOne (a = true ∧ m < p.clock) ((!a) = true ∧ m < p.clock)
            cases a <;> simp [ExactlyOne, hm]
  trace_fresh := by
    intro p h
    exact absurd h (Nat.lt_irrefl p.clock)
  offer_open := offer_open_of
  offer_ne_seed := offer_ne_seed_of

/-- Settle opposition `k` on pole `a`.  Cadence becomes "was already resolved"
(turn → promote next; promote → turn next). -/
def cont (s : St) (k : Nat) (a : Bool) : St where
  base := s.base
  val := fun j => if j = k then some a else (if j < s.clock then s.val j else none)
  clock := s.clock + k + 2
  seedOpp := k
  seedPole := a
  seed_ok := by
    refine ⟨by omega, ?_⟩
    rw [if_pos rfl]
  promoteNext := decide (k < s.clock ∧ s.val k ≠ none)

theorem cont_continues (s : St) (k : Nat) (a : Bool) :
    layer.Continues s (cont s k a) ⟨Idx.opp k, a⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · show k < (cont s k a).clock ∧ (cont s k a).val k = some a
    simp only [cont, ite_true]
    exact ⟨by omega, trivial⟩
  · intro o hne pol he
    cases o with
    | base =>
        show (pol = (cont s k a).base ↔ pol = s.base)
        simp only [cont]
    | opp j =>
        have hjk : j ≠ k := fun hj => hne (by cases hj; rfl)
        show (j < (cont s k a).clock ∧ (cont s k a).val j = some pol)
          ↔ (j < s.clock ∧ s.val j = some pol)
        simp only [cont]
        rw [if_neg hjk]
        cases Nat.decLt j s.clock with
        | isTrue hj =>
            rw [if_pos hj]
            exact ⟨fun hx => ⟨hj, hx.2⟩, fun hx => ⟨by omega, hx.2⟩⟩
        | isFalse hj =>
            rw [if_neg hj]
            exact ⟨fun hx => absurd hx.2 (fun hc => Option.noConfusion hc),
                   fun hx => absurd hx.1 hj⟩
    | tr m =>
        have hm : m < s.clock := he
        show (pol = true ∧ m < (cont s k a).clock) ↔ (pol = true ∧ m < s.clock)
        simp only [cont]
        exact ⟨fun hx => ⟨hx.1, hm⟩, fun hx => ⟨hx.1, by omega⟩⟩
  · intro e he
    cases e with
    | mk o c =>
      cases o with
      | base => trivial
      | opp j =>
          have hj : j < s.clock := he.1
          have hvj : s.val j ≠ none := he.2
          show j < (cont s k a).clock ∧ (cont s k a).val j ≠ none
          simp only [cont]
          refine ⟨by omega, ?_⟩
          cases Nat.decEq j k with
          | isTrue hjk => rw [if_pos hjk]; intro hc; exact Option.noConfusion hc
          | isFalse hjk => rw [if_neg hjk, if_pos hj]; exact hvj
      | tr m =>
          have hm : m < s.clock := he
          show m < (cont s k a).clock
          simp only [cont]; omega
  · intro e he
    cases e with
    | mk o c =>
      cases o with
      | base => trivial
      | opp j => trivial
      | tr m =>
          have hm : m < s.clock := he
          show m < (cont s k a).clock
          simp only [cont]; omega
  · change true = true ∧ s.clock < s.clock + k + 2
    constructor
    · rfl
    · omega
  · -- cadence: decide(Resolves) = true ↔ ¬ OpenIn
    show ((cont s k a).promoteNext = true) ↔ ¬ (articulates s ⟨Idx.opp k, a⟩ ∧ ¬ resolves s ⟨Idx.opp k, a⟩)
    simp only [cont, articulates, resolves]
    constructor
    · intro h ⟨_, hnr⟩
      exact hnr (of_decide_eq_true h)
    · intro h
      refine decide_eq_true ?_
      cases inst : (inferInstance : Decidable (k < s.clock ∧ s.val k ≠ none)) with
      | isTrue ht => exact ht
      | isFalse hf => exact absurd ⟨trivial, hf⟩ h
  · -- offer_avoid
    intro heq
    have hclk : (cont s k a).clock = k := by
      simpa [offerOf, cont] using Idx.opp.inj heq
    simp only [cont] at hclk
    omega

abbrev generation : GenerativeLayer layer := Possibility.full layer

theorem rich : Possibility.Rich layer where
  open_cont := by
    intro p d hd
    cases d with
    | mk o a =>
        cases o with
        | base => exact absurd trivial hd.2
        | opp k => exact ⟨cont p k a, cont_continues p k a⟩
        | tr m => exact absurd hd.1 hd.2
  seed_turn := by
    intro p
    refine ⟨cont p p.seedOpp (!p.seedPole), ?_⟩
    have h := cont_continues p p.seedOpp (!p.seedPole)
    simpa [seedOf, Field.neg] using h

theorem seed_realised (p : St) : layer.realises p (seedOf p) := p.seed_ok

theorem nullityFailure : layer.NullityFailure :=
  layer.nullityFailure_of_seed_realised seed_realised

theorem openNonExhaustive : layer.OpenNonExhaustive :=
  layer.openNonExhaustive_of_offer

abbrev gradient : field.Polarisation where
  choose := fun _ => true

abbrev observers : ObserverLayer layer where
  IsObserver := fun _ => True
  AppearsTo := fun p o d => layer.realises p o ∧ layer.realises p d
  observer_is_realised := fun h => h.1
  observed_is_realised := fun h => h.2

/-- Start in turn cadence on opp 0; offer is clock (=1). -/
def s₀ : St :=
  ⟨true, fun j => if j = 0 then some true else none, 1, 0, true,
    ⟨Nat.zero_lt_one, rfl⟩, false⟩

abbrev system : LatentActualSystem.{0,0} where
  field := field
  presentations := layer
  possible := generation
  observers := observers
  gradient := gradient
  seed_realised := seed_realised
  somePresentation := s₀
  rich := rich
  plenitude := Possibility.full_maximal

theorem s₀_turn_cadence : layer.promoteNext s₀ = false := rfl

/-- First actual act turns the seed. -/
theorem actual_turn₀ :
    system.actual.Active s₀ (cont s₀ 0 false)
      (field.neg ⟨Idx.opp 0, true⟩) := by
  refine ⟨cont_continues s₀ 0 false, ?_⟩
  have h := system.focusing.index_turn s₀ s₀_turn_cadence
  simpa [seedOf, Field.neg] using h.symm

def s₁ : St := cont s₀ 0 false

theorem s₁_promote_cadence : layer.promoteNext s₁ = true := by
  decide

/-- Second actual act promotes the offer (clock of s₁). -/
theorem actual_promote₁ :
    system.actual.Active s₁ (cont s₁ s₁.clock true)
      ⟨Idx.opp s₁.clock, true⟩ := by
  have hp : layer.promoteNext s₁ = true := s₁_promote_cadence
  refine ⟨cont_continues s₁ s₁.clock true, ?_⟩
  -- index at promote = select at offer = gradient true at opp clock
  change system.focusing.index s₁ = ⟨Idx.opp s₁.clock, true⟩
  simp only [Focus.index, Focus.focusOpp, LatentActualSystem.focusing,
    LatentActualSystem.selector, offerOf, seedOf]
  -- ofSeed / seedSelect at opp clock, seed is opp 0
  unfold Selector.ofSeed Selector.seedSelect Selector.seedSelectPole
  have hne : (seedOf s₁).opp ≠ Idx.opp s₁.clock := by
    intro h
    have : s₁.seedOpp = s₁.clock := Idx.opp.inj h
    exact Nat.ne_of_lt s₁.seed_ok.1 this
  cases hdec : field.decEqOpp (seedOf s₁).opp (Idx.opp s₁.clock) with
  | isTrue h => exact absurd h hne
  | isFalse h => rfl

def s₂ : St := cont s₁ s₁.clock true

theorem promote_then_turn_cadence : layer.promoteNext s₂ = false := by
  decide

theorem actual_novelty :
    system.actual.Active s₀ s₁ (field.neg ⟨Idx.opp 0, true⟩) ∧
    system.actual.Active s₁ s₂ ⟨Idx.opp s₁.clock, true⟩ ∧
    Idx.opp s₁.clock ≠ Idx.opp 0 :=
  ⟨actual_turn₀, actual_promote₁, by
    intro h
    have : s₁.clock = 0 := Idx.opp.inj h
    have : s₁.seedOpp < s₁.clock := s₁.seed_ok.1
    omega⟩

theorem seed_written : seedOf s₁ = ⟨Idx.opp 0, false⟩ := rfl

theorem oscillation_possible :
    layer.StatusEqOn s₀ (cont s₁ 0 true) ∧
      Archive.Precedes layer s₀ (cont s₁ 0 true) := by
  have h₁ : generation.Active s₀ s₁ (field.neg ⟨Idx.opp 0, true⟩) :=
    cont_continues s₀ 0 false
  have h₂ : generation.Active s₁ (cont s₁ 0 true) ⟨Idx.opp 0, true⟩ :=
    cont_continues s₁ 0 true
  exact Archive.recurrence_without_return layer h₁ h₂ ⟨Nat.zero_lt_one, rfl⟩

end Stage

/-! ## 12. Where the account now stands

Repaired relative to revision 8.

* **The swirl.**  On actual runs, cadence alternates
  (`actual_alternates_promote` / `actual_alternates_turn`).  A promotion is
  followed by a reverse (`actual_promote_then_reverse`), with archive movement.
  Selection constrains which act occurs; it does not thin `Continues`.
* **Void as a layer.**  `nullity_failure_not_derivable` exhibits a full
  `PresentationLayer` that is absolutely null while keeping `offer_open`.
  Only `seed_realised` excludes nullity.
* **Axiom hygiene.**  Stage proofs use `decide`, not `native_decide`.
* **Openness / nullity discharged**, **seed promotion**, **no free focus**,
  **R1–R6** preserved.

Still owed.

* **Richness** remains a strong premise (seed-turn and open halves).
* **Plenitude** remains a generative thickness premise; the selection split is
  now explicit (actual respects selection; possible does not).
* **Space and lived succession** remain open.
-/

end LatentActual
