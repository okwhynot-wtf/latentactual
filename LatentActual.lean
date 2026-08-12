import Init

/-!
# Latent–Actual, revision 11

Revision 11 retains revision 10's genuine reductions while restoring plenitude
as the system-level explanation of productivity.  Focus replaces a uniform
gradient in the system core; rooted histories propagate seed effectiveness;
observation and archive carriage are internal again; continuations state an
explicit realised-content locality law; and cadence is proved across runs.

**Structurally marked succession (section 5b).**  `trace_encodes` makes a trace
complete for its source's articulation profile, which marks the archive order
inside a later presentation.  The marked past is exactly what precedes the
later presentation; it is a strict asymmetric order, it never shrinks, and each
act adds at least its own source.  The immediate source trace is settled while
open content remains.  Any realised determination persists through an act that
does not work its opposition.  These are structural results, not claims about
awareness or phenomenal time, and the past is not proved linearly ordered.

**Opposition-primitive, unlabelled.**  Fibres are `Z/2`-torsors; a gradient is
a choice of section.

**Seed and offer.**  Each act writes `seed q = d` and refreshes the offer to a
fresh open opposition distinct from `d`.  Cadence: `promoteNext q ↔ ¬ OpenIn p d`
— promote then turn, turn then promote.

**Index.**  If `promoteNext p`, select at `offer p`; else select at
`(seed p).opp` (the contrary, under the seeded selector).  Actuality both
reverses and settles new content.

Compiles under plain Lean 4 core (checked on 4.24.0).  No `axiom`, no `sorry`,
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
  flip_free : ∀ {o : Opposition} (p : Pole o), flip p ≠ p
  pole_dichotomy : ∀ {o : Opposition} (p q : Pole o), p = q ∨ p = flip q
  decEqOpp : DecidableEq Opposition

namespace Field

variable (F : Field.{u})

/-- In a two-pole free fibre, flipping twice is forced to return the pole. -/
theorem flip_involutive {o : F.Opposition} (p : F.Pole o) :
    F.flip (F.flip p) = p := by
  cases F.pole_dichotomy p (F.flip p) with
  | inl h => exact absurd h.symm (F.flip_free p)
  | inr h => exact h.symm

structure Determination where
  opp : F.Opposition
  pole : F.Pole opp

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
  realises : Presentation → F.Determination → Prop
  trace : Presentation → F.Determination
  seed : Presentation → F.Determination
  /-- A fresh open opposition offered for promotion into the seed. -/
  offer : Presentation → F.Opposition
  /-- Cadence bit: if true, the next act promotes the offer; if false, it turns
  the seed. -/
  promoteNext : Presentation → Bool
  articulates_neg : ∀ {p d}, articulates p d → articulates p (F.neg d)
  realises_articulates : ∀ {p d}, realises p d → articulates p d
  realises_exclusive : ∀ {p d}, realises p d → ¬ realises p (F.neg d)
  trace_fresh : ∀ p, ¬ articulates p (trace p)
  /-- A trace is complete for its source's articulation profile: to articulate
  a presentation's trace is to articulate everything that presentation had
  articulated.  This makes the archive order internally marked; it does not
  encode the source's whole state or supply an epistemic reading operation. -/
  trace_encodes : ∀ p q, articulates q (trace p) →
    ∀ d, articulates p d → articulates q d
  /-- The offer is open. -/
  offer_open : ∀ p, ∃ pol, articulates p ⟨offer p, pol⟩ ∧
    ¬ (realises p ⟨offer p, pol⟩ ∨
      realises p (F.neg ⟨offer p, pol⟩))

namespace PresentationLayer

variable {F : Field.{u}} (P : PresentationLayer.{u,v} F)

def HasRealisation (p : P.Presentation) : Prop := ∃ d, P.realises p d

def AbsolutelyNull (p : P.Presentation) : Prop := ∀ d, ¬ P.realises p d

/-- Resolution is not extra structure: an opposition is resolved exactly when
one of its poles is realised. -/
def Resolves (p : P.Presentation) (d : F.Determination) : Prop :=
  P.realises p d ∨ P.realises p (F.neg d)

theorem realises_resolves {p : P.Presentation} {d : F.Determination}
    (h : P.realises p d) : P.Resolves p d := Or.inl h

theorem resolves_neg {p : P.Presentation} {d : F.Determination}
    (h : P.Resolves p d) : P.Resolves p (F.neg d) := by
  cases h with
  | inl hl =>
      exact Or.inr (by rw [F.neg_involutive]; exact hl)
  | inr hr => exact Or.inl hr

theorem resolves_articulates {p : P.Presentation} {d : F.Determination}
    (h : P.Resolves p d) : P.articulates p d := by
  cases h with
  | inl hl => exact P.realises_articulates hl
  | inr hr =>
      have ha := P.articulates_neg (P.realises_articulates hr)
      rw [F.neg_involutive] at ha
      exact ha

theorem resolution_orients {p : P.Presentation} {d : F.Determination}
    (h : P.Resolves p d) :
    ExactlyOne (P.realises p d) (P.realises p (F.neg d)) := by
  cases h with
  | inl hl => exact Or.inl ⟨hl, P.realises_exclusive hl⟩
  | inr hr =>
      refine Or.inr ⟨hr, ?_⟩
      intro hl
      exact P.realises_exclusive hr (by
        rw [F.neg_involutive]
        exact hl)

theorem resolves_iff_pole {p : P.Presentation} {d : F.Determination} :
    P.Resolves p d ↔ (P.realises p d ∨ P.realises p (F.neg d)) := Iff.rfl

theorem not_realises_neg {p : P.Presentation} {d : F.Determination}
    (h : P.realises p d) : ¬ P.realises p (F.neg d) :=
  P.realises_exclusive h

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

def NullityFailureOn (R : P.Presentation → Prop) : Prop :=
  ∀ p, R p → P.HasRealisation p

/-- Realising every seed discharges absolute nullity. -/
theorem nullityFailure_of_seed_realised
    (h : ∀ p, P.realises p (P.seed p)) : P.NullityFailure :=
  fun p => ⟨P.seed p, h p⟩

/-- Seed resolution is the weakest global seed premise needed to exclude
absolute nullity: one of the two seed poles must be realised. -/
theorem nullityFailure_of_seed_resolved
    (h : ∀ p, P.Resolves p (P.seed p)) : P.NullityFailure := by
  intro p
  cases h p with
  | inl hr => exact ⟨P.seed p, hr⟩
  | inr hr => exact ⟨F.neg (P.seed p), hr⟩

/-- An open offer cannot share the opposition of a resolved seed.  Freshness
therefore need not be a primitive presentation-layer field. -/
theorem offer_ne_seed_of_resolved {p : P.Presentation}
    (hseed : P.Resolves p (P.seed p)) :
    P.offer p ≠ (P.seed p).opp := by
  intro heq
  obtain ⟨pol, _, hopen⟩ := P.offer_open p
  let e : F.Determination := ⟨P.offer p, pol⟩
  change ¬ P.Resolves p e at hopen
  have hopp : F.Opposed (P.seed p) e := heq.symm
  cases F.eq_or_neg (P.seed p) e hopp with
  | inl hsame => exact hopen (by rw [hsame]; exact hseed)
  | inr hneg => exact hopen (by rw [hneg]; exact P.resolves_neg hseed)

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
  articulation : ∀ e, P.articulates p e → P.articulates q e
  /-- The successor makes the predecessor's trace effective, not merely drawn. -/
  carries : P.realises q (P.trace p)
  /-- Apart from the target opposition, a genuinely new articulation can only
  be the predecessor's trace opposition. -/
  locality : ∀ e, P.articulates q e → ¬ P.articulates p e →
    F.Opposed d e ∨ F.Opposed (P.trace p) e
  /-- Away from the settled opposition, the predecessor's trace is the only
  newly realised determination.  New articulation without realisation remains
  possible. -/
  realised_locality : ∀ e, ¬ F.Opposed d e → P.realises q e →
    P.realises p e ∨ e = P.trace p
  seeded : P.seed q = d
  /-- After promoting (settling something open), next turns; after turning,
  next promotes. -/
  cadence : (P.promoteNext q = true) ↔ ¬ P.OpenIn p d

namespace Continues

variable {P}

theorem excludes {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : ¬ P.realises q (F.neg d) :=
  P.not_realises_neg h.pole

theorem articulates_trace {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : P.articulates q (P.trace p) :=
  P.realises_articulates h.carries

/-- If the target was already drawn, the predecessor trace is the only newly
drawn opposition. -/
theorem newly_articulated_is_trace {p q : P.Presentation}
    {d : F.Determination} (h : Continues P p q d)
    (hd : P.articulates p d) {e : F.Determination}
    (hq : P.articulates q e) (hp : ¬ P.articulates p e) :
    F.Opposed (P.trace p) e := by
  cases h.locality e hq hp with
  | inl hde =>
      cases F.eq_or_neg d e hde with
      | inl he => exact False.elim (hp (by rw [he]; exact hd))
      | inr he => exact False.elim (hp (by rw [he]; exact P.articulates_neg hd))
  | inr htr => exact htr

theorem off_target_novel_is_trace {p q : P.Presentation}
    {d e : F.Determination} (h : Continues P p q d)
    (hoff : ¬ F.Opposed d e) (hnew : ¬ P.realises p e)
    (hq : P.realises q e) : e = P.trace p := by
  cases h.realised_locality e hoff hq with
  | inl hp => exact absurd hp hnew
  | inr he => exact he

theorem off_determination {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) (e : F.Determination) (hne : ¬ F.Opposed d e)
    (he : P.articulates p e) :
    P.realises q e ↔ P.realises p e := by
  cases e with
  | mk o pol =>
      have : o ≠ d.opp := fun heq => hne heq.symm
      exact h.off o this pol he

/-- Resolution persistence follows from the realised target and preservation
away from its opposition, so it need not burden continuation constructors. -/
theorem resolution {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) :
    ∀ e, P.Resolves p e → P.Resolves q e := by
  intro e hres
  cases F.opposed_em d e with
  | inl hopp =>
      cases F.eq_or_neg d e hopp with
      | inl hsame =>
          rw [hsame]
          exact P.realises_resolves h.pole
      | inr hneg =>
          rw [hneg]
          exact P.resolves_neg (P.realises_resolves h.pole)
  | inr hne =>
      have hart : P.articulates p e := P.resolves_articulates hres
      rw [P.resolves_iff_pole] at hres ⊢
      cases hres with
      | inl hre => exact Or.inl ((h.off_determination e hne hart).mpr hre)
      | inr hrn =>
          have hne' : ¬ F.Opposed d (F.neg e) := by
            change ¬ d.opp = e.opp
            exact hne
          exact Or.inr ((h.off_determination (F.neg e) hne'
            (P.articulates_neg hart)).mpr hrn)

/-- Offer avoidance follows from the target being realised and the refreshed
offer being open. -/
theorem offer_avoid {p q : P.Presentation} {d : F.Determination}
    (h : Continues P p q d) : P.offer q ≠ d.opp := by
  intro heq
  obtain ⟨pol, _, hopen⟩ := P.offer_open q
  let e : F.Determination := ⟨P.offer q, pol⟩
  change ¬ P.Resolves q e at hopen
  have hopp : F.Opposed d e := heq.symm
  cases F.eq_or_neg d e hopp with
  | inl hsame => exact hopen (by rw [hsame]; exact P.realises_resolves h.pole)
  | inr hneg => exact hopen (by
      rw [hneg]
      exact P.resolves_neg (P.realises_resolves h.pole))

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

namespace Cadence

/-- The cadence bit after `n` actual acts, assuming every act flips it. -/
def after : Nat → Bool → Bool
  | 0, b => b
  | n + 1, b => !after n b

@[simp] theorem after_two (b : Bool) : after 2 b = b := by
  simp [after]

theorem after_add_two (n : Nat) (b : Bool) : after (n + 2) b = after n b := by
  simp [after]

@[simp] theorem after_even (k : Nat) (b : Bool) : after (2 * k) b = b := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.mul_succ]
      simp only [after_add_two, ih]

@[simp] theorem after_odd (k : Nat) (b : Bool) :
    after (2 * k + 1) b = !b := by
  simp [after]

end Cadence

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

theorem active_seed_realised {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : P.realises q (P.seed q) := by
  have hc := G.active_continues h
  rw [hc.seeded]
  exact hc.pole

/-- Every non-empty run ends at a presentation realising its newly written
seed, without a global invariant over unreachable presentations. -/
theorem chain_end_seed_realised :
    ∀ {n : Nat} {p q : P.Presentation}, Chain G (n + 1) p q →
      P.realises q (P.seed q) := by
  intro n p q h
  cases h with
  | step _ a => exact G.active_seed_realised a

def ReachableFrom (p q : P.Presentation) : Prop :=
  ∃ n, Chain G n p q

theorem reachable_seed_realised {p q : P.Presentation}
    (hseed : P.realises p (P.seed p)) (h : G.ReachableFrom p q) :
    P.realises q (P.seed q) := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => cases hn; exact hseed
  | succ n => exact G.chain_end_seed_realised hn

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
  AppearsTo : P.Presentation → F.Determination → F.Determination → Prop
  observer_is_realised : ∀ {p o d}, AppearsTo p o d → P.realises p o
  observed_is_realised : ∀ {p o d}, AppearsTo p o d → P.realises p d

namespace ObserverLayer

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F} (O : ObserverLayer P)

/-- To be an observer *at* a presentation is to have something appear there;
this replaces an unconstrained global observer tag. -/
def IsObserverAt (p : P.Presentation) (o : F.Determination) : Prop :=
  ∃ d, O.AppearsTo p o d

theorem observerAt_is_realised {p o} (h : O.IsObserverAt p o) :
    P.realises p o := by
  obtain ⟨d, hd⟩ := h
  exact O.observer_is_realised hd

theorem appears_internal {p o d} (h : O.AppearsTo p o d) :
    P.realises p o ∧ P.realises p d :=
  ⟨O.observer_is_realised h, O.observed_is_realised h⟩

theorem not_appears_both {p o d}
    (h₁ : O.AppearsTo p o d) (h₂ : O.AppearsTo p o (F.neg d)) : False :=
  P.not_realises_neg (O.observed_is_realised h₁) (O.observed_is_realised h₂)

theorem not_appears_open {p o d} (h : O.AppearsTo p o d) : ¬ P.OpenIn p d :=
  fun ho => ho.2 (P.realises_resolves (O.observed_is_realised h))

theorem not_observer_open {p o d} (h : O.AppearsTo p o d) : ¬ P.OpenIn p o :=
  fun ho => ho.2 (P.realises_resolves (O.observer_is_realised h))

/-- An immediate successor carries the predecessor's exact trace pole. -/
def EffectivelyRegisters (q p : P.Presentation) : Prop :=
  P.realises q (P.trace p)

/-- A later presentation continues to register the trace opposition, although
subsequent acts may reverse its pole. -/
def Registers (q p : P.Presentation) : Prop := P.Resolves q (P.trace p)

variable {G : GenerativeLayer P}

theorem effectively_registers_of_active {p q : P.Presentation}
    {d : F.Determination} (h : G.Active p q d) : EffectivelyRegisters q p :=
  (G.active_continues h).carries

theorem registers_of_chain : ∀ {n : Nat} {p q : P.Presentation},
    Chain G (n + 1) p q → Registers q p := by
  intro n
  induction n with
  | zero =>
      intro p q h
      cases h with
      | step c a =>
          cases c with
          | refl _ => exact P.realises_resolves (G.active_continues a).carries
  | succ k ih =>
      intro p q h
      cases h with
      | step c a => exact (G.active_continues a).resolution _ (ih c)

theorem registers_asymm {p q : P.Presentation}
    (h : Archive.Precedes P p q) : ¬ Registers p q :=
  fun hr => P.trace_fresh q (h.1 _ (P.resolves_articulates hr))

end ObserverLayer

/-! ## 5b. Lived succession

The archive order was, until now, visible only from outside: `Archive.Precedes`
relates two presentations, and nothing let a presentation recover the order of
what it had registered.  `trace_encodes` closes that gap, and everything here
follows from it together with trace freshness and articulative growth.

What is derived: the past marked inside a presentation is a strict order, it
never shrinks, each act adds at least its own source, the immediate source trace
is settled, and open content remains.  The direction of succession follows from
the stated trace assumptions rather than from a separate temporal primitive.

What is deliberately not derived: that the past is *linearly* ordered.  It is a
strict partial order and nothing here makes any two of its members comparable.
That is the right outcome: linearity is a feature of a single strand, and
strands are the structure the spatial question needs. -/

namespace Succession

variable {F : Field.{u}} (P : PresentationLayer.{u,v} F)

/-- The past marked inside `q`: `q` articulates `p`'s trace. -/
def InPast (q p : P.Presentation) : Prop := P.articulates q (P.trace p)

/-- **The archive is internally marked.**  A source's trace is articulated at a
later presentation exactly when the source precedes it. -/
theorem inPast_iff_precedes (p q : P.Presentation) :
    InPast P q p ↔ Archive.Precedes P p q := by
  constructor
  · intro h
    exact ⟨P.trace_encodes p q h, h⟩
  · intro h
    exact h.2

theorem inPast_irrefl (p : P.Presentation) : ¬ InPast P p p :=
  P.trace_fresh p

theorem inPast_trans {p q r : P.Presentation}
    (h₁ : InPast P q p) (h₂ : InPast P r q) : InPast P r p := by
  rw [inPast_iff_precedes] at h₁ h₂ ⊢
  exact Archive.precedes_trans P h₁ h₂

/-- Succession has a direction: nothing that is in your past has you in its
past. -/
theorem inPast_asymm {p q : P.Presentation}
    (h : InPast P q p) : ¬ InPast P p q :=
  fun h' => inPast_irrefl P p (inPast_trans P h h')

/-- Transitively, the past of anything in your past is in your past. -/
theorem past_of_past {p q r : P.Presentation}
    (h : InPast P q p) (h' : InPast P p r) : InPast P q r :=
  inPast_trans P h' h

variable {G : GenerativeLayer P}

/-- The past never shrinks. -/
theorem past_monotone {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : ∀ r, InPast P p r → InPast P q r :=
  fun _ hr => (G.active_continues h).articulation _ hr

/-- Each act adds at least its own source to the marked past. -/
theorem past_gains_source {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) : InPast P q p ∧ ¬ InPast P p p :=
  ⟨P.realises_articulates (G.active_continues h).carries, inPast_irrefl P p⟩

/-- Strict growth: everything already registered stays registered, the source
is newly registered, and no presentation registers itself. -/
theorem past_grows_strictly {p q : P.Presentation} {d : F.Determination}
    (h : G.Active p q d) :
    (∀ r, InPast P p r → InPast P q r) ∧ InPast P q p ∧ ¬ InPast P p p :=
  ⟨past_monotone P h, past_gains_source P h⟩

/-- Along a positive chain, the endpoint marks the chain source as past. -/
theorem chain_inPast : ∀ {n : Nat} {p q : P.Presentation},
    Chain G (n + 1) p q → InPast P q p :=
  fun h => (Archive.chain_precedes P h).2

/-- **The arrow.**  The source trace of a positive chain is settled at the
endpoint, prior past markers persist, and the endpoint retains open content. -/
theorem past_settled_future_open
    {n : Nat} {p q : P.Presentation} (h : Chain G (n + 1) p q) :
    P.Resolves q (P.trace p) ∧ (∀ r, InPast P p r → InPast P q r) ∧
      ∃ pol, P.OpenIn q ⟨P.offer q, pol⟩ := by
  refine ⟨ObserverLayer.registers_of_chain h, ?_, ?_⟩
  · intro r hr
    exact (Archive.chain_precedes P h).1 _ hr
  · obtain ⟨pol, ha, hres⟩ := P.offer_open q
    exact ⟨pol, ha, hres⟩

/-! ### Persistent realised content in succession

Here `o` is any realised determination, not an `ObserverLayer` observer or an
appearance witness.  Its one-edge persistence follows from locality whenever
the act targets a different opposition. -/

/-- Off-target realised content persists through one act. -/
theorem observer_persists {p q : P.Presentation} {d o : F.Determination}
    (h : G.Active p q d) (hne : ¬ F.Opposed d o) (ho : P.realises p o) :
    P.realises q o :=
  ((G.active_continues h).off_determination o hne
    (P.realises_articulates ho)).mpr ho

/-- **Structural lived succession.**  Off-target realised content persists;
old past markers remain, the source is newly marked, the successor is not its
own past, the source trace is settled, and open content remains.  The name is a
term of art here and does not assert awareness or phenomenal duration. -/
theorem lived_succession
    {p q : P.Presentation} {d o : F.Determination}
    (h : G.Active p q d) (hne : ¬ F.Opposed d o) (ho : P.realises p o) :
    P.realises q o ∧
    (∀ r, InPast P p r → InPast P q r) ∧
    InPast P q p ∧
    ¬ InPast P q q ∧
    P.Resolves q (P.trace p) ∧
    ∃ pol, P.OpenIn q ⟨P.offer q, pol⟩ := by
  refine ⟨observer_persists P h hne ho, past_monotone P h, ?_, inPast_irrefl P q,
    P.realises_resolves (G.active_continues h).carries, ?_⟩
  · exact P.realises_articulates (G.active_continues h).carries
  · obtain ⟨pol, ha, hres⟩ := P.offer_open q
    exact ⟨pol, ha, hres⟩

end Succession

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

/-- Away from the seed opposition, the seeded selector is exactly the supplied
polarisation. -/
theorem seedSelect_of_ne_seed (T : F.Polarisation) (p : P.Presentation)
    (o : F.Opposition) (hne : (P.seed p).opp ≠ o) :
    (ofSeed T : Selector P).select p o = T.atOpp o := by
  change seedSelect T p o = T.atOpp o
  unfold seedSelect seedSelectPole Field.Polarisation.atOpp
  cases h : F.decEqOpp (P.seed p).opp o with
  | isTrue he => exact absurd he hne
  | isFalse _ => rfl

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

theorem maximal_iff_extends_full {G : GenerativeLayer P} :
    Maximal G ↔ Extends (full P) G := by
  constructor
  · intro h
    exact h (full P) (extends_full G)
  · intro h G' _ p q d hg
    exact h p q d (G'.active_continues hg)

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
    (hmax : Maximal G) (hrich : Rich P)
    (p₀ : P.Presentation) : ¬ S.Respected G := by
  intro hresp
  obtain ⟨pol, ha, hnres⟩ := P.offer_open p₀
  let d : F.Determination := ⟨P.offer p₀, pol⟩
  have hd : P.OpenIn p₀ d := ⟨ha, hnres⟩
  show False
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

/-! ### Explicit active-witness compatibility

These hypotheses are useful for clients that want theorem-local sufficient
conditions.  They are deliberately not the system's explanation of
productivity: `seed_turn_active` already entails productivity. -/

namespace Compatibility

structure OfferAndSeedActs (G : GenerativeLayer P) : Prop where
  offer_active : ∀ p d, d.opp = P.offer p → P.OpenIn p d →
    ∃ q, G.Active p q d
  seed_turn_active : ∀ p, ∃ q, G.Active p q (F.neg (P.seed p))

theorem of_plenitude {G : GenerativeLayer P}
    (hmax : Maximal G) (hrich : Rich P) : OfferAndSeedActs G where
  offer_active := fun p d _ hd => by
    obtain ⟨q, hq⟩ := hrich.open_cont p d hd
    exact ⟨q, (maximal_iff_extends_full.mp hmax) p q d hq⟩
  seed_turn_active := fun p => by
    obtain ⟨q, hq⟩ := hrich.seed_turn p
    exact ⟨q, (maximal_iff_extends_full.mp hmax) p q _ hq⟩

theorem entails_productive {G : GenerativeLayer P}
    (h : OfferAndSeedActs G) : G.Productive := by
  intro p
  obtain ⟨q, hq⟩ := h.seed_turn_active p
  exact ⟨q, ⟨F.neg (P.seed p), hq⟩⟩

end Compatibility

end Possibility

/-! ## 8. Actuality

### Index: promote the offer, or turn the seed

No free focus map.  The cadence bit chooses the regime; the seed and offer
supply the opposition.  Under the seeded selector, turning yields the contrary
of the seed.  Promotion is at the offered opposition, and uses the gradient's
pole whenever seed resolution (hence offer/seed freshness) is available. -/

structure Focus {F : Field.{u}} (P : PresentationLayer.{u,v} F) where
  selector : Selector P
  /-- At the seed's opposition, selection is the contrary. -/
  turns : ∀ p, selector.select p (P.seed p).opp = F.neg (P.seed p)

namespace Focus

open Possibility

variable {F : Field.{u}} {P : PresentationLayer.{u,v} F}

/-- Convenience constructor for the original seeded-gradient account.  The
dynamic core itself needs only the resulting focus. -/
def ofSeed (T : F.Polarisation) : Focus P where
  selector := Selector.ofSeed T
  turns := by
    intro p
    change Selector.seedSelect T p (P.seed p).opp = F.neg (P.seed p)
    simp only [Selector.seedSelect, Field.neg]
    rw [Selector.seedSelectPole_at_seed T p]

def SeededBy (Φ : Focus P) (T : F.Polarisation) : Prop :=
  Φ.selector = Selector.ofSeed T

/-- The opposition under consideration: offer if promoting, else seed. -/
def focusOpp (p : P.Presentation) : F.Opposition :=
  if P.promoteNext p then P.offer p else (P.seed p).opp

variable (Φ : Focus P)

/-- The determination an act from `p` settles. -/
def index (p : P.Presentation) : F.Determination :=
  Φ.selector.select p (focusOpp p)

theorem index_turn (p : P.Presentation) (h : P.promoteNext p = false) :
    Φ.index p = F.neg (P.seed p) := by
  simp only [index, focusOpp, h]
  exact Φ.turns p

theorem index_promote_opp (p : P.Presentation) (h : P.promoteNext p = true) :
    (Φ.index p).opp = P.offer p := by
  simp only [index, focusOpp, h, ↓reduceIte]
  exact Φ.selector.select_opp p (P.offer p)

theorem index_opp (p : P.Presentation) : (Φ.index p).opp = focusOpp p :=
  Φ.selector.select_opp p (focusOpp p)

theorem select_index (p : P.Presentation) :
    Φ.selector.selectDet p (Φ.index p) = Φ.index p := by
  simp only [Selector.selectDet, index]
  rw [Φ.selector.select_opp p (focusOpp p)]

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

/-- Direct active witnesses are a sufficient compatibility route, but their
seed-turn component already entails productivity and is not used as the
system-level explanation. -/
theorem actual_productive_compatibility {G : GenerativeLayer P}
    (hready : Compatibility.OfferAndSeedActs G) :
    (Φ.actual G).Productive := by
  intro p
  cases hp : P.promoteNext p with
  | true =>
      obtain ⟨pol, ha, hr⟩ := P.offer_open p
      have hOpen : P.OpenIn p ⟨P.offer p, pol⟩ := ⟨ha, hr⟩
      have hidx : (Φ.index p).opp = P.offer p := Φ.index_promote_opp p hp
      have hs : Φ.index p = Φ.selector.selectDet p ⟨P.offer p, pol⟩ := by
        simp only [Selector.selectDet, index, focusOpp, hp, ↓reduceIte]
      have hOpen' : P.OpenIn p (Φ.index p) := by
        rw [hs]
        exact Φ.selector.open_select hOpen
      obtain ⟨q, hq⟩ := hready.offer_active p (Φ.index p) hidx hOpen'
      exact ⟨q, ⟨Φ.index p, hq, rfl⟩⟩
  | false =>
      obtain ⟨q, hq⟩ := hready.seed_turn_active p
      have hi : Φ.index p = F.neg (P.seed p) := Φ.index_turn p hp
      exact ⟨q, ⟨Φ.index p, ⟨by rw [hi]; exact hq, rfl⟩⟩⟩

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

/-- With a resolved seed, openness forces the offer away from the seed, so a
promotion genuinely uses the supplied polarisation rather than the seed turn. -/
theorem actual_promotes_gradient (T : F.Polarisation) {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (hselector : Φ.selector = Selector.ofSeed T)
    (h : (Φ.actual G).Active p q d) (hp : P.promoteNext p = true)
    (hseed : P.Resolves p (P.seed p)) :
    d = T.atOpp (P.offer p) := by
  have hd : d = Φ.index p := h.2
  have hne : (P.seed p).opp ≠ P.offer p :=
    (P.offer_ne_seed_of_resolved hseed).symm
  rw [hd]
  simp only [index, focusOpp, hp, ↓reduceIte, hselector]
  exact Selector.seedSelect_of_ne_seed T p (P.offer p) hne

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

/-- A turn is followed by a promotion when the source realises its seed.  This
premise is local; actual reachability propagates it from a rooted initial
presentation. -/
theorem actual_alternates_turn {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d) (hp : P.promoteNext p = false)
    (hseed : P.realises p (P.seed p)) :
    P.promoteNext q = true := by
  have hidx : d = F.neg (P.seed p) := by rw [h.2]; exact Φ.index_turn p hp
  refine ((Φ.actual G).active_continues h).cadence.mpr ?_
  intro hopen
  have hres : P.Resolves p d := by
    rw [hidx]
    exact P.resolves_neg (P.realises_resolves hseed)
  exact hopen.2 hres

/-- Every actual edge flips cadence.  Seed effectiveness is needed only when
the source is in turn cadence. -/
theorem actual_cadence_flip_of_turn_seed {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d)
    (hseed : P.promoteNext p = false → P.realises p (P.seed p)) :
    P.promoteNext q = !P.promoteNext p := by
  cases hp : P.promoteNext p with
  | false =>
      have hq := Φ.actual_alternates_turn h hp (hseed hp)
      simp [hq]
  | true =>
      have hq := Φ.actual_alternates_promote h hp
      simp [hq]

theorem actual_cadence_flip {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d)
    (hseed : P.realises p (P.seed p)) :
    P.promoteNext q = !P.promoteNext p :=
  Φ.actual_cadence_flip_of_turn_seed h (fun _ => hseed)

theorem actual_cadence_ne {G : GenerativeLayer P}
    {p q : P.Presentation} {d : F.Determination}
    (h : (Φ.actual G).Active p q d)
    (hseed : P.realises p (P.seed p)) :
    P.promoteNext q ≠ P.promoteNext p := by
  rw [Φ.actual_cadence_flip h hseed]
  intro heq
  exact (Bool.not_eq_self _).mp heq

/-- Cadence at the end of a finite actual run is determined by run length and
initial cadence.  The chain supplies the transitions; no productivity premise
is used. -/
theorem actual_chain_cadence {G : GenerativeLayer P} :
    ∀ {n : Nat} {p q : P.Presentation}, Chain (Φ.actual G) n p q →
      (P.promoteNext p = false → P.realises p (P.seed p)) →
      P.promoteNext q = Cadence.after n (P.promoteNext p) := by
  intro n p q h
  induction h with
  | refl p =>
      intro _
      rfl
  | @step n p q r d c a ih =>
      intro hseed
      have hseedq : P.promoteNext q = false → P.realises q (P.seed q) := by
        intro hturn
        cases n with
        | zero =>
            cases c
            exact hseed hturn
        | succ n =>
            exact (Φ.actual G).chain_end_seed_realised c
      rw [Φ.actual_cadence_flip_of_turn_seed a hseedq]
      rw [ih hseed]
      rfl

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
  focus : Focus presentations

/-- Optional system-level plenitude.  Its statement avoids a direct active-act
existential: presentation-level continuation witnesses are transferred into
the chosen generative layer by maximality.  `maximal_iff_extends_full` also
makes clear that this is extensionally full, not logically weaker than the
resulting active witnesses. -/
structure LatentActualSystem.Plenitude
    (S : LatentActualSystem.{u,v}) : Prop where
  rich : Possibility.Rich S.presentations
  maximal : Possibility.Maximal S.possible

/-- A rooted actual history carries one seed-effectiveness premise at its root;
all positive successors inherit it from continuation. -/
structure LatentActualSystem.Rooted (S : LatentActualSystem.{u,v}) where
  initial : S.presentations.Presentation
  initial_seed_realised :
    S.presentations.realises initial (S.presentations.seed initial)

namespace LatentActualSystem

variable (S : LatentActualSystem.{u,v})

abbrev selector : Selector S.presentations := S.focus.selector

abbrev focusing : Focus S.presentations := S.focus

def actual : GenerativeLayer S.presentations := S.focusing.actual S.possible

/-- Presentations occurring on a finite actual history from a chosen root. -/
def Reachable (R : Rooted S) (p : S.presentations.Presentation) : Prop :=
  S.actual.ReachableFrom R.initial p

theorem initial_reachable (R : Rooted S) : S.Reachable R R.initial :=
  ⟨0, Chain.refl R.initial⟩

theorem reachable_step (R : Rooted S)
    {p q : S.presentations.Presentation} {d : S.field.Determination}
    (hp : S.Reachable R p) (h : S.actual.Active p q d) :
    S.Reachable R q := by
  obtain ⟨n, hn⟩ := hp
  exact ⟨n + 1, Chain.step hn h⟩

theorem reachable_seed_realised (R : Rooted S)
    {p : S.presentations.Presentation} (hp : S.Reachable R p) :
    S.presentations.realises p (S.presentations.seed p) :=
  S.actual.reachable_seed_realised R.initial_seed_realised hp

/-- Absolute nullity fails on actual history, without a global premise over
unreachable presentations. -/
theorem reachable_nullity_failure (R : Rooted S)
    {p : S.presentations.Presentation} (hp : S.Reachable R p) :
    S.presentations.HasRealisation p :=
  ⟨S.presentations.seed p, S.reachable_seed_realised R hp⟩

theorem nullity_failure_on_reachable (R : Rooted S) :
    S.presentations.NullityFailureOn (S.Reachable R) :=
  fun _ hp => S.reachable_nullity_failure R hp

/-- Something remains open: the offer is open at every presentation. -/
theorem open_nonexhaustive : S.presentations.OpenNonExhaustive :=
  S.presentations.openNonExhaustive_of_offer

theorem fixedPointFree : ∀ d, S.field.neg d ≠ d :=
  S.field.fixedPointFree

theorem possible_productive (H : Plenitude S) :
    S.possible.Productive :=
  Possibility.productive_of_plenitude H.maximal H.rich

theorem actual_productive (H : Plenitude S) :
    S.actual.Productive :=
  S.focusing.actual_productive H.maximal H.rich

theorem actual_respected : S.selector.Respected S.actual :=
  S.focusing.actual_respected S.possible

theorem possible_not_respected (H : Plenitude S)
    (p : S.presentations.Presentation) :
    ¬ S.selector.Respected S.possible :=
  Possibility.plenitude_excludes_selection S.selector H.maximal H.rich p

theorem Rooted.possible_not_respected (R : Rooted S)
    (H : Plenitude S) :
    ¬ S.selector.Respected S.possible :=
  S.possible_not_respected H R.initial

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

theorem actual_promotes_gradient
    (T : S.field.Polarisation) (hfocus : S.focus.SeededBy T)
    {p q : S.presentations.Presentation} {d : S.field.Determination}
    (h : S.actual.Active p q d) (hp : S.presentations.promoteNext p = true)
    (hseed : S.presentations.Resolves p (S.presentations.seed p)) :
    d = T.atOpp (S.presentations.offer p) :=
  S.focusing.actual_promotes_gradient T hfocus h hp hseed

theorem not_fullResolution (p : S.presentations.Presentation) :
    ¬ S.presentations.FullResolution :=
  fun h => S.presentations.fullResolution_inconsistent_of_offer p h

theorem Rooted.not_fullResolution (R : Rooted S) :
    ¬ S.presentations.FullResolution :=
  S.not_fullResolution R.initial

theorem latency_is_permanent (R : Rooted S) {p : S.presentations.Presentation}
    (hp : S.Reachable R p) :
    (∃ d, S.presentations.realises p d) ∧
    (∃ d, S.presentations.ExcludedIn p d) ∧
    (∃ d, S.presentations.OpenIn p d) ∧
    (∃ d, S.presentations.UndrawnIn p d) := by
  refine ⟨S.reachable_nullity_failure R hp, ?_, S.open_nonexhaustive p,
    S.presentations.articulativeNonExhaustive p⟩
  refine ⟨S.field.neg (S.presentations.seed p), ?_⟩
  show S.presentations.realises p (S.field.neg (S.field.neg (S.presentations.seed p)))
  rw [S.field.neg_involutive]
  exact S.reachable_seed_realised R hp

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
    (R : Rooted S) (hr : S.Reachable R p) (h : S.actual.Active p q d)
    (hp : S.presentations.promoteNext p = false) :
    S.presentations.promoteNext q = true :=
  S.focusing.actual_alternates_turn h hp (S.reachable_seed_realised R hr)

/-- Adjacent reachable actual presentations cannot have the same cadence. -/
theorem actual_cadence_ne
    (R : Rooted S) {p q : S.presentations.Presentation}
    {d : S.field.Determination}
    (hp : S.Reachable R p) (h : S.actual.Active p q d) :
    S.presentations.promoteNext q ≠ S.presentations.promoteNext p :=
  S.focusing.actual_cadence_ne h (S.reachable_seed_realised R hp)

/-- Run-level cadence parity from any reachable presentation. -/
theorem actual_chain_cadence_from
    (R : Rooted S) {n : Nat} {p q : S.presentations.Presentation}
    (hp : S.Reachable R p) (h : Chain S.actual n p q) :
    S.presentations.promoteNext q =
      Cadence.after n (S.presentations.promoteNext p) :=
  S.focusing.actual_chain_cadence h
    (fun _ => S.reachable_seed_realised R hp)

/-- Root-specialised run-level parity. -/
theorem Rooted.actual_chain_cadence
    (R : Rooted S) {n : Nat} {q : S.presentations.Presentation}
    (h : Chain S.actual n R.initial q) :
    S.presentations.promoteNext q =
      Cadence.after n (S.presentations.promoteNext R.initial) :=
  S.focusing.actual_chain_cadence h (fun _ => R.initial_seed_realised)

theorem actual_chain_cadence_even
    (R : Rooted S) {k : Nat} {p q : S.presentations.Presentation}
    (hp : S.Reachable R p) (h : Chain S.actual (2 * k) p q) :
    S.presentations.promoteNext q = S.presentations.promoteNext p := by
  simpa using S.actual_chain_cadence_from R hp h

theorem actual_chain_cadence_odd
    (R : Rooted S) {k : Nat} {p q : S.presentations.Presentation}
    (hp : S.Reachable R p) (h : Chain S.actual (2 * k + 1) p q) :
    S.presentations.promoteNext q = !S.presentations.promoteNext p := by
  simpa using S.actual_chain_cadence_from R hp h

/-- Two consecutive actual acts restore the initial cadence. -/
theorem actual_two_step_cadence
    (R : Rooted S) {p q r : S.presentations.Presentation}
    {d e : S.field.Determination}
    (hp : S.Reachable R p) (h₁ : S.actual.Active p q d)
    (h₂ : S.actual.Active q r e) :
    S.presentations.promoteNext r = S.presentations.promoteNext p := by
  have hchain : Chain S.actual 2 p r :=
    Chain.step (Chain.step (Chain.refl p) h₁) h₂
  simpa using S.actual_chain_cadence_from R hp hchain

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

/-- At every promoting parity position in a rooted actual run, the following
actual act reverses the determination just settled and advances the archive. -/
theorem Rooted.actual_chain_swirl
    (R : Rooted S) {n : Nat} {p q r : S.presentations.Presentation}
    {d e : S.field.Determination}
    (hprefix : Chain S.actual n R.initial p)
    (h₁ : S.actual.Active p q d) (h₂ : S.actual.Active q r e)
    (hparity : Cadence.after n
      (S.presentations.promoteNext R.initial) = true) :
    e = S.field.neg d ∧ Archive.Precedes S.presentations p r := by
  have hp : S.presentations.promoteNext p = true :=
    (LatentActualSystem.Rooted.actual_chain_cadence S R hprefix).trans hparity
  exact S.actual_promote_then_reverse h₁ h₂ hp

/-- **Structural lived succession, at system level.**  Across an actual edge,
off-target realised content persists while past markers strictly grow, the
source trace is settled, and open content remains. -/
theorem lived_succession
    {p q : S.presentations.Presentation} {d o : S.field.Determination}
    (h : S.actual.Active p q d) (hne : ¬ S.field.Opposed d o)
    (ho : S.presentations.realises p o) :
    S.presentations.realises q o ∧
    (∀ r, Succession.InPast S.presentations p r →
      Succession.InPast S.presentations q r) ∧
    Succession.InPast S.presentations q p ∧
    ¬ Succession.InPast S.presentations q q ∧
    S.presentations.Resolves q (S.presentations.trace p) ∧
    ∃ pol, S.presentations.OpenIn q ⟨S.presentations.offer q, pol⟩ :=
  Succession.lived_succession S.presentations h hne ho

/-- Internally marked past is exactly generative precedence. -/
theorem past_is_precedence (p q : S.presentations.Presentation) :
    Succession.InPast S.presentations q p ↔
      Archive.Precedes S.presentations p q :=
  Succession.inPast_iff_precedes S.presentations p q

theorem past_asymm {p q : S.presentations.Presentation}
    (h : Succession.InPast S.presentations q p) :
    ¬ Succession.InPast S.presentations p q :=
  Succession.inPast_asymm S.presentations h

end LatentActualSystem

/-! ## 10. The void -/

namespace Void

abbrev field : Field.{0} where
  Opposition := Bool
  Pole := fun _ => Bool
  flip := fun {_} b => !b
  flip_free := by intro o p; cases p <;> intro h <;> exact Bool.noConfusion h
  pole_dichotomy := by
    intro o p q; cases p <;> cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  decEqOpp := inferInstance

/-- A coherent layer that draws one opposition, leaves it open, and realises
nothing at all.  Every reduced `PresentationLayer` field is satisfied,
including `offer_open` and `trace_fresh`. -/
abbrev layer : PresentationLayer.{0,0} field where
  Presentation := Unit
  articulates := fun _ d => d.opp = false
  realises := fun _ _ => False
  trace := fun _ => ⟨true, true⟩
  seed := fun _ => ⟨true, true⟩
  offer := fun _ => false
  promoteNext := fun _ => true
  articulates_neg := fun h => h
  realises_articulates := fun h => False.elim h
  realises_exclusive := fun h => False.elim h
  trace_fresh := fun _ h => Bool.noConfusion h
  trace_encodes := fun _ _ h => Bool.noConfusion h
  offer_open := fun _ => ⟨true, rfl, fun h => h.elim (fun x => x) (fun x => x)⟩

/-- Absolute nullity is still coherent as a layer.  What excludes it on an
actual history is rooted seed effectiveness, not anything in the definition of
a presentation layer. -/
theorem absolutely_null : layer.AbsolutelyNull () := fun _ h => h

end Void

/-- Absolute nullity is not derivable from presentation structure alone: a
full layer can realise nothing while keeping its offer open.  Rooted seed
effectiveness excludes nullity only along reachable actual histories. -/
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
  flip_free := by intro o p; cases p <;> intro h <;> exact Bool.noConfusion h
  pole_dichotomy := by
    intro o p q; cases p <;> cases q
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  decEqOpp := inferInstance

structure St where
  base : Bool
  val : Nat → Option Bool
  clock : Nat
  /-- Number of predecessor traces already carried into this stage.  This is
  separate from `clock`: settling a distant opposition must not silently make
  a block of unrelated archive tokens effective. -/
  history : Nat
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
  | ⟨Idx.tr m, _⟩ => m < s.history

def realises (s : St) : field.Determination → Prop
  | ⟨Idx.base, a⟩ => a = s.base
  | ⟨Idx.opp k, a⟩ => k < s.clock ∧ s.val k = some a
  | ⟨Idx.tr m, a⟩ => a = true ∧ m < s.history

theorem offer_open_of (s : St) :
    ∃ pol, articulates s ⟨offerOf s, pol⟩ ∧
      ¬ (realises s ⟨offerOf s, pol⟩ ∨
        realises s (field.neg ⟨offerOf s, pol⟩)) := by
  refine ⟨true, trivial, ?_⟩
  intro h
  cases h with
  | inl h => exact absurd h.1 (Nat.lt_irrefl s.clock)
  | inr h => exact absurd h.1 (Nat.lt_irrefl s.clock)

theorem offer_ne_seed_of (s : St) : offerOf s ≠ (seedOf s).opp := by
  intro h
  exact (Nat.ne_of_lt s.seed_ok.1).symm (Idx.opp.inj h)

abbrev layer : PresentationLayer.{0,0} field where
  Presentation := St
  articulates := articulates
  realises := realises
  trace := fun s => ⟨Idx.tr s.history, true⟩
  seed := seedOf
  offer := offerOf
  promoteNext := fun s => s.promoteNext
  articulates_neg := by
    intro p d h
    cases d with | mk o a => cases o <;> exact h
  realises_articulates := by
    intro p d h
    cases d with
    | mk o a =>
        cases o with
        | base => trivial
        | opp k => trivial
        | tr m => exact h.2
  realises_exclusive := by
    intro p d h
    cases d with
    | mk o a =>
        cases o with
        | base => cases a <;> cases p.base <;> simp_all [Field.neg, realises]
        | opp k =>
            intro hn
            cases a <;> simp_all [Field.neg, realises]
        | tr m => cases a <;> simp_all [Field.neg, realises]
  trace_fresh := by
    intro p h
    exact absurd h (Nat.lt_irrefl p.history)
  trace_encodes := by
    intro p q h d hd
    have hlt : p.history < q.history := h
    cases d with
    | mk o a =>
        cases o with
        | base => trivial
        | opp k => trivial
        | tr m => exact Nat.lt_trans (hd : m < p.history) hlt
  offer_open := offer_open_of

/-- Settle opposition `k` on pole `a`.  Cadence becomes "was already resolved"
(turn → promote next; promote → turn next). -/
def cont (s : St) (k : Nat) (a : Bool) : St where
  base := s.base
  val := fun j => if j = k then some a else (if j < s.clock then s.val j else none)
  clock := s.clock + k + 2
  history := s.history + 1
  seedOpp := k
  seedPole := a
  seed_ok := by
    refine ⟨by omega, ?_⟩
    rw [if_pos rfl]
  promoteNext := decide (k < s.clock ∧ s.val k ≠ none)

theorem cont_continues (s : St) (k : Nat) (a : Bool) :
    layer.Continues s (cont s k a) ⟨Idx.opp k, a⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
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
            constructor
            · intro hx
              exact absurd hx.2 (by intro hc; cases hc)
            · intro hx
              exact absurd hx.1 hj
    | tr m =>
        have hm : m < s.history := he
        show (pol = true ∧ m < (cont s k a).history) ↔
          (pol = true ∧ m < s.history)
        simp only [cont]
        exact ⟨fun hx => ⟨hx.1, hm⟩, fun hx => ⟨hx.1, by omega⟩⟩
  · intro e he
    cases e with
    | mk o c =>
      cases o with
      | base => trivial
      | opp j => trivial
      | tr m =>
          have hm : m < s.history := he
          show m < (cont s k a).history
          simp only [cont]; omega
  · change true = true ∧ s.history < s.history + 1
    exact ⟨rfl, by omega⟩
  · intro e hq hnot
    cases e with
    | mk o c =>
      cases o with
      | base => exact False.elim (hnot trivial)
      | opp j => exact False.elim (hnot trivial)
      | tr m =>
          have hmq : m < s.history + 1 := hq
          have hmp : ¬ m < s.history := hnot
          have hm : m = s.history := by omega
          exact Or.inr (by
            change Idx.tr s.history = Idx.tr m
            rw [hm])
  · intro e hne hq
    cases e with
    | mk o c =>
      cases o with
      | base =>
          exact Or.inl (by
            show c = s.base
            simpa only [realises, cont] using hq)
      | opp j =>
          have hjk : j ≠ k := fun hj => hne (by cases hj; rfl)
          have hq' : j < (cont s k a).clock ∧
              (cont s k a).val j = some c := hq
          simp only [cont] at hq'
          rw [if_neg hjk] at hq'
          cases Nat.decLt j s.clock with
          | isTrue hj =>
              rw [if_pos hj] at hq'
              exact Or.inl ⟨hj, hq'.2⟩
          | isFalse hj =>
              rw [if_neg hj] at hq'
              exact absurd hq'.2 (by intro hc; cases hc)
      | tr m =>
          have hc : c = true := hq.1
          have hm : m < s.history + 1 := by
            simpa only [cont] using hq.2
          by_cases hold : m < s.history
          · exact Or.inl ⟨hc, hold⟩
          · have heq : m = s.history := by omega
            exact Or.inr (by cases hc; cases heq; rfl)
  · -- cadence: decide(Resolves) = true ↔ ¬ OpenIn
    change (decide (k < s.clock ∧ s.val k ≠ none) = true) ↔
      ¬ (True ∧ ¬ ((k < s.clock ∧ s.val k = some a) ∨
        (k < s.clock ∧ s.val k = some (!a))))
    cases a <;> cases hv : s.val k with
    | none => simp
    | some b => cases b <;> simp

abbrev generation : GenerativeLayer layer := Possibility.full layer

theorem rich : Possibility.Rich layer where
  open_cont := by
    intro p d hd
    cases d with
    | mk o a =>
      cases o with
        | base =>
            cases a with
            | false =>
                cases hb : p.base with
                | false => exact False.elim (hd.2 (Or.inl hb.symm))
                | true  => exact False.elim (hd.2 (Or.inr hb.symm))
            | true =>
                cases hb : p.base with
                | false => exact False.elim (hd.2 (Or.inr hb.symm))
                | true  => exact False.elim (hd.2 (Or.inl hb.symm))
        | opp k => exact ⟨cont p k a, cont_continues p k a⟩
        | tr m =>
            cases a with
            | false => exact False.elim (hd.2 (Or.inr ⟨rfl, hd.1⟩))
            | true  => exact False.elim (hd.2 (Or.inl ⟨rfl, hd.1⟩))
  seed_turn := by
    intro p
    refine ⟨cont p p.seedOpp (!p.seedPole), ?_⟩
    exact cont_continues p p.seedOpp (!p.seedPole)

theorem seed_realised (p : St) : layer.realises p (seedOf p) := p.seed_ok

theorem nullityFailure : layer.NullityFailure :=
  layer.nullityFailure_of_seed_realised seed_realised

theorem openNonExhaustive : layer.OpenNonExhaustive :=
  layer.openNonExhaustive_of_offer

abbrev gradient : field.Polarisation where
  choose := fun _ => true

abbrev observers : ObserverLayer layer where
  AppearsTo := fun p o d => layer.realises p o ∧ layer.realises p d
  observer_is_realised := fun h => h.1
  observed_is_realised := fun h => h.2

/-- Start in turn cadence on opp 0; offer is clock (=1). -/
def s₀ : St :=
  ⟨true, fun j => if j = 0 then some true else none, 1, 0, 0, true,
    ⟨Nat.zero_lt_one, rfl⟩, false⟩

abbrev focus : Focus layer := Focus.ofSeed gradient

abbrev system : LatentActualSystem.{0,0} where
  field := field
  presentations := layer
  possible := generation
  focus := focus

abbrev plenitude : LatentActualSystem.Plenitude system where
  rich := rich
  maximal := Possibility.full_maximal

abbrev rooted : LatentActualSystem.Rooted system where
  initial := s₀
  initial_seed_realised := seed_realised s₀

theorem possible_productive : generation.Productive :=
  system.possible_productive plenitude

theorem actual_productive : system.actual.Productive :=
  system.actual_productive plenitude

theorem possible_not_respected :
    ¬ system.selector.Respected generation :=
  system.possible_not_respected plenitude s₀

theorem s₀_reachable : system.Reachable rooted s₀ :=
  system.initial_reachable rooted

theorem s₀_turn_cadence : layer.promoteNext s₀ = false := rfl

/-- First actual act turns the seed. -/
theorem actual_turn₀ :
    system.actual.Active s₀ (cont s₀ 0 false)
      (field.neg ⟨Idx.opp 0, true⟩) := by
  refine ⟨cont_continues s₀ 0 false, ?_⟩
  have h := system.focusing.index_turn s₀ s₀_turn_cadence
  exact h.symm

def s₁ : St := cont s₀ 0 false

theorem s₁_reachable : system.Reachable rooted s₁ :=
  system.reachable_step rooted s₀_reachable actual_turn₀

theorem s₁_promote_cadence : layer.promoteNext s₁ = true := by
  exact system.actual_alternates_turn rooted s₀_reachable actual_turn₀
    s₀_turn_cadence

/-- Second actual act promotes the offer (clock of s₁). -/
theorem actual_promote₁ :
    system.actual.Active s₁ (cont s₁ s₁.clock true)
      ⟨Idx.opp s₁.clock, true⟩ := by
  have hp : layer.promoteNext s₁ = true := s₁_promote_cadence
  refine ⟨cont_continues s₁ s₁.clock true, ?_⟩
  -- index at promote = select at offer = gradient true at opp clock
  change system.focusing.index s₁ = ⟨Idx.opp s₁.clock, true⟩
  simp only [LatentActualSystem.focusing, system, focus, Focus.ofSeed,
    Focus.index, Focus.focusOpp, offerOf, seedOf]
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

/-- The concrete transition-locality law does real work: after the first act,
the newly drawn trace opposition is exactly the predecessor's history token. -/
theorem first_new_articulation_is_trace {e : field.Determination}
    (hq : layer.articulates s₁ e) (hp : ¬ layer.articulates s₀ e) :
    field.Opposed (layer.trace s₀) e := by
  exact (cont_continues s₀ 0 false).newly_articulated_is_trace
    (layer.articulates_neg (layer.realises_articulates (seed_realised s₀))) hq hp

/-- Away from the turned opposition, the only newly effective content in the
first successor is the predecessor's trace. -/
theorem first_off_target_novel_is_trace {e : field.Determination}
    (hoff : ¬ field.Opposed (field.neg ⟨Idx.opp 0, true⟩) e)
    (hp : ¬ layer.realises s₀ e) (hq : layer.realises s₁ e) :
    e = layer.trace s₀ :=
  (cont_continues s₀ 0 false).off_target_novel_is_trace hoff hp hq

/-- The model exhibits the stated conjunction concretely: the base pole
survives the first act, `s₀` enters `s₁`'s past, `s₁` is not in its own past,
and `s₀`'s trace is settled at `s₁`. -/
theorem lived_succession_witness :
    layer.realises s₁ ⟨Idx.base, true⟩ ∧
    Succession.InPast layer s₁ s₀ ∧
    ¬ Succession.InPast layer s₁ s₁ ∧
    layer.Resolves s₁ (layer.trace s₀) := by
  have h := system.lived_succession actual_turn₀
    (show ¬ field.Opposed (field.neg ⟨Idx.opp 0, true⟩) ⟨Idx.base, true⟩ from by
      intro hc; exact Idx.noConfusion hc)
    (show layer.realises s₀ ⟨Idx.base, true⟩ from rfl)
  exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

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

/-! ## Axiom regression checks

These guards make the choice-freedom claim executable.  In particular they
fail if broad automation reintroduces `Classical.choice` into the concrete
richness/productivity/non-selection route. -/

/--
info: 'LatentActual.Stage.rich' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Stage.rich

/--
info: 'LatentActual.Stage.possible_productive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Stage.possible_productive

/--
info: 'LatentActual.Stage.actual_productive' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Stage.actual_productive

/--
info: 'LatentActual.Stage.possible_not_respected' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Stage.possible_not_respected

/-! ## 12. Where the account now stands

Premise-reduced relative to revision 9, with revision 10's explanatory
regression repaired.

* **Semantic core.**  Resolution is definitionally the realisation of either
  pole.  Involution, resolution persistence, offer/seed freshness and refreshed
  offer avoidance are theorems rather than constructor burdens.
* **Generative thickness.**  Optional `Plenitude` bundles `Rich + Maximal` as
  the system-level route to productivity and possible non-selection.
  `maximal_iff_extends_full` exposes its extensional strength.  The narrower
  `Compatibility.OfferAndSeedActs` interface is retained for theorem-local
  clients and explicitly proves that its seed-turn clause entails productivity.
* **Focus.**  The four-field dynamic core stores a `Focus`, not a uniform
  polarisation.  This drops uniformity, not total selection: a focus still
  chooses at every presentation and opposition.  `Focus.ofSeed` and `SeededBy`
  recover gradient-specific conclusions when that stronger origin matters.
* **Transition locality and archive.**  An immediate successor realises the
  predecessor's exact trace; later stages keep its opposition resolved.
  `locality` and `realised_locality` exclude unrelated new articulation and
  off-target realisation.  Stage's independent history counter witnesses this.
* **Rooted runs.**  The system carries no global seed-effectiveness axiom.
  `Rooted` assumes it once and successors inherit it.  Finite actual chains now
  have proved endpoint cadence, even/odd parity, and parity-indexed swirl.
* **The swirl.**  Conditional reversal, determinacy, archive movement,
  promote cadence and no-return use neither plenitude nor global seed axioms.
* **Optional observers.**  The observer layer is outside the dynamic core, but
  observation is internal when supplied: observer and observed determination
  are both realised at the presentation.  `IsObserverAt` is derived from an
  appearance instead of imposed as an unused global tag.
* **Void and Stage.**  Absolute nullity remains coherent at layer strength;
  the Stage model supplies both optional richness and rooted-history evidence.

Still owed: space and phenomenal lived duration beyond the structural theorem.
-/

end LatentActual
