# Latent-Actual

Latent-Actual is a Lean 4 formalization of a conditional process metaphysics:
actuality is locally determinate and productive, but it never exhausts what is
latent. Determinations belong to unlabelled binary oppositions. Presentations
distinguish what is articulated from what is realized. Lawful continuations
settle one determination, carry a fresh trace of their predecessor, and
alternate between promoting an open opposition and turning the determination
just settled. A trace-encoding law also marks the strict archive order within
later presentations' articulation profiles as their past.

The resulting motion is a **swirl**: after a promotion, the next actual act
realizes its contrary, while the archive has irreversibly advanced. Qualitative
reversal therefore need not be a return to the same presentation.

This repository makes that claim precise and checks it in Lean. It does **not**
claim to derive actuality, plenitude, time, or experience from logic alone.
The assumptions responsible for openness, generation, focus, and historical
advance are explicit, and the file includes a countermodel showing that
presentation structure by itself is compatible with absolute nullity.

## The argument at a glance

The formalization separates three levels that are easy to conflate:

1. **Determinations.** An opposition has two freely exchanged poles. A
   determination is one pole at one opposition; its contrary is the other pole,
   not a proposition's logical negation.
2. **Presentations.** A determination may be realized, excluded because its
   contrary is realized, open because its opposition is articulated but
   unresolved, or undrawn because it is not articulated there.
3. **Transitions.** A possible transition settles a target and carries a fresh
   trace. A focus filters possible transitions into actual transitions by
   choosing one target at each source presentation.

From there the main argument is:

1. Every presentation offers some articulated but unresolved opposition, and
   every presentation has a fresh, undrawn trace.
2. A continuation preserves prior articulation, realizes its target, realizes
   the predecessor's trace, and writes the target as its new seed.
3. Trace freshness plus trace carriage gives a strict archive order, so no
   non-empty finite chain returns to the identical presentation. Trace encoding
   marks that same order internally: a presentation articulates the trace of
   exactly those presentations that precede it.
4. Optional **plenitude** says that every relevant continuation is possible. It
   makes both possibility and focused actuality locally productive. Given a
   presentation (in particular, a root), it also proves that no single selector
   can agree with every possible act.
5. A **focus** makes actuality target-determinate: it promotes the open offer or
   turns the seed, according to a two-state cadence.
6. On a history rooted in one realized seed, seed realization propagates.
   Realized, excluded, open, and undrawn content consequently coexist at every
   reachable presentation.
7. Every promotion is followed by a turn of the promoted determination, but
   the archive moves forward. This is reversal without return.

In compact form, the strongest system-level conclusion is:

$$
\text{Plenitude} + \text{Rooted history}
\Longrightarrow
\begin{cases}
\text{productive possibility and actuality},\\
\text{focused target determinacy},\\
\text{permanent latent excess},\\
\text{alternating promotion and reversal},\\
\text{irreversible, internally marked archival advance}.
\end{cases}
$$

## Core vocabulary

| Formal notion | Intended reading | Important qualification |
| --- | --- | --- |
| <code>Field.Opposition</code> | A determinable or dimension of contrast | A bare field may contain an empty pole type; inhabited fibres have the intended two-pole form |
| <code>Determination</code> | A pole of an opposition | Its <code>neg</code> is an ontic contrary, not logical negation |
| <code>articulates p d</code> | The content is drawn or intelligible at <code>p</code> | Articulation does not imply realization |
| <code>realises p d</code> | The pole is effective at <code>p</code> | Opposite poles cannot both be realized |
| <code>OpenIn p d</code> | The opposition is articulated but unresolved | Both poles are latent |
| <code>trace p</code> | Fresh historical content of <code>p</code> | Freshness, articulation-complete encoding, and successor carriage are structural assumptions |
| <code>seed p</code> | The target written by the preceding act | A rooted history assumes its initial seed is realized |
| <code>offer p</code> | An open opposition available for promotion | Its openness is presentation structure |
| <code>possible.Active</code> | A lawful continuation | Possibility is transition-relative, not a possible-world semantics |
| <code>actual.Active</code> | A possible act selected by the focus | This is distinct from the state predicate <code>realises</code> |
| <code>Archive.Precedes</code> | Strict historical advance | It is generated by monotone articulation and fresh trace carriage |
| <code>Succession.InPast q p</code> | <code>q</code> articulates <code>p</code>'s trace as a past marker | Trace encoding proves this is equivalent to archive precedence; it does not imply that every such trace is resolved |

## Headline results

| Result | Lean declaration |
| --- | --- |
| Resolution realizes exactly one pole | <code>PresentationLayer.resolution_orients</code> |
| Full resolution is inconsistent with the open offer | <code>LatentActualSystem.not_fullResolution</code> |
| Plenitude makes possibility and actuality productive | <code>LatentActualSystem.possible_productive</code>, <code>LatentActualSystem.actual_productive</code> |
| At any supplied presentation, no selector agrees with all plenitudinous possibilities | <code>LatentActualSystem.possible_not_respected</code> |
| Actual targets are unique from a source, though successors need not be | <code>LatentActualSystem.actual_determinate</code> |
| Rooted reachable stages contain realized, excluded, open, and undrawn content | <code>LatentActualSystem.latency_is_permanent</code> |
| No positive finite actual chain returns to its source | <code>LatentActualSystem.no_return</code> |
| The internally marked past is exactly archive precedence and is asymmetric | <code>LatentActualSystem.past_is_precedence</code>, <code>LatentActualSystem.past_asymm</code> |
| An off-target realized determination persists while the successor has a strictly enlarged past, a settled source trace, and open content | <code>LatentActualSystem.lived_succession</code> |
| Cadence has proved even/odd parity along finite actual runs | <code>LatentActualSystem.actual_chain_cadence_even</code>, <code>LatentActualSystem.actual_chain_cadence_odd</code> |
| A promotion is followed by contrary realization and archive advance | <code>LatentActualSystem.actual_promote_then_reverse</code>, <code>LatentActualSystem.Rooted.actual_chain_swirl</code> |
| Presentation structure alone does not exclude absolute nullity | <code>nullity_failure_not_derivable</code> |

The concrete <code>Stage</code> model witnesses that the optional assumptions can
hold together. In particular, it supplies actual productivity, genuine novelty,
transition locality, a concrete lived-succession witness, and a two-step possible
recurrence whose endpoint is still later in the archive.

## Repository layout

| Path | Contents |
| --- | --- |
| [LatentActual.lean](LatentActual.lean) | The complete revision 11 formalization, countermodel, concrete model, and axiom regressions |
| [OpenSite.lean](OpenSite.lean) | Successor schema from compossibility: coherence, independence, locality as a theorem |
| [paper/latent-actual.tex](paper/latent-actual.tex) | The self-contained LaTeX paper developing the argument and its metaphysical interpretation |
| [paper/open-site.tex](paper/open-site.tex) | Design note for the Open Site schema |
| [output/pdf/latent-actual.pdf](output/pdf/latent-actual.pdf) | A compiled copy of the paper |

There is no executable application and no Mathlib dependency. The Lean source
imports only <code>Init</code>; typechecking the file is the build and test.

## Check the formalization

The development's declared baseline is **Lean 4.24.0**. Install Lean through
[elan](https://github.com/leanprover/elan), then run:

~~~powershell
elan toolchain install leanprover/lean4:v4.24.0
elan run leanprover/lean4:v4.24.0 lean LatentActual.lean
elan run leanprover/lean4:v4.24.0 lean OpenSite.lean
~~~

A successful check exits without output. The repository deliberately has no
Lake project or <code>lean-toolchain</code> file, so the explicit version in the
command makes the check reproducible. This checkout also passes Lean 4.33.0
(with one non-fatal universe-linter warning).

The final <code>#guard_msgs</code> blocks are executable regressions over
<code>#print axioms</code>. Under Lean 4.24.0 they report only
<code>Quot.sound</code> for the commuting-assignment diamonds, and no
axioms for the other checked routes.
The source contains no <code>axiom</code>, <code>sorry</code>,
<code>admit</code>, or <code>native_decide</code>.

## Build the paper

With a standard LaTeX distribution and <code>latexmk</code>:

~~~powershell
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=output/pdf paper/latent-actual.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=output/pdf paper/open-site.tex
~~~

The paper uses only common TeX Live packages and carries its bibliography in
the source, so BibTeX is not required.

## What is established - and what is not

The project is best read as a **conditional representation result**. It
establishes the joint coherence and consequences of a sharply stated package:
binary opposition, stratified presentation, local continuation, optional
plenitude, total focus, and one effective root seed.

Its limits are equally important:

- Plenitude is strong: maximality is extensionally the full lawful
  continuation relation.
- Actual determinacy fixes the target and the old articulated realization
  profile, not a unique successor presentation.
- Productivity is one-step seriality; the file does not construct a completed
  infinite history.
- The possible-layer recurrence theorem restores status only on content drawn
  at the starting presentation. The actual swirl proves one-step reversal, not
  perpetual oscillation of a single opposition.
- The optional observer layer formalizes internal co-realization, not
  consciousness or phenomenology. Separately, the succession theorem calls any
  off-target realized determination an observer and proves its persistence.
- The archive's arrow and internal marking are grounded in assumed fresh trace
  production, articulation-complete trace encoding, monotone articulation, and trace
  carriage. Irreversibility is exposed, not conjured from neutral dynamics.
- The formal <code>lived_succession</code> theorem captures a registered-past
  and open-content contrast, not a present predicate, a future event, or
  phenomenal duration. Space, embodiment, causal interpretation, and a
  phenomenology of lived time remain outside the account.

## A successor schema: Open Sites

[OpenSite.lean](OpenSite.lean) starts from **compossibility**, not from
acts. A step is already ordinal, so an act-first primitive gets time
almost free and has nowhere for extension to come from.

Kinds are types of values. Pairwise compatibility says which
determinations can be settled together. Independence is the spatial
primitive; locality (amalgamation of independent settlements) is a
theorem, not a clause on acts. Articulation accumulates and values vary,
as two structures. Time is the ancestral of articulative growth.
Plenitude is the one existential. Observation is restriction to a region.
Dimension and metric are out of scope.

| Result | Lean declaration |
| --- | --- |
| Independent settlements amalgamate and commute | <code>independent_amalgamate</code>, <code>independent_commute</code>, <code>independent_settle_diamond</code> |
| Constraint-locality: settling an independent kind does not change what is settable at the other | <code>independent_settable_iff</code> |
| Time's arrow is irreflexive; settle and revise are not earlier | <code>earlier_irrefl</code>, <code>settles_not_earlier</code>, <code>revises_not_earlier</code> |
| Coherence does not yield a successor | <code>productivity_is_not_coherence_level</code> |
| Remainder is not a theorem of coherence | <code>remainder_not_coherence_level</code>, <code>World.world_not_remainderLaw</code> |
| Independence is not forced by having kinds | <code>independence_not_forced</code> |
| Plenitude exceeds any value-selector | <code>plenitude_exceeds_selector</code> |
| Dichotomous settlement orients; hue is not dichotomous | <code>dichotomous_orients</code>, <code>World.not_dichotomous_hue</code> |
| Interaction blocks amalgamation | <code>World.interaction_blocks_amalgamation</code> |

The binary file is not retracted. It remains the right special case for
promote-and-turn on dichotomous kinds.

## License

No license has been supplied. Until one is added, the usual default copyright
restrictions apply.
