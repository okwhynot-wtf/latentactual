#!/usr/bin/env python3
"""Three-layer split vs chance, on draws from a set of numbers.

Possibility  = remaining numbers (draws without replacement).
Expectation  = a weighting over that remainder.
Actuality    = the number that was drawn.

Two worlds:
  fair   — uniform among remaining. Dynamics cannot beat coherence.
  biased — remaining i is drawn with probability proportional to (i+1).
           A kernel that knows (or learns) those weights should beat
           uniform-on-remainder.

Baselines:
  naive      — uniform over the whole alphabet, including already-drawn.
  coherence  — uniform over the remainder (chance given the constraint).
  learned    — empirical pick-rates among remaining, from a train set.
  oracle     — the true weights, when the world is biased.

This is not a sports predictor and not a metaphysics claim. It only
asks whether the split has measurable content on a toy.
"""

from __future__ import annotations

import argparse
import math
import random
from collections import defaultdict
from dataclasses import dataclass


Alphabet = tuple[int, ...]


def alphabet(n: int) -> Alphabet:
    return tuple(range(n))


def draw_next(remaining: list[int], weights: list[float] | None, rng: random.Random) -> int:
    if weights is None:
        return rng.choice(remaining)
    return rng.choices(remaining, weights=weights, k=1)[0]


def true_weight(value: int, kind: str) -> float:
    if kind == "fair":
        return 1.0
    if kind == "biased":
        return float(value + 1)
    raise ValueError(kind)


def generate_sequence(n: int, kind: str, rng: random.Random) -> list[int]:
    remaining = list(alphabet(n))
    out: list[int] = []
    while remaining:
        ws = [true_weight(v, kind) for v in remaining]
        pick = draw_next(remaining, None if kind == "fair" else ws, rng)
        remaining.remove(pick)
        out.append(pick)
    return out


def log_loss(dist: dict[int, float], actual: int) -> float:
    p = dist.get(actual, 0.0)
    return -math.log(max(p, 1e-12))


def as_dist(support: list[int], weight_of) -> dict[int, float]:
    raw = [float(weight_of(v)) for v in support]
    total = sum(raw)
    if total <= 0:
        u = 1.0 / len(support)
        return {v: u for v in support}
    return {v: w / total for v, w in zip(support, raw)}


def naive_dist(n: int) -> dict[int, float]:
    u = 1.0 / n
    return {v: u for v in alphabet(n)}


def coherence_dist(remaining: list[int]) -> dict[int, float]:
    return as_dist(remaining, lambda _v: 1.0)


def oracle_dist(remaining: list[int], kind: str) -> dict[int, float]:
    return as_dist(remaining, lambda v: true_weight(v, kind))


@dataclass
class Rates:
    """How often each value is chosen when it is still available."""

    chosen: dict[int, int]
    available: dict[int, int]

    def weight(self, v: int) -> float:
        a = self.available.get(v, 0)
        if a == 0:
            return 1.0
        return (self.chosen.get(v, 0) + 1.0) / (a + 2.0)  # Laplace


def train_rates(seqs: list[list[int]], n: int) -> Rates:
    chosen: dict[int, int] = defaultdict(int)
    available: dict[int, int] = defaultdict(int)
    for seq in seqs:
        remaining = list(alphabet(n))
        for actual in seq:
            for v in remaining:
                available[v] += 1
            chosen[actual] += 1
            remaining.remove(actual)
    return Rates(chosen=dict(chosen), available=dict(available))


def learned_dist(remaining: list[int], rates: Rates) -> dict[int, float]:
    return as_dist(remaining, rates.weight)


def argmax_pred(dist: dict[int, float], rng: random.Random) -> int:
    best = max(dist.values())
    tied = [v for v, p in dist.items() if p == best]
    return rng.choice(tied)


@dataclass
class Score:
    n: int = 0
    hits: int = 0
    ll: float = 0.0
    illegal: int = 0

    def add(self, dist: dict[int, float], pred: int, actual: int, remaining: list[int]) -> None:
        self.n += 1
        self.hits += int(pred == actual)
        self.ll += log_loss(dist, actual)
        self.illegal += int(pred not in remaining)

    def acc(self) -> float:
        return self.hits / self.n if self.n else 0.0

    def mean_ll(self) -> float:
        return self.ll / self.n if self.n else 0.0

    def illegal_rate(self) -> float:
        return self.illegal / self.n if self.n else 0.0


def evaluate(
    seqs: list[list[int]],
    n: int,
    kind: str,
    rates: Rates,
    rng: random.Random,
) -> dict[str, Score]:
    scores = {
        "naive": Score(),
        "coherence": Score(),
        "learned": Score(),
        "oracle": Score(),
    }
    for seq in seqs:
        remaining = list(alphabet(n))
        for actual in seq:
            dists = {
                "naive": naive_dist(n),
                "coherence": coherence_dist(remaining),
                "learned": learned_dist(remaining, rates),
                "oracle": oracle_dist(remaining, kind),
            }
            for name, dist in dists.items():
                pred = argmax_pred(dist, rng)
                scores[name].add(dist, pred, actual, remaining)
            remaining.remove(actual)
    return scores


def fmt(score: Score) -> str:
    return (
        f"acc={score.acc():.3f}  "
        f"logloss={score.mean_ll():.3f}  "
        f"illegal={score.illegal_rate():.3f}  "
        f"n={score.n}"
    )


def run_world(kind: str, n: int, train_n: int, test_n: int, seed: int) -> dict[str, Score]:
    rng = random.Random(seed)
    train = [generate_sequence(n, kind, rng) for _ in range(train_n)]
    test = [generate_sequence(n, kind, rng) for _ in range(test_n)]
    rates = train_rates(train, n)
    return evaluate(test, n, kind, rates, rng)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--n", type=int, default=10, help="alphabet size (numbers 0..n-1)")
    p.add_argument("--train", type=int, default=400)
    p.add_argument("--test", type=int, default=400)
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    print(f"alphabet 0..{args.n - 1}  train={args.train}  test={args.test}  seed={args.seed}")
    print("Each sequence is a full draw-without-replacement of the alphabet.")
    print()

    for kind in ("fair", "biased"):
        print(f"=== world: {kind} ===")
        if kind == "fair":
            print("True process: uniform among remaining.")
            print("Coherence should beat naive. Learned/oracle should match coherence.")
        else:
            print("True process: P(i) proportional to (i+1) among remaining.")
            print("Learned and oracle should beat uniform-on-remainder.")
        scores = run_world(kind, args.n, args.train, args.test, args.seed + (0 if kind == "fair" else 1))
        for name in ("naive", "coherence", "learned", "oracle"):
            print(f"  {name:10s} {fmt(scores[name])}")
        print()


if __name__ == "__main__":
    main()
