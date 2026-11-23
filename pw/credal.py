"""The probabilistic layer: credal sets on a finite Stone space.

  stone_space      points of a finitely presented Boolean algebra (possible worlds)
  CredalSet        convex set of probability measures cut out by linear constraints
  CredalSet.bounds lower / upper probability after conditioning (generalized Bayes rule)
  joint_likelihood what a class of copulas allows for evidence observed together
  exchangeable_agreement  what repeated random checks say about a universal hypothesis

Computing the coherent range of one event from constraints on others is de
Finetti's fundamental theorem of probability; it is a linear program.
"""
import numpy as np
from scipy.optimize import linprog

from . import formula as fm


def stone_space(atoms, theory):
    """Mod(T): the valuations of `atoms` satisfying every formula in `theory`.

    Returns {atom: bool vector over the surviving worlds}. Dually, these are the
    homomorphisms from the presented Boolean algebra to 2.
    """
    n = len(atoms)
    bits = (np.arange(2 ** n)[:, None] >> np.arange(n)) & 1
    env = {a: bits[:, i].astype(bool) for i, a in enumerate(atoms)}
    ok = np.ones(2 ** n, dtype=bool)
    for t in theory:
        ok &= np.asarray(fm.evaluate(t, env), dtype=bool)
    return {a: v[ok] for a, v in env.items()}, int(ok.sum())


# Copula classes for k pieces of evidence on one target. Each maps the marginal
# probabilities, given as intervals [lo_i, hi_i], to the range of P(all observed | target state).
#   independent  the product copula Pi
#   comonotone   the upper Frechet bound M: the pieces are one piece seen k times
#   pqd          positive dependence: every copula between Pi and M
#   frechet      no knowledge at all: every copula between W and M
COPULAS = {
    "independent": lambda lo, hi: (lo.prod(), hi.prod()),
    "comonotone": lambda lo, hi: (lo.min(), hi.min()),
    "pqd": lambda lo, hi: (lo.prod(), hi.min()),
    "frechet": lambda lo, hi: (max(0.0, lo.sum() - (len(lo) - 1)), hi.min()),
}


def joint_likelihood(items, dependence):
    """Extreme likelihood pairs (P(all | true), P(all | false)) under a copula class.

    items: one ((t_lo, t_hi), (f_lo, f_hi)) per piece of evidence. Only the ratio
    matters, and the posterior is monotone in it, so the two pairs with the
    smallest and largest ratio are enough.
    """
    a = np.asarray(items, dtype=float)            # shape (k, 2 states, 2 ends)
    t_lo, t_hi = COPULAS[dependence](a[:, 0, 0], a[:, 0, 1])
    f_lo, f_hi = COPULAS[dependence](a[:, 1, 0], a[:, 1, 1])
    return sorted({(t_lo, f_hi), (t_hi, f_lo)})


def exchangeable_agreement(k, mean, min_concentration):
    """Range of P(k randomly drawn checks all agree | the hypothesis is false).

    If the hypothesis is false, an unknown fraction q of inputs still agrees. Draws
    are independent given q, hence exchangeable (de Finetti). q has a Beta prior
    with the given mean and any concentration s >= min_concentration:

        E[q^k] = prod_{i<k} (s*mean + i) / (s + i)

    which decreases in s. s -> infinity gives mean^k (the draws are independent);
    s -> 0 would give `mean` for every k (a wrong hypothesis is wrong either
    everywhere or nowhere a random draw can see), which is why s is bounded below:
    without that bound random checks cannot raise the lower probability at all.
    mean = 1/2, s = 2 is the uniform prior and gives Laplace's 1 / (k + 1).
    """
    s = float(min_concentration)
    hi = float(np.prod([(s * mean + i) / (s + i) for i in range(k)]))
    return mean ** k, hi


class CredalSet:
    """{ mu in Delta(worlds) : each constraint mu(event | given) = p holds }."""

    def __init__(self, n_worlds):
        self.m = n_worlds
        self.rows = []

    def constrain(self, event, given, p):
        """mu(event | given) = p, written linearly as mu(event & given) - p mu(given) = 0."""
        event, given = np.asarray(event, dtype=bool), np.asarray(given, dtype=bool)
        self.rows.append((event & given).astype(float) - p * given.astype(float))

    def _lp(self, objective, weights):
        A = np.vstack(self.rows + [weights])
        b = np.zeros(len(A))
        b[-1] = 1.0
        return linprog(objective, A_eq=A, b_eq=b, bounds=(0, None), method="highs")

    def feasible(self):
        return self._lp(np.zeros(self.m), np.ones(self.m)).status == 0

    def bounds(self, event, likelihoods=None):
        """(lower, upper) probability of `event` after conditioning on each candidate
        likelihood vector; None if every candidate gives the evidence probability zero.

        Conditioning a set of measures element by element is Walley's generalized
        Bayes rule. The ratio objective is linearised by the Charnes-Cooper
        substitution y = mu / mu(evidence), which is the row `weights . y = 1`.
        """
        event = np.asarray(event, dtype=float)
        lo, hi = None, None
        for L in (likelihoods if likelihoods is not None else [np.ones(self.m)]):
            r1, r2 = self._lp(L * event, L), self._lp(-L * event, L)
            if r1.status != 0 or r2.status != 0:
                continue
            lo = r1.fun if lo is None else min(lo, r1.fun)
            hi = -r2.fun if hi is None else max(hi, -r2.fun)
        if lo is None:
            return None
        return max(0.0, round(lo, 9)), min(1.0, round(hi, 9))
