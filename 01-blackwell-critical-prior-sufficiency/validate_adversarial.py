#!/usr/bin/env python3
"""
Exact-Rational & Adversarial Validation Suite for:
Quantitative Critical-Prior Sufficiency (`QuantitativeCriticalSlack.lean`,
`UnifiedSufficiencyBridge.lean`, and `AdversarialTightnessAndMarginalBound.lean`).

All core identities and bounds are verified in exact rational arithmetic (`fractions.Fraction`)
with zero floating-point rounding error.
"""

from fractions import Fraction
import json
import random
import unittest
from pathlib import Path
from typing import List, Tuple, Dict, Any

Frac = Fraction


def pushforward(p: List[Frac], K: List[List[Frac]]) -> List[Frac]:
    """Compute P_b = sum_a p_a * K[a][b]."""
    n_in = len(p)
    n_out = len(K[0])
    return [sum((p[a] * K[a][b] for a in range(n_in)), Frac(0)) for b in range(n_out)]


def weighted_value(p: List[Frac], q: List[Frac], t: Frac) -> Frac:
    """Compute V_t(p, q) = sum_a max(t * p_a, (1 - t) * q_a)."""
    return sum((max(t * pa, (Frac(1) - t) * qa) for pa, qa in zip(p, q)), Frac(0))


def local_slack(p: List[Frac], q: List[Frac], K: List[List[Frac]], t: Frac, b: int) -> Frac:
    """Compute Delta_t(b) = sum_a max(t*p_a, (1-t)*q_a)*K[a][b] - max(t*P_b, (1-t)*Q_b)."""
    P = pushforward(p, K)
    Q = pushforward(q, K)
    upper = sum((max(t * p[a], (Frac(1) - t) * q[a]) * K[a][b] for a in range(len(p))), Frac(0))
    lower = max(t * P[b], (Frac(1) - t) * Q[b])
    return upper - lower


def critical_prior(P_b: Frac, Q_b: Frac) -> Frac:
    """Compute t_b = Q_b / (P_b + Q_b) for P_b + Q_b > 0."""
    if P_b + Q_b == 0:
        return Frac(1, 2)
    return Q_b / (P_b + Q_b)


def mixture_recover(p: List[Frac], q: List[Frac], K: List[List[Frac]]) -> List[List[Frac]]:
    """
    Explicit sum-mixture recovery kernel R_mix[b][a]:
    For P_b + Q_b > 0: R_mix[b][a] = (p_a + q_a) * K[a][b] / (P_b + Q_b)
    For P_b + Q_b == 0: fallback to p_a.
    """
    n_in = len(p)
    n_out = len(K[0])
    P = pushforward(p, K)
    Q = pushforward(q, K)
    R = []
    for b in range(n_out):
        denom = P[b] + Q[b]
        if denom == 0:
            R.append([ p[a] for a in range(n_in) ])
        else:
            R.append([ (p[a] + q[a]) * K[a][b] / denom for a in range(n_in) ])
    return R


def reference_recover(q: List[Frac], K: List[List[Frac]]) -> List[List[Frac]]:
    """
    Q-relative canonical reference decoder R_ref[b][a] = q_a * K[a][b] / Q_b
    (with uniform fallback when Q_b == 0).
    """
    n_in = len(q)
    n_out = len(K[0])
    Q = pushforward(q, K)
    R = []
    for b in range(n_out):
        if Q[b] == 0:
            R.append([ Frac(1, n_in) for _ in range(n_in) ])
        else:
            R.append([ q[a] * K[a][b] / Q[b] for a in range(n_in) ])
    return R


def reconstruct_marginal(P: List[Frac], R: List[List[Frac]]) -> List[Frac]:
    """Compute (P.bind R)_a = sum_b P_b * R[b][a]."""
    n_out = len(P)
    n_in = len(R[0])
    return [sum((P[b] * R[b][a] for b in range(n_out)), Frac(0)) for a in range(n_in)]


def l1_dist(u: List[Frac], v: List[Frac]) -> Frac:
    """Compute L1 distance sum_a |u_a - v_a|."""
    return sum((abs(ua - va) for ua, va in zip(u, v)), Frac(0))


def hockey_stick(p: List[Frac], q: List[Frac], gamma: Frac) -> Frac:
    """Compute H_gamma(p || q) = sum_a max(p_a - gamma * q_a, 0)."""
    return sum((max(pa - gamma * qa, Frac(0)) for pa, qa in zip(p, q)), Frac(0))


class TestQuantitativeCriticalPriorSufficiency(unittest.TestCase):

    def verify_all_theorems_on_instance(self, p: List[Frac], q: List[Frac], K: List[List[Frac]]):
        n_in = len(p)
        n_out = len(K[0])
        self.assertEqual(sum(p), Frac(1))
        self.assertEqual(sum(q), Frac(1))
        for a in range(n_in):
            self.assertEqual(sum(K[a]), Frac(1))

        P = pushforward(p, K)
        Q = pushforward(q, K)
        R_mix = mixture_recover(p, q, K)

        total_critical_slack = Frac(0)
        total_global_defect_at_critical = Frac(0)

        for b in range(n_out):
            denom = P[b] + Q[b]
            if denom > 0:
                tb = critical_prior(P[b], Q[b])
                # 1. Check critical tie: tb * P_b == (1 - tb) * Q_b
                self.assertEqual(tb * P[b], (Frac(1) - tb) * Q[b])

                # 2. Check nonnegativity of local slack: Delta_{tb}(b) >= 0
                slack_b = local_slack(p, q, K, tb, b)
                self.assertGreaterEqual(slack_b, Frac(0))

                # 3. Check sum_b Delta_{tb}(b) == V_{tb}(p,q) - V_{tb}(P,Q)
                global_def_tb = weighted_value(p, q, tb) - weighted_value(P, Q, tb)
                sum_slacks_tb = sum((local_slack(p, q, K, tb, c) for c in range(n_out)), Frac(0))
                self.assertEqual(sum_slacks_tb, global_def_tb)
                self.assertLessEqual(slack_b, global_def_tb)

                # 4. Theorem `weighted_abs_tie_defect_eq_twice_localSlack`:
                # sum_a |tb * p_a - (1 - tb) * q_a| * K[a][b] == 2 * Delta_{tb}(b)
                tie_defect = sum(
                    (abs(tb * p[a] - (Frac(1) - tb) * q[a]) * K[a][b] for a in range(n_in)),
                    Frac(0),
                )
                self.assertEqual(tie_defect, 2 * slack_b)

                # 5. Theorem `fiber_joint_l1_defect_eq_twice_critical_slack`:
                # sum_a |P_b * R_mix[b][a] - p_a * K[a][b]| == 2 * Delta_{tb}(b)
                joint_defect_p = sum(
                    (abs(P[b] * R_mix[b][a] - p[a] * K[a][b]) for a in range(n_in)),
                    Frac(0),
                )
                joint_defect_q = sum(
                    (abs(Q[b] * R_mix[b][a] - q[a] * K[a][b]) for a in range(n_in)),
                    Frac(0),
                )
                self.assertEqual(joint_defect_p, 2 * slack_b)
                self.assertEqual(joint_defect_q, 2 * slack_b)

                # 6. Theorem `weightedValue_eq_hockeyStick` (when tb > 0):
                if tb > 0:
                    gamma = (Frac(1) - tb) / tb
                    hs_val = (Frac(1) - tb) * sum(q) + tb * hockey_stick(p, q, gamma)
                    self.assertEqual(weighted_value(p, q, tb), hs_val)

                total_critical_slack += slack_b
                total_global_defect_at_critical += global_def_tb

        # 7. Theorem `marginal_l1_error_le_sum_fiber_joint_defect`:
        p_rec = reconstruct_marginal(P, R_mix)
        q_rec = reconstruct_marginal(Q, R_mix)
        err_p = l1_dist(p_rec, p)
        err_q = l1_dist(q_rec, q)
        self.assertLessEqual(err_p, 2 * total_critical_slack)
        self.assertLessEqual(err_q, 2 * total_critical_slack)
        self.assertLessEqual(err_p, 2 * total_global_defect_at_critical)
        self.assertLessEqual(err_q, 2 * total_global_defect_at_critical)

        return {
            "err_p": err_p,
            "err_q": err_q,
            "two_sum_local_slack": 2 * total_critical_slack,
            "two_sum_global_defect": 2 * total_global_defect_at_critical,
        }

    def test_01_v34_counterexample_twin(self):
        """V34 Fin 3 -> Fin 2 counterexample: preserves TV at t=1/2, caught at t_0 = 3/13."""
        p = [Frac(2, 5), Frac(1, 10), Frac(1, 2)]
        q = [Frac(1, 10), Frac(1, 20), Frac(17, 20)]
        K = [
            [Frac(1), Frac(0)],
            [Frac(1), Frac(0)],
            [Frac(0), Frac(1)],
        ]
        P = pushforward(p, K)
        Q = pushforward(q, K)
        # Equal-prior TV preservation (t = 1/2):
        self.assertEqual(weighted_value(p, q, Frac(1, 2)), Frac(27, 40))
        self.assertEqual(weighted_value(P, Q, Frac(1, 2)), Frac(27, 40))
        self.assertEqual(local_slack(p, q, K, Frac(1, 2), 0), Frac(0))

        # Critical prior at b=0 is t_0 = (3/20) / (10/20 + 3/20) = 3/13:
        t0 = critical_prior(P[0], Q[0])
        self.assertEqual(t0, Frac(3, 13))
        slack_0 = local_slack(p, q, K, t0, 0)
        self.assertEqual(slack_0, Frac(1, 65))

        res = self.verify_all_theorems_on_instance(p, q, K)
        # Deterministic map -> marginal L1 error attains 2 * sum_b Delta_{tb}(b) = 2/65 WITH EQUALITY!
        self.assertEqual(res["err_p"], Frac(2, 65))
        self.assertEqual(res["err_q"], Frac(2, 65))
        self.assertEqual(res["two_sum_local_slack"], Frac(2, 65))

    def test_02_v34_recoverable_twin(self):
        """V34 Fin 3 -> Fin 2 recoverable twin: zero slack at all critical priors."""
        p = [Frac(2, 5), Frac(1, 10), Frac(1, 2)]
        qR = [Frac(3, 25), Frac(3, 100), Frac(17, 20)]
        K = [
            [Frac(1), Frac(0)],
            [Frac(1), Frac(0)],
            [Frac(0), Frac(1)],
        ]
        res = self.verify_all_theorems_on_instance(p, qR, K)
        self.assertEqual(res["err_p"], Frac(0))
        self.assertEqual(res["err_q"], Frac(0))
        self.assertEqual(res["two_sum_local_slack"], Frac(0))

        # Also verify UnifiedSufficiencyBridge: R_mix == R_ref on all active fibers
        R_mix = mixture_recover(p, qR, K)
        R_ref = reference_recover(qR, K)
        self.assertEqual(R_mix, R_ref)

    def test_03_adversarial_multi_prior_evasion(self):
        """
        Adversarial Fin 4 -> Fin 2 channel that preserves Bayes risk at t = 1/4, 1/2, AND 3/4
        simultaneously (zero defect at all three standard test priors!), yet is non-recoverable
        and is immediately caught at its critical prior t_0 = 1/9.
        """
        # On fiber 0 (atoms 0 and 1): p_0/q_0 = 16, p_1/q_1 = 6.
        # Both ratios > 3 = (1-t)/t for all t >= 1/4! So t=1/4, 1/2, 3/4 all have zero slack!
        # Critical prior t_0 = Q_0 / (P_0 + Q_0) = (3/40) / (30/40 + 3/40) = 1/11.
        p = [Frac(8, 15), Frac(1, 5), Frac(4, 15), Frac(0)]
        q = [Frac(1, 30), Frac(1, 30), Frac(14, 15), Frac(0)]
        K = [
            [Frac(1), Frac(0)],
            [Frac(1), Frac(0)],
            [Frac(0), Frac(1)],
            [Frac(0), Frac(1)],
        ]
        P = pushforward(p, K)
        Q = pushforward(q, K)
        for t_grid in [Frac(1, 4), Frac(1, 2), Frac(3, 4)]:
            self.assertEqual(weighted_value(p, q, t_grid), weighted_value(P, Q, t_grid))

        t0 = critical_prior(P[0], Q[0])
        self.assertEqual(t0, Frac(1, 12))
        res = self.verify_all_theorems_on_instance(p, q, K)
        self.assertGreater(res["two_sum_local_slack"], Frac(0))
        self.assertEqual(res["err_p"], res["two_sum_local_slack"])

    def test_04_adversarial_zero_q_support_singularity(self):
        """
        Adversarial boundary where Q_0 == 0 while P_0 > 0:
        R_ref fails completely on P (cannot reconstruct mass on fiber 0 because Q_0 = 0),
        whereas R_mix handles P_0 > 0, Q_0 = 0 with zero error when critical balance holds!
        """
        p = [Frac(1, 2), Frac(0), Frac(1, 2)]
        q = [Frac(0), Frac(0), Frac(1)]
        K = [
            [Frac(1), Frac(0)],
            [Frac(1), Frac(0)],
            [Frac(0), Frac(1)],
        ]
        res = self.verify_all_theorems_on_instance(p, q, K)
        self.assertEqual(res["err_p"], Frac(0))
        self.assertEqual(res["err_q"], Frac(0))

        # Meanwhile R_ref puts uniform fallback [1/3, 1/3, 1/3] on fiber 0, giving L1 error 2/3 on p!
        P = pushforward(p, K)
        R_ref = reference_recover(q, K)
        p_ref_rec = reconstruct_marginal(P, R_ref)
        self.assertEqual(l1_dist(p_ref_rec, p), Frac(2, 3))

    def test_05_randomized_adversarial_stress_suite(self):
        """Run 500 randomized exact-rational channels (including rank-deficient & sparse)."""
        rng = random.Random(20261024)
        for _ in range(500):
            n_in = rng.randint(2, 6)
            n_out = rng.randint(2, 5)
            raw_p = [rng.randint(0, 10) for _ in range(n_in)]
            if sum(raw_p) == 0:
                raw_p[0] = 1
            p = [Frac(x, sum(raw_p)) for x in raw_p]

            raw_q = [rng.randint(0, 10) for _ in range(n_in)]
            if sum(raw_q) == 0:
                raw_q[-1] = 1
            q = [Frac(x, sum(raw_q)) for x in raw_q]

            K = []
            for _a in range(n_in):
                row = [rng.randint(0, 8) for _ in range(n_out)]
                if sum(row) == 0:
                    row[rng.randint(0, n_out - 1)] = 1
                s = sum(row)
                K.append([Frac(x, s) for x in row])

            self.verify_all_theorems_on_instance(p, q, K)


if __name__ == "__main__":
    unittest.main()
