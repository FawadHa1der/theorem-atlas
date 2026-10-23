# Discovery 04: Bellman Residual Control & The Coreset Bellman Compression Bridge

## Overview & Verification Status
- **V34 Record Owner:** [`bellman_residual`](http://127.0.0.1:4200/preview/v34/?v=1&a=bellman_residual&s=bellman-residual) (`bellman-residual`, `bellman-selfloop`, `bellman-successor`)
- **V34 Proof Status:** Native Lean 4.29.0 verified (`Econlib 003655cc`, `Mathlib 8a178386`), zero `sorryAx`, standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Source Files in This Folder:**
  1. [`BellmanResidual.lean`](./BellmanResidual.lean) — Verified V34 Lean 4 source proving `abs_sub_valueFunction_le_of_residual_le` (SHA-256: `58351f28572722db2dc092c5166dae7ed65a90056176340a61bfb4da0b5c0950`).
  2. [`CoresetBellmanCompression.lean`](./CoresetBellmanCompression.lean) — **Novel Breakthrough Formalization** creating the first compiled mathematical bridge between `observable_span` (Discovery 02) and `bellman_residual` (Discovery 04).

## 1. The V34 Discovery & Its Sharp Counterexamples
In [`BellmanResidual.lean`](./BellmanResidual.lean), V34 connects `Econlib.Optimization.DynamicProgramming.DetMDP.contractingWith_bellmanOperatorBddFun` with Mathlib's `ContractingWith.dist_fixedPoint_le` to prove that for any uniformly bounded candidate $v : S \to \mathbb{R}$ and discount $0 \le \beta < 1$:
$$\big(\forall s \in S,\ |v(s) - Tv(s)| \le \varepsilon\big) \implies \big(\forall s \in S,\ |v(s) - V^*(s)| \le \frac{\varepsilon}{1 - \beta}\big).$$
Crucially, V34 pairs this with two boundary fixtures:
- **Tightness (`bellman-selfloop`):** A single-state zero-reward self-loop with constant candidate $v(s) = c$ has residual $(1-\beta)|c|$ and value error $|c| = \text{residual}/(1-\beta)$, proving the $(1-\beta)^{-1}$ amplification factor cannot be improved.
- **Why Uniform Boundedness Cannot Be Dropped (`bellman-successor`):** On $S = \mathbb{N}$ with transition $n \mapsto n+1$, zero reward, and $\beta = 1/2$, the unbounded candidate $v(n) = 2^n$ satisfies $Tv(n) = \frac{1}{2} 2^{n+1} = 2^n$, so its Bellman residual is **identically zero at every state** ($\forall n, |v(n) - Tv(n)| = 0$), yet the bounded value function is $V^*(n) = 0$ and the true error $|v(n) - V^*(n)| = 2^n \to \infty$.

## 2. New Breakthrough in `CoresetBellmanCompression.lean`
In [`CoresetBellmanCompression.lean`](./CoresetBellmanCompression.lean), we connect the universal affine query compression theorem from Discovery 02 directly to Bellman residual control:
- **Exact Coreset Q-Backup Invariance (`compressedQBackup_eq_fullQBackup`):** In a stochastic MDP with transition kernel $P(\cdot \mid s,a)$, if candidate value functions lie in the affine span of $k$ basis features $f_1, \dots, f_k : S \to \mathbb{R}$, then replacing the full transition distribution $P(\cdot \mid s,a)$ by a $(k+1)$-point moment-matching coreset $(s_{s,a}, w_{s,a})$ preserves the exact Q-value backup at $(s,a)$ for **all** linear value functions $v(s') = c + \sum_{j=1}^k \theta_j f_j(s')$ simultaneously.
- **Coreset Bellman Residual Transfer (`coreset_bellman_value_error_bound`):** Because the $(k+1)$-point compressed Bellman operator $\hat{T}$ agrees with the full Bellman operator $T$ on the entire affine feature span, a uniform residual bound $|\hat{T}v(s) - v(s)| \le \varepsilon$ computed using only $k+1$ next-states per state-action pair certifies $|v(s) - V^*(s)| \le \varepsilon / (1 - \beta)$ against the true full-kernel value function $V^*$.
