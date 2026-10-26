# Reverse-Edge `e = 0` (`f = 2d`) Jacobian Covariants, Binary-Block Contact Wronskian Law, and Mordell Conic Seed for `four-plus-two-residual`

## Exact Target and Architecture

For the immutable target of [`#71 four-plus-two-residual`](instance.rec):

\[
\begin{aligned}
F_{71} &= \left(X_0^6 + \frac{5}{7} X_0^5 X_1 + \frac{10}{7} X_0 X_1^5 + X_1^6\right) + \frac{5}{7} X_0 X_1 Y_0 Y_1 (X_0^2 + 2 Y_0^2) \\
&\quad + \left(Y_0^6 + \frac{5}{7} Y_0^5 Y_1 + \frac{15}{7} Y_0 Y_1^5 + Y_1^6\right) + \left(X_2^6 + \frac{15}{7} X_2^4 Y_2^2 + \frac{10}{7} X_2^2 Y_2^4 + Y_2^6\right), \\
A_{71} &= X_0^3 Y_0^3, \qquad q = 1,
\end{aligned}
\]

this package establishes the complete physical function field, closed-form `e = 0` ($f = 2d$) reverse-edge Weierstrass covariant and $k^1$-jet hierarchy, block paired-normal Euler identities, nonsingular $\mathbb{F}_5$ 13-equation Mordell conic incidence seed, binary-block 3-torsion contact-cover Wronskian strict certificate law, and target-binding reduction:

- [ReverseEdgeCovariants.lean](ReverseEdgeCovariants.lean): Proves the closed-form factorization of `H_e0`, `Theta_e0`, `J_e0`, `Hk_e0`, `Thetak_e0`, `Jk_e0`, and `Mk_e0`, together with `cleared_differential_e0`, `full_syzygy_e0`, and `cleared_differential_jet_e0`.
- [PhysicalField.lean](PhysicalField.lean): Proves irreducibility of $F_{71}$ over $\mathbb{C}$ via `holdoutSpecialization Complex.I`, constructs `CoordinateRing` and `FunctionField`, proves `normal_legal` and `normal_ne_zero`, and establishes `certificate_of_normalized` and `certificate_of_residue_solution`.
- [PhysicalCoordinates.lean](PhysicalCoordinates.lean): Establishes the $2+2+2$ block reduction $B_1 = (X_0, X_1), B_2 = (Y_0, Y_1), B_3 = (X_2, Y_2)$ to the `e = 0` reverse-edge cubic `U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0` with `coeffF = 2 * coeffD = (10/7) * c0 * c1` in `FunctionField`.
- [PhysicalChart.lean](PhysicalChart.lean): Constructs the open chart localization away from $X_0 X_2 Y_0$.
- [PhysicalNormalTransport.lean](PhysicalNormalTransport.lean): Proves the block paired-normal Euler identities $X_0 F_0 + X_1 F_1 = 2 R^3 x U_x$ and $Y_0 F_3 + Y_1 F_4 = 2 R^3 y U_y$ in `FunctionField`.
- [PhysicalCubicJets.lean](PhysicalCubicJets.lean): Proves `mordell_syzygy_in_field` and `mordell_weierstrass_curve` ($\eta^2 = \xi^3 + b_{\text{Weierstrass}}$ with $I_4 = 0$) in `FunctionField`.
- [JacobianSeedAndModel.lean](JacobianSeedAndModel.lean): Proves the nonsingular $\mathbb{F}_5$ 13-equation Mordell conic incidence seed $(r(t), x(t), y(t)) = (1+4t+4t^2, 2+2t^2+2t^4, 2+2t^6)$, its exact $13 \times 13$ inverse Jacobian `inverse_product`, and the Chapter 2a binary-block 3-torsion contact-cover Wronskian strict certificate law `binary_block_wronskian_certificate_directional`.
- [Solution.lean](Solution.lean): Binds `HodgeSubmission.F = sextic`, `HodgeSubmission.A = source`, `HodgeSubmission.q = 1`, proves `official_reverse_edge_cubic`, and exports `Submission.certificate_from_residue_solution`.
