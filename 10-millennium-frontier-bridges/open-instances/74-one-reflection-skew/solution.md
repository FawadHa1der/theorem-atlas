# Reverse-Edge `e = 0` Jacobian Covariants, 3-Coordinate Paired-Normal Transport, and Mordell Conic Seed for `one-reflection-skew`

## Exact Target and Architecture

For the immutable target of [`#74 one-reflection-skew`](instance.rec):

\[
\begin{aligned}
F_{74} &= X_0^6 + X_0^3 X_1 Y_0 Y_1 + \frac{1}{7} X_0 X_1 Y_0^3 Y_1 - \frac{1}{7} X_0 X_1 Y_0 Y_1^3 + X_1^6 + X_1^3 X_2 Y_0 Y_1 + X_2^6 + Y_0^6 + Y_1^6 + Y_2^6, \\
A_{74} &= X_0^3 Y_0^3, \qquad q = 1,
\end{aligned}
\]

this package establishes the complete physical function field, closed-form `e = 0` reverse-edge Weierstrass covariant and $k^1$-jet hierarchy, 3-coordinate paired-normal transport identity, nonsingular $\mathbb{F}_5$ 13-equation Mordell conic incidence seed, degree-10 even-parity Fermat cover reduction, and target-binding reduction:

- [ReverseEdgeCovariants.lean](ReverseEdgeCovariants.lean): Proves the closed-form factorization of `H_e0`, `Theta_e0`, `J_e0`, `Hk_e0`, `Thetak_e0`, `Jk_e0`, and `Mk_e0`, together with `cleared_differential_e0`, `full_syzygy_e0`, and `cleared_differential_jet_e0`.
- [PhysicalField.lean](PhysicalField.lean): Proves irreducibility of $F_{74}$ over $\mathbb{C}$ via `holdoutSpecialization Complex.I`, constructs `CoordinateRing` and `FunctionField`, proves `normal_legal` and `normal_ne_zero`, and establishes `certificate_of_normalized` and `certificate_of_residue_solution`.
- [PhysicalCoordinates.lean](PhysicalCoordinates.lean): Establishes the $3+2+1$ block reduction $B_1 = (X_0, X_2, Y_0), B_2 = (X_1, Y_1), B_3 = (Y_2)$ to the `e = 0` reverse-edge cubic `U_e0 coeffA coeffB coeffC coeffD coeffF x y 1 = 0` in `FunctionField`.
- [PhysicalChart.lean](PhysicalChart.lean): Certifies the Gaussian-rational point $(2, 1-i, 0, 1+i, 0, 2i)$ on $F_{74} = 0$ and constructs the localization away from $X_0 X_1 Y_0 Y_2$.
- [PhysicalNormalTransport.lean](PhysicalNormalTransport.lean): Proves the 3-coordinate paired-normal Euler identity $X_0 F_0 + X_2 F_2 + Y_0 F_3 = 2 R^3 x U_x$, the 2-coordinate paired-normal identity $X_1 F_1 + Y_1 F_4 = 2 R^3 y U_y$, and the cleared 3-coordinate paired-normal residue transport identity `paired_normal_change_3coord_cleared`.
- [PhysicalCubicJets.lean](PhysicalCubicJets.lean): Proves `mordell_syzygy_in_field` and `mordell_weierstrass_curve` ($\eta^2 = \xi^3 + b_{\text{Weierstrass}}$ with $I_4 = 0$) in `FunctionField`.
- [JacobianSeedAndModel.lean](JacobianSeedAndModel.lean): Proves the nonsingular $\mathbb{F}_5$ 13-equation Mordell conic incidence seed $(r(t), x(t), y(t)) = (1+4t+4t^2, 2+2t^2+2t^4, 2+2t^6)$ and its exact $13 \times 13$ inverse Jacobian `inverse_product`, together with `mordell_residue_divergence_cancellation`, `mordell_wronskian_divergence_zero`, and `raw_determinant_74_cleared`.
- [Solution.lean](Solution.lean): Binds `HodgeSubmission.F = sextic`, `HodgeSubmission.A = source`, `HodgeSubmission.q = 1`, proves `fermat_cover_reduction`, and exports `Submission.certificate_from_residue_solution`.
