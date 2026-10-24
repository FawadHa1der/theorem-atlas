The sextic is invariant under independent permutations of the three \(X\) coordinates and the three \(Y\) coordinates. Its mixed part is built from the elementary quadratic symmetric forms \(Q_X\) and \(Q_Y\), so the equation has \(S_3\times S_3\) symmetry without splitting into two ternary summands.

The target \(A=X_0\cdot X_1\cdot X_2\cdot Y_0\cdot Y_1\cdot Y_2\) is symmetric under both permutation groups. That does **not** put its residue in their invariant cohomology. A transposition changes the sign of the residue volume while preserving \(A\), so the residue transforms by the sign character in each factor. The distinction between polynomial symmetry and residue symmetry is crucial here.

The quotient map given by the elementary symmetric functions has weights \((1,2,3,1,2,3)\). Its Jacobian determinant is, up to sign,

\[
\Delta_X\cdot\Delta_Y=\prod_{i<j}(X_i-X_j)\cdot\prod_{i<j}(Y_i-Y_j).
\]

[Chapter 3, §§3.3–3.4](#technical-information/geometric-support) supports the invariant residue sector through reflection or Fano quotients. At \(q=1\), that density construction serves a multiple of \(\Delta_X\cdot\Delta_Y\), not the symmetric monomial chosen here. Individual transpositions likewise serve the opposite character. The global sign involution is not an element of this permutation group, so the book's all-target reflection-group hypothesis is absent.

The large symmetry may still be valuable: it reduces a search to explicit representation types and suggests using covariants, discriminants, or branch correspondences of the symmetric quotient. A certificate need not be invariant as a polynomial six-tuple; the relevant transformation law includes the tangent representation. Averaging a candidate in the correct representation is legitimate, whereas averaging the target into the invariant sector erases it.

The Hessian symmetrizer space is scalar, excluding a hidden linear direct-sum construction, and the projective diagonal group contributes only the global involution. Thus the permutation symmetry remains the main visible organizing feature, while its quotient construction misses the selected character. The challenge is to use that symmetry without discarding the class it is meant to serve.
