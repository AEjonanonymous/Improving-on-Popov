# <p align="center">Improving on Popov 
### <p align="center"><i>Machine-Certified Absolute Stability for High-Dimensional Lur'e Systems via Lean 4 &amp; Comparator.</i>

## <p align="center">$Abstract$

<i>High-dimensional Lur'e system stability analysis relies heavily on numerical matrix solvers, leaving safety-critical applications like aerospace EDL vulnerable to frequency-gridding gaps and floating-point drift. To eliminate these approximations, this paper introduces a five-module Popov multiplier framework mechanized via Lean 4 and Comparator. By systematically bridging sector invariants, frequency-domain conditions, and quadratic storage functions through the KYP lemma, we establish an exact, solver-free trajectory stability theorem that guarantees absolute asymptotic convergence across high-dimensional parameter spaces.</i> 

## The Popov Multiplier Framework

Before implementing the proofs in Lean 4, the stability problem is structured into five analytical modules:

**Module 1 (Plant Definition):** Formulate the transfer function $G(s) = C(sI - A)^{-1}B$ over $\mathbb{C}$ and establish its pole stability conditions in Mathlib.

**Module 2 (Sector Invariants):** Formulate the mathematical properties of sector-bounded functions $\phi \in \text{Sector}[\alpha, \beta]$.

**Module 3 (Frequency-Domain Inequalities):** State the strict positive real (SPR) condition for the SISO Circle Criterion:

$$\text{Re}\left( \frac{1 + \beta G(j\omega)}{1 + \alpha G(j\omega)} \right) > 0 \quad \forall \omega \in [0, \infty)$$

**Module 4 (Popov Criterion Extension):** Incorporate the Popov parameter $q \ge 0$ for memoryless time-invariant non-linearities:

$$\text{Re}\left( (1 + j\omega q) G(j\omega) \right) + \frac{1}{k} > 0 \quad \forall \omega \ge 0$$

**Module 5 (Lyapunov Equivalence):** Connect the frequency-domain SPR condition back to the existence of a quadratic-plus-integral Lyapunov Function $V(x) = x^T P x + q \int_0^y \phi(\sigma) d\sigma$ via the Kalman-Yakubovich-Popov (KYP) Lemma.

## Formal Verification in Lean 4 & Comparator

The complete mechanical formalization written in Lean 4 implementing the five-module framework and closing the $n$-dimensional absolute stability theorem is provided below:

🌐 Verify in Lean Web: `LureSystemAbsoluteStability.lean`

🤝 Verify with Comparator Live: `Challenge.lean/Solution.lean`

