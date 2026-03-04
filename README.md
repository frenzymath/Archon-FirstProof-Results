# Archon-FirstProof-Results

**Archon** is an early-stage, **fully autonomous mathematical formalization agentic system** built upon Claude Code.

This repository contains Lean 4 formalizations, **generated entirely by the Archon system**, of problems selected from the FirstProof project. Generated **fully autonomously** (with only one strategic hint for Problem 4), these formalizations are complete with **zero sorrys** and **zero manually written code**.

For each problem, the system automatically executes the following workflow:
1. **Proof Generation:** **Generates** proofs by utilizing LeanSearch for precise Mathlib retrieval and consulting external models (like Gemini/GPT) for informal guides. Guided by this information, the agent automatically **plans a formalization path**, **eliminates sorrys step-by-step**, **adapts** to Mathlib-related roadblocks, and **verifies** that the formal semantics align faithfully with the original natural language proof.
2. **Linter & Formatting:** **fixes** syntax errors and linter warnings.
3. **Optimization for Generality:** **Refactor** the code to further enhance its generality and broader applicability.

This project is developed by **FrenzyMath**, the AI4M team at the Beijing International Center for Mathematical Research (BICMR), Peking University.

---

## Problem Statements

### Problem 4 — Finite Additive Convolution and Harmonic-Mean Inequality

For monic real-rooted polynomials $p, q$ of degree $n \ge 2$, define the **finite additive convolution** $p \boxplus_n q$ via the coefficient formula involving falling factorials. Define $\Phi_n(p) = \sum\limits_{i} \left(\sum\limits_{j \ne i} \frac{1}{r_i - r_j}\right)^2$ where $r_1 < \cdots < r_n$ are the roots.

**Theorem.** For any monic real-rooted polynomials $p, q$ of degree $n \ge 2$:

$$\frac{1}{\Phi_n(p \boxplus_n q)} \ge \frac{1}{\Phi_n(p)} + \frac{1}{\Phi_n(q)}$$

where both sides are defined via `invPhiN_poly` (which returns 0 when the polynomial is not squarefree, and $1/\Phi_n$ otherwise).

### Problem 6 — Large ε-Light Vertex Subsets

For a graph $G = (V, E)$ with Laplacian $L$, a vertex subset $S \subseteq V$ is called **ε-light** if $\varepsilon L - L_S \succeq 0$, where $L_S$ is the Laplacian of the induced subgraph on $S$.

**Theorem.** There exists a constant $c > 0$ such that for every graph $G$ and every $\varepsilon \in (0, 1]$, the vertex set $V$ contains an ε-light subset $S$ with $|S| \ge c\varepsilon|V|$.

---

## Main Formalized Declarations

### Problem 4

```lean
/- Single coefficient of box-plus. -/
def boxPlusCoeff (n : ℕ) (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).sum fun i ↦
    ((n - i).factorial * (n - (k - i)).factorial : ℝ) /
      ((n.factorial * (n - k).factorial : ℝ)) * a i * b (k - i)

/-- Box-plus convolution of two polynomials. -/
def polyBoxPlus (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  coeffsToPoly (boxPlusConv n (polyToCoeffs p n) (polyToCoeffs q n)) n

notation:65 p " ⊞[" n "] " q => polyBoxPlus n p q

/-- Φₙ(roots) = Σ_{i≠j} 1/(rᵢ - rⱼ)². -/
def PhiN (roots : Fin n → ℝ) : ℝ :=
  ∑ i, ((Finset.univ.filter (· ≠ i)).sum fun j ↦
    1 / (roots i - roots j)) ^ 2

/-- 1/Φₙ for polynomials (0 if not squarefree). -/
noncomputable def invPhiN_poly (n : ℕ) (p : ℝ[X]) : ℝ :=
  if h : p.Monic ∧ p.natDegree = n ∧ Squarefree p ∧
      (∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) then
    1 / PhiN n (extract_ordered_real_roots p n h.1 h.2.1 h.2.2.2 h.2.2.1).choose
  else 0

/-- Full harmonic mean inequality (all monic real-rooted polynomials). -/
theorem harmonic_mean_inequality_full
    (n : ℕ) (hn : 2 ≤ n) (p q : ℝ[X])
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_real : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hq_real : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0) :
    invPhiN_poly n (polyBoxPlus n p q) ≥ invPhiN_poly n p + invPhiN_poly n q
```

### Problem 6

```lean
/-- The Laplacian matrix of a simple graph. -/
def graphLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (G.Adj i)).card : ℝ)
    else if G.Adj i j then -1
    else 0

/-- The Laplacian of the induced subgraph on S. -/
def inducedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Matrix V V ℝ :=
  Matrix.of fun i j =>
    if i = j then ((Finset.univ.filter (fun k => i ∈ S ∧ k ∈ S ∧ G.Adj i k)).card : ℝ)
    else if G.Adj i j ∧ i ∈ S ∧ j ∈ S then -1
    else 0

/-- A set S is ε-light if εL - L_S is positive semidefinite. -/
def IsEpsLight (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) (S : Finset V) : Prop :=
  (ε • graphLaplacian G - inducedLaplacian G S).PosSemidef

/-- Main Theorem (Problem 6)-/
theorem exists_eps_light_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∃ S : Finset V, IsEpsLight G ε S ∧ ε / 256 * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := by ...
```

*(Simplified signatures for readability; see source files for full Lean types.)*

---

## Project Structure

```
FirstProof/
├── FirstProof4/
|   ├── Problem4.lean                              # Main theorem chain (harmonic mean inequality)
|   ├── Problem4Aux.lean                           # Auxiliary imports (barrel file)
|   └── Auxiliary/
|       ├── Defs.lean                              # Box-plus convolution, E-transform, translation invariance
|       ├── PhiN.lean                              # Φₙ, rPoly, RPoly, transport matrix, partial fractions
|       ├── Residue.lean                           # Second derivative, sum of residues, residue formula
|       ├── RPoly.lean                             # RPoly lemmas, transport identity, polar decomposition
|       ├── Transport.lean                         # Doubly stochastic transport, critical value decomposition
|       ├── HarmonicBound.lean                     # Jensen, Cauchy-Schwarz, harmonic sum bound
|       ├── RealRoots.lean                         # Real-rootedness, IVT root counting, Rolle
|       ├── SignSquarefree.lean                    # Sign between roots, squarefree lemmas
|       ├── Obreschkoff.lean                       # Backward Hermite-Kakeya / Obreschkoff theorem
|       ├── Obreschkoff_Transport.lean             # Transport matrix nonnegativity via Obreschkoff
|       ├── TransportDecomp.lean                   # Transport decomposition, critical value positivity
|       ├── BoxPlusRealRoots.lean                  # Real-rootedness preservation, PhiN residue bound
|       ├── InvPhiN.lean                           # invPhiN_poly, nonnegativity, positivity
|       ├── RootContinuity.lean                    # Polynomial root perturbation
|       ├── Continuity.lean                        # Continuity of invPhiN_poly at squarefree points
|       └── Density.lean                           # Density of squarefree polynomials
└── FirstProof6/
    ├── Problem6.lean                    # Main theorem — assembles all steps
    ├── Problem6Aux.lean                 # Auxiliary imports
    └── Auxiliary/
        ├── LaplacianBasics.lean         # Step 1 — Edge/graph/induced Laplacians, IsEpsLight
        ├── BarrierPotential.lean        # Step 2 — BSS barrier potential Φ_u(M)
        ├── ResolventBound.lean          # Step 2 — PSD resolvent trace inequality
        ├── OneSidedBarrier.lean         # Step 2 — One-sided barrier lemma (Lemma 6.1)
        ├── ColoringFramework.lean       # Step 3 — PartialColoring, pigeonhole bounds
        ├── DynamicColoring.lean         # Steps 4–5 — Induced Laplacian monotonicity & PSD
        └── LoewnerPullback.lean         # Step 6 — Loewner pullback to ε-lightness
```

---

## Statistics

| Metric | Problem 4 | Problem 6 |
|--------|-----------|-----------|
| Total lines of Lean | ~8,800 | ~3,200 |
| Lean files | 18 | 9 |
| Auxiliary modules | 16 | 7 |
| Lean version | 4.28.0 | 4.28.0 |
| Mathlib version | v4.28.0 | v4.28.0 |

---

## Lean Setup

Lean is an open-source programming language and interactive theorem prover developed by Leonardo de Moura at Microsoft Research and now maintained by the [Lean FRO](https://lean-fro.org/). It combines a dependently typed functional programming language with a powerful tactic framework, enabling the construction of formally verified mathematical proofs.

- Lean repository: https://github.com/leanprover/lean4
- Lean community: https://leanprover-community.github.io/
- Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/index.html

### Step 1: Install Lean

Follow the official installation guide (straightforward, step-by-step instructions):

https://lean-lang.org/install/

### Step 2: Clone this repository

```bash
git clone https://github.com/frenzymath/Archon-FirstProof-Results
cd Archon-FirstProof-Results
```

### Step 3: Build

Open the project in VS Code (with the [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)), then in the terminal:

```bash
# Fetch Mathlib cache (avoids rebuilding Mathlib from source)
lake exe cache get

# Build the project
lake build
```

---

## References

- M. Abouzaid, A. J. Blumberg, M. Hairer, J. Kileel, T. G. Kolda, P. D. Nelson, D. Spielman, N. Srivastava, R. Ward, S. Weinberger, L. Williams, *First Proof*, arXiv:2602.05192, February 2026. https://arxiv.org/abs/2602.05192
- OpenAI, *First Proof?*, February 2026. https://cdn.openai.com/pdf/26177a73-3b75-4828-8c91-e8f1cf27aaa0/oai_first_proof.pdf
- [Mathlib4 documentation](https://leanprover-community.github.io/mathlib4_docs/)
