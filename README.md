# Universal Quotient Master Theorem (`∀ n ≥ 7`) — Pure Lean 4 Formalization

[![Universal Master Theorem CI](https://github.com)](https://github.com)
[![Pure Lean 4](https://shields.io)](https://lean-lang.org)
[![ORCID](https://shields.io)](https://orcid.org)
[![License: MIT](https://shields.io)](https://opensource.org)

**Author:** Mohamed Ghali ([ORCID: 0009-0006-3364-5341](https://orcid.org))  
**Date:** November 2026

---

## Methodology & Transparency (Human–AI Collaboration)

This repository follows a transparent **computer-assisted formal mathematics** workflow:
* **Scientific Direction & Mathematical Architecture:** All algebraic definitions (`RingProj`, quotient–Bézout duality), modular sieve choices, and theorem structures were conceived and directed by **Mohamed Ghali**.
* **AI Assistance:** Large Language Models (LLMs) were utilized as productivity assistants for generating Python combinatorial residue-search scripts, LaTeX formatting, and Lean 4 tactic synthesis (`omega`, `ac_rfl`).
* **Absolute Kernel Verification:** Every theorem in this repository is mechanically verified by the **pure Lean 4 kernel** (automated GitHub Actions CI, zero `sorryAx`, relying strictly on standard axioms `[propext, Quot.sound]`), guaranteeing 100% mathematical soundness independent of the drafting process.

---

## Main Certified Results (`∀ n ≥ 7`)

The **Universal Master Theorem** (`universalQuotientMasterTheoremForAllN`) rigorously reduces two major open problems in number theory to their minimal modular obstruction cores:

1. **Erdős–Straus Conjecture (`HasErdosStraus n`):**  
   For **every integer \(n \ge 7\)**, either \(4/n = 1/x + 1/y + 1/z\) admits an explicit constructive Egyptian fraction decomposition (**834 / 840 residue classes = 99.29%**), or \(n \bmod 840\) belongs strictly to the **6 critical quadratic residues** \(\{1, 121, 169, 289, 361, 529\}\) (the theoretical Mordell–Schinzel polynomial barrier).
2. **Collatz Conjecture (`HasCollatzDescent n`):**  
   For **every integer \(n \ge 2\)**, either the Syracuse trajectory strictly decreases in a bounded number of steps (\(\exists k > 0,\ T^{(k)}(n) < n\), **231 / 256 residue classes = 90.23%**), or \(n\) belongs to the **25 critical ascending residue classes modulo 256**.

---

## Repository Structure

```text
universal-quotient-master-theorem/
├── .github/workflows/
│   └── lean_master_ci.yml           # Automated CI: Python generation + Lean 4 verification + axiom audit
├── scripts/
│   └── generate_master_lean.py      # Reproducible generator for modular algebraic identities
├── theorems/
│   └── UniversalMasterTheorem.lean  # Universal Master Theorem ∀ n ≥ 7 (100% kernel-certified)
├── docs/
│   └── Universal_Master_Theorem.tex # Scientific manuscript (English LaTeX source)
└── README.md
```

---

## Local Verification & Reproducibility

No external libraries (`Mathlib`) are required. A standard installation of **Lean 4** (`v4.14.0` or later) and **Python 3** is sufficient:

```bash
# 1. Generate the formal Lean 4 proof file
python3 scripts/generate_master_lean.py

# 2. Mechanically verify all theorems and audit axioms
lean theorems/UniversalMasterTheorem.lean
```

### Axiom Audit (`#print axioms`)
Continuous integration verifies that all theorems depend exclusively on standard Lean 4 kernel axioms:
```text
'erdosStrausTwoDivisorSplit' depends on axioms: [propext, Quot.sound]
'universalQuotientMasterTheoremForAllN' depends on axioms: [propext]
```

---

## Related Works & Citation

* **Algebraic Quotient Duality & La Machine v22.0:** DOI [`10.5281/zenodo.24424556`](https://doi.org)
* **Regularized Macro-Block Quadratic Polynomial Factorization (MBC-Annealing v5):** HAL [`hal-05860758`](https://hal.science)

```bibtex
@software{ghali2026master,
  author       = {Ghali, Mohamed},
  title        = {{Universal Quotient Master Theorem for all n >= 7: Pure Lean 4 Formalization}},
  year         = {2026},
  month        = nov,
  url          = {https://github.com}
}
```
