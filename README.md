---

## Theoretical Upper Bounds & Completeness Verification

The table below benchmarks the certified coverage of our pure Lean 4 architecture against the absolute mathematical limits of finite quotient methods:

| Problem / Theorem | Certified Coverage | Theoretical Maximum | Nature of the Theoretical Barrier |
| :--- | :---: | :---: | :--- |
| **Erdős–Straus** ($\forall n \ge 7$) | **99.29%** ($834 / 840$) | **99.29%** ($834 / 840$) | **Schinzel–Mordell Ceiling Reached:** Proven impossible for any finite family of polynomial identities to cover the 6 coprime squares $\{1, 121, 169, 289, 361, 529\} \pmod{840}$. |
| **Collatz** ($\forall n \ge 2$) | **90.23%** ($231 / 256$) | $\to 100\%$ asymptotically | **Terras–Everett Exponential Barrier:** Trajectory density converges to $100\%$ as $2^k \to \infty$, though no finite modulus captures every integer. |
| **Riemann / Guy Robin** | **100%** on weighted wheels $\widetilde{V}_r$ | **100%** on $\widetilde{V}_r$ | **Analytic Limit Barrier:** Strict abundance monotonicity ($p^a(p-1) < p^{a+1}-1$) is fully certified; taking $r \to \infty$ is equivalent to the Riemann Hypothesis. |
| **Spectral Regularization** | **100%** universal | **100%** universal | **Optimal:** $\det(\mathcal{A}_j^*) \ge \mu^2 > 0$ holds unconditionally for all $\mu > 0$ and $H_+ \succeq 0$. |
