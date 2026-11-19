# Gaussian Perimeter

This project uses Lean to verify Theorem 1.

> Paata Ivanisvili and Xinyuan Xie, *Grokability in five inequalities*, [arXiv:2605.05193](https://arxiv.org/abs/2605.05193).

## Mathematical statements

For a convex set $`K \subseteq \mathbb{R}^n`$, its Gaussian perimeter (or Gaussian surface area) is

```math
\operatorname{GSA}(K) = \int_{\partial K} \varphi_n(x)\,d\sigma(x),
\qquad
\varphi_n(x) = (2\pi)^{-n/2} e^{-\lVert x\rVert^2/2}.
```

Here $\sigma$ is surface measure on the boundary. The maximal Gaussian perimeter in dimension $n$ is

```math
\Gamma(n) = \sup\{\operatorname{GSA}(K) \mid K \subseteq \mathbb{R}^n \text{ is convex}\}.
```

<a name="theorem-1"></a>

**Theorem 1.** We have

```math
\liminf_{n\to\infty} \frac{\Gamma(n)}{n^{1/4}} \ge 0.31258.
```

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there.
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log (lines 198–203) reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.


Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
