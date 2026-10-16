# irrationality-measure-constants

In this repository, we seek to prove several irrationality measure results. Let `μ(·)` be the irrationality measure function.<br>
We prove that for all positive rationals `a/b`, `μ(arctan(a/b)) = 2` and `μ(√(a/b)π) = 2`.

`QuadraticField.criterion` in `QuadraticFieldCriterion/QuadraticCriterionStatement.lean` states the quadratic field criterion. For a nonsquare integer `D` and nonzero real `x`, its hypotheses are that `exp(2√D x)` belongs to `ℚ(√D)` and has field norm one. Its conclusion is that `μ(x) = 2`.

Corollaries include the families already discussed above having irrationality measure `2`.


# Instructions

Install Lean 4.34.0 using your usual Lean installation method. From this directory run in powershell:

```powershell
lake build
```
The build completed successfully under Lean 4.34.0 in our session. There are no `sorry`, `admit`, `native_decide`, nor user-created axioms. The formalization depends on Theorem 9 of Liu–Jiang–Zhang, and we've imported their formalization to `ExternalResults/`. Their preprint is found at [https://arxiv.org/abs/2610.10192v2](https://arxiv.org/abs/2610.10192v2).


# Credit

Lily Zhang (pink@berkeley.edu), Evan Li (evl012@ucsd.edu).<br>
We received help from GPT-6 Astra to determine implications from `μ(π) = 2` and Liu–Jiang–Zhang's interpolation theorems, as well as to form this repository (since we aren't very familiar with Lean). Still, we both independently derived the quadratic criterion to summarize these findings. We checked the Lean statements, and we are very confident that the formalized statement remains faithful to the original statement to be proven.<br>
We plan to publish a preprint on arXiv once we fully write up the arguments ourselves.