# irrationality-measure-constants

In this repository, we seek to prove that the irrationality measure `μ(·)` of `arctan(1/n)` is `2` for every positive integer `n`.<br>
Additionally, we prove that `μ(√(a/b)π) = 2`, where `a/b` is a positive rational.


# Reproduce

Install Lean 4.34.0 using your usual Lean installation method. From this directory run in powershell:

```powershell
lake build
```
The build completed successfully under Lean 4.34.0 in our session. There are no `sorry`, `admit`, nor `native_decide`. However, the formalization depends on an axiom, being Theorem 9 of Liu–Jiang–Zhang. The preprint is found at [https://arxiv.org/abs/2610.10192v2](https://arxiv.org/abs/2610.10192v2).


# Credit

Lily Zhang, Evan Li.<br>
We plan to publish a preprint on arXiv once we write up the arguments.
