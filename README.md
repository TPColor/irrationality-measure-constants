# irrationality-measure-constants

In this repository, we seek to prove several irrationality measure results. Let `μ(·)` be the irrationality measure function.<br>
We prove that for all positive rationals `a/b`, `μ(arctan(a/b)) = 2` and `μ(√(a/b)π) = 2`.


# Reproduce

Install Lean 4.34.0 using your usual Lean installation method. From this directory run in powershell:

```powershell
lake build
```
The build completed successfully under Lean 4.34.0 in our session. There are no `sorry`, `admit`, nor `native_decide`. However, the formalization depends on an axiom, being Theorem 9 of Liu–Jiang–Zhang. The preprint is found at [https://arxiv.org/abs/2610.10192v2](https://arxiv.org/abs/2610.10192v2).


# Credit

Lily Zhang (pink@berkeley.edu), Evan Li (evl012@ucsd.edu).<br>
We plan to publish a preprint on arXiv once we write up the arguments.
