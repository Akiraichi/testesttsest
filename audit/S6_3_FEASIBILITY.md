# S6.3 feasibility gate

## Required theorem

For every finite-dimensional real Hermitian space `(E,g,J)`, every real multilinear functional invariant under the full unitary group is a finite linear combination of products of the metric `g` and symplectic form `ω(u,v)=g(u,Jv)` over complete pairings.

## Missing formal infrastructure

1. complexification and the `±i` eigenspace decomposition of `J`;
2. equivariant identification of the negative eigenspace with the dual of the positive eigenspace;
3. transfer from `U(r)` invariance to invariance under the complexified `GL(r,ℂ)` action;
4. the mixed tensor first fundamental theorem for `GL(W)`;
5. descent of complex contractions to real products of `g` and `ω`;
6. product-unitary and symmetric-slot factorization for S6.5.

## Verdict

`REQUIRES_NEW_LIBRARY_DEVELOPMENT`.

Treating the tensor FFT as a global Lean axiom would violate p27 and would not upgrade the result beyond the conditional milestone.
