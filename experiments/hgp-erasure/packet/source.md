# Erasure-supported logical information in hypergraph product codes

Work over F₂. All coordinate sets are finite and may be empty. Matrices may
have dependent rows. The results below, including both examples, are targets.
The notes provide mathematical proofs. Choose any equivalent Lean presentation.

## A. The code and its parameters

For matrices H_i : R_i × C_i → F₂, put qubits on the disjoint union
Q = (C₁ × C₂) ⊔ (R₁ × R₂). The X and Z checks, respectively, with the first
block corresponding to the first summand, are

    P = [ H₁ ⊗ I_C₂ | I_R₁ ⊗ H₂ᵀ ],
    D = [ I_C₁ ⊗ H₂ | H₁ᵀ ⊗ I_R₂ ].

They satisfy P Dᵀ = 0: the two product terms are identical in characteristic
two. A Z logical class is a vector of ker P modulo row D, and an X class is
a vector of ker D modulo row P. Write k for the dimension of either quotient.
With K_i = ker H_i and T_i = ker H_iᵀ, the length is
|C₁||C₂| + |R₁||R₂|, and k = dim(K₁)dim(K₂) + dim(T₁)dim(T₂).
Every nonzero logical class in either sector has every representative of weight
at least min(d(K₁),d(K₂),d(T₁),d(T₂)); zero codes have distance infinity.
State and prove these facts for the same checks used below. They may be invoked
from the supplied Tillich–Zémor parameter theorem (QECert, Theorem 4.3).
For the dimension formula one may split each two-term input complex into its
kernel, an isomorphism summand, and its cokernel, and tensor; only products of
homology factors survive. The distance estimate in the supplied theorem uses
the minimum weight over nontrivial pure logical vectors, so it bounds every
representative of a nonzero class.

## B. Logical information supported in an arbitrary erasure

For a binary CSS pair (P,D) of length n with P Dᵀ = 0, let V_E be the space
of words zero outside E ⊆ Q. Define L_Z(E) as the image of ker P ∩ V_E in
ker P / row D. Define L_X(E) by swapping P and D; write z(E), x(E) for the
two actual dimensions. For a check matrix M write M|E for its columns in E,
and Eᶜ for the complement in the full qubit set. Prove both rank identities:

    z(E) + rank(P|E) + rank D = |E| + rank(D|Eᶜ)
    x(E) + rank(D|E) + rank P = |E| + rank(P|Eᶜ).

Indeed ker P ∩ V_E has dimension |E| − rank(P|E). The kernel of its map
to the global quotient is row D ∩ V_E, whose dimension is rank D − rank(D|Eᶜ):
restrict row D to the complementary coordinates and use rank–nullity.
Swapping the two checks gives the second identity. Using
k = n − rank P − rank D, deduce z(E)+x(Eᶜ)=k and x(E)+z(Eᶜ)=k.

## C. Erasure inference and distance

A pair (u,v) of X and Z errors supported in E has syndrome (D u, P v).
Two pairs are equivalent when the difference of their X components belongs
to row P and that of their Z components belongs to row D. Prove that any
two such pairs of equal syndrome are equivalent exactly when x(E)=z(E)=0.
In one direction differences are supported cycles; in the other, compare a
cycle with zero in the same sector. Define failure by this ambiguity. Show
that the least |E| over all failing E is the CSS distance (infinity if there
is no failing E). In fact each logical representative supplies its support,
and each failure supplies a nontrivial representative supported in E.
This task concerns error equivalence in the CSS model; quantum channels and
a circuit-level recovery implementation are outside its mathematical scope.

## D. A whole strip in the physical variable-variable block

Return to the actual HGP checks of A. For S ⊆ C₁ take E = S × C₂ in the first
block, with no check-check qubits. Write K₁[S] for words of K₁ vanishing
outside S, and K₁|S for the image of K₁ under coordinate restriction. Then

    z(E) = dim(K₁[S]) · dim(K₂),
    x(E) = dim(K₁|S) · dim(K₂).

Here is a proof. Regard a word in the first block as a C₁-by-C₂ array.
A strip Z cycle has columns in K₁[S]. Boundaries with second block zero are
obtained from arrays B of shape C₁-by-R₂ with columns in K₁, by the map
B ↦ B H₂. Their first-block span is K₁ ⊗ row H₂. Intersecting with the strip
gives K₁[S] ⊗ row H₂: expand in a basis of row H₂ extended to a basis of the
second factor; coefficients outside S vanish. Quotienting the cycles gives
K₁[S] ⊗ (F₂^{C₂}/row H₂), proving the Z formula. Strip X cycles have their
rows in K₂. X boundaries with second block zero form row H₁ ⊗ K₂, whose
intersection with the strip is (row H₁ ∩ V_S) ⊗ K₂ by the same basis
argument. In F₂^S the orthogonal complement of the restriction of K₁ is
exactly the restriction of row H₁ ∩ V_S, as is seen by extending a word on
S by zero and testing against all of K₁. The quotient therefore has the
claimed X dimension. These arguments also apply when a factor has dimension
zero. Equivalent matrix-rank proofs are welcome.

## E. Calling the results on concrete inputs

1. Both input checks are the single row [1,1]. Show parameters [[5,1,2]].
   A nonzero two-bit repetition word gives weight-two logical representatives;
   all single-qubit erasures succeed by the distance bound. For S={first
   column}, the strip has (z,x)=(0,1), so that erasure fails.
2. Both input checks are the two-by-two all-ones matrix. Show [[8,2,2]].
   For the entire first block (z,x)=(1,1), and the complementary block
   also has (1,1). The transposed kernels have dimension one. The lower
   bound is two, and a two-bit repetition word on one row or column of the
   first block gives a nontrivial logical vector. Justify that the displayed
   representative is nontrivial, or check the upper bound by a certified
   finite calculation.

In both examples the HGP object and the supported dimensions are the ones of
the general results. Reuse of a verified finite computation is allowed.
