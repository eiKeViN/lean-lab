# Independent binary HGP erasure audit

All claims below hold over GF(2), with arbitrary finite input dimensions,
including empty index sets and redundant rows. Physical coordinates are ordered
as VV = V1 × V2 followed by CC = C1 × C2. The check convention is

\[
H_X=[H_1\otimes I_{n_2}\mid I_{m_1}\otimes H_2^T],\qquad
H_Z=[I_{n_1}\otimes H_2\mid H_1^T\otimes I_{m_2}].
\]

Here H_i has m_i rows and n_i columns. Their product H_X H_Z^T is zero
because its two equal tensor summands cancel in characteristic two. Set
N = n1 n2 + m1 m2 and k = N − rank(H_X) − rank(H_Z).

## Arbitrary erasures

For a coordinate subset E, let F^E denote the vectors supported in E, and
let A_E denote the restriction of A to columns E. The Z cycles supported in E
have dimension |E| − rank((H_X)_E). Projection of row(H_Z) onto the complement
of E has image dimension rank((H_Z)_{Eᶜ}); therefore its kernel, the Z
stabilizers supported in E, has dimension
rank(H_Z) − rank((H_Z)_{Eᶜ}). Quotienting the supported cycles by these
supported stabilizers is exactly the image of the supported cycles in the
global logical quotient. Consequently

\[
\ell_Z(E)=|E|-\operatorname{rank}((H_X)_E)
 -\operatorname{rank}H_Z+\operatorname{rank}((H_Z)_{E^c}).
\]

Exchange X and Z for the X formula. Adding the Z formula on E to the X
formula on Eᶜ cancels the restricted ranks and gives

\[
\ell_Z(E)+\ell_X(E^c)=k.
\]

The opposite-sector version follows in the same way. Two binary Pauli errors
supported in E have equal syndrome exactly when their difference has Z part
in ker(H_X)∩F^E and X part in ker(H_Z)∩F^E. Every such pair is stabilizer
equivalent exactly when both supported logical images vanish. Thus the
same-syndrome uniqueness statement is true if and only if
ell_Z(E) = ell_X(E) = 0. Phases are omitted in this binary Pauli formulation.

## A VV strip E = S × V2

Write K_i = ker(H_i), R_i = row(H_i), W = F^S ⊆ F^{n1},
K_1[S] = K_1∩W, and π_S for coordinate projection onto S.

A Z vector supported in VV is a matrix V of shape n1 × n2. Its cycle
condition is H1 V = 0, so supported Z cycles form K_1[S]⊗F^{n2}.
A general Z stabilizer, with coefficient matrix B of shape n1 × m2, is
(B H2, H1 B). Having zero CC component forces every column of B into K_1.
Hence VV-only Z stabilizers form K_1⊗R_2. Their intersection with the strip
is K_1[S]⊗R_2. This uses the tensor intersection identity
(U⊗R)∩(W⊗V) = (U∩W)⊗R for R ⊆ V; it follows by choosing bases adapted
to U∩W, U, W, and R. Therefore

\[
\ell_Z(S\times V_2)
=\dim K_1[S]\,(n_2-\operatorname{rank}H_2)
=\dim K_1[S]\,\dim K_2.
\]

For X, the VV cycle condition is V H2^T = 0, giving strip cycles W⊗K_2.
An X stabilizer with coefficient matrix A of shape m1 × n2 is
(H1^T A, A H2^T). The zero CC condition forces every row of A into K_2,
so VV-only X stabilizers form R_1⊗K_2. The strip intersection is
(R_1∩W)⊗K_2. It follows that

\[
\ell_X(S\times V_2)
=(|S|-\dim(R_1\cap W))\dim K_2
=\dim(\pi_S K_1)\dim K_2.
\]

The last equality is ordinary duality on F^S: the orthogonal complement of
π_S K_1 consists precisely of vectors in F^S whose zero extension belongs
to K_1^⊥ = R_1. These arguments use only subspaces and tensor products;
neither full row rank nor nonempty index sets are assumed.

In the task notation C2 must denote the second **variable/column index set**
for E to be a VV strip. If C2 instead denotes the check/row index set, write
V2 or the column set explicitly to avoid a type mismatch.

## Finite verification

Reproduce from the experiment directory:

```sh
python3 supervision/oracle.py --json supervision/oracle-results.json
```

`oracle.py` uses Python's standard library only. It enumerates every actual
binary word, every actual stabilizer row combination, and canonical cosets.
Supported logical dimensions come from the cardinalities of the resulting
coset images, independently of Gaussian elimination. It also scans supported
errors for same-syndrome coset collisions. Classical shortening and projection
dimensions come from enumerated classical kernel words. The competing rank
formulas use a separate Gaussian-elimination routine.

Fresh run: **passed**.

| Input or comparison | Count |
|---|---:|
| All binary input matrices, each dimension from 0 through 2 | 31 |
| Ordered input pairs | 961 |
| Pairs containing an empty row or column index set | 285 |
| Pairs containing redundant input rows | 792 |
| All physical erasure subsets, at most 8 qubits | 86,617 |
| Actual logical dimension versus rank formula | 173,234 |
| Complementary-sector cleaning equality | 173,234 |
| Same-syndrome uniqueness versus vanishing logical dimension | 173,234 |
| VV strip subsets | 3,131 |
| Actual logical dimension versus strip formula | 6,262 |

The two named examples are also explicitly rechecked:

| H1 = H2 | N | k | d_X | d_Z | ell_Z({0}×V2) | ell_X({0}×V2) |
|---|---:|---:|---:|---:|---:|---:|
| [1 1] | 5 | 1 | 2 | 2 | 0 | 1 |
| 2×2 all ones | 8 | 2 | 2 | 2 | 0 | 1 |

In particular, a strip can contain no nontrivial Z logical while still
containing an X logical. Checking only shortened ker(H1) is insufficient
for Pauli erasure correctability. This finite verification corroborates the
general proofs; it is not a Lean elaboration or a substitute for those proofs.
