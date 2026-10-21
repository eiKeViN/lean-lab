import OAI.RepresentationTheory.KazhdanLusztig.DihedralIntervals

open OAI.KLInvariance OAI.KLInvariance.SignedDihedral

example {i j : ℤ} (hij : |i| < |j|) :
    arrowAfter i (i+j) 0 + arrowAfter i (i+j) (-0) = 0 := by
  simpa only [Nat.cast_zero, Nat.not_lt_zero, false_and, ite_false] using
    (arrowAfter_pair hij 0)

example {i j : ℤ} (hij : |i| < |j|) :
    arrowAfter i (i+j) i.natAbs + arrowAfter i (i+j) (-i.natAbs) = 0 := by
  rw [arrowAfter_pair hij]
  simp

example {i j : ℤ} (hij : |i| < |j|) (hj : 0 < j)
    (ho : Odd (i.natAbs+j.natAbs)) :
    arrowAfter i (i+j) j.natAbs + arrowAfter i (i+j) (-j.natAbs) = 1 := by
  rw [arrowAfter_pair hij]
  simp [hj, ho, (OAI.KLInvariance.Dihedral.natAbs_lt_iff i j).mpr hij]

example {i j : ℤ} (hij : |i| < |j|) (hj : j < 0) :
    arrowAfter i (i+j) j.natAbs + arrowAfter i (i+j) (-j.natAbs) = 0 := by
  rw [arrowAfter_pair hij]
  simp [not_lt_of_ge hj.le]

noncomputable def pair (i j : ℤ) (r : ℕ) :=
  arrowAfter i (i+j) r + arrowAfter i (i+j) (-r)

-- Zero, source rank, immediately below/at/above the upper rank, both signs,
-- and both parity outcomes. These checks unfold the original definitions.
example :
    [pair 0 3 0, pair 0 (-3) 0,
     pair 0 3 1, pair 0 (-3) 1,
     pair 0 3 2, pair 0 (-3) 2,
     pair 0 3 3, pair 0 (-3) 3,
     pair 0 3 4, pair 0 (-3) 4,
     pair 0 3 5, pair 0 (-3) 5,
     pair 1 3 1, pair 1 (-3) 1,
     pair 1 3 2, pair 1 (-3) 2,
     pair 1 3 3, pair 1 (-3) 3,
     pair 1 3 4, pair 1 (-3) 4,
     pair (-1) 3 2, pair (-1) (-3) 2] =
    [0,0, 1,1, 0,0, 1,0, 0,0, 2,0, 0,0, 1,1, 0,0, 2,0, 1,1] := by
  norm_num [pair, arrowAfter, Before, Int.odd_iff]

-- Empty eligible range, literal c=j (including a negative top), and higher top.
example :
    [countAfter 0 1 1, countAfter 0 (-1) (-1),
     countAfter 0 1 3, countAfter 0 (-1) 3,
     countAfter 0 3 3, countAfter 0 (-3) (-3),
     countAfter 0 3 5, countAfter 0 (-3) 5] = [0,0,2,0,1,1,3,1] := by
  norm_num [countAfter, arrowAfter, Before, Int.odd_iff, Finset.sum_range_succ]
