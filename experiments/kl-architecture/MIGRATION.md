# Source migration index

Reference: `../kl-kernel-transport` at `7ddc53ba8a09ed902fefff86e67a87217518c1d4`.
Ranges below are inclusive, 1-based reference lines. Mathematical bodies are unchanged.
Existing anonymous instance names are pinned explicitly; Hecke inverse proofs restore their original local instance attribute.
Old module paths are import-only compatibility entries.

## Old file → semantic homes

### BalancedPairings.lean

- `OAI/Algebra/Module/Graded/ModuleData/Range.lean` ← 839–862, 1513–1522, 626–680
- `OAI/Combinatorics/MomentGraph/Boundary/Summand.lean` ← 1965–2001
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Summand.lean` ← 1524–1552, 1629–1679, 466–515, 864–908, 918–964, 1305–1396, 1770–1907, 1917–1963
- `OAI/LinearAlgebra/ConjugateRange.lean` ← 971–1005
- `OAI/LinearAlgebra/Descent.lean` ← 594–619
- `OAI/LinearAlgebra/Dual/Adjoint.lean` ← 1687–1699, 1126–1151, 1158–1180
- `OAI/LinearAlgebra/Dual/Summand.lean` ← 1016–1117
- `OAI/LinearAlgebra/Dual/TransportPairing.lean` ← 306–328
- `OAI/RepresentationTheory/BottSamelson/AdjointSheaf.lean` ← 1187–1199, 167–299, 339–404, 11–84, 414–456, 94–157, 2043–2098, 524–587, 691–756, 766–830, 1209–1295, 1454–1506, 1562–1620, 1406–1443, 1701–1760, 2011–2033

### BottSamelson.lean

- `OAI/Algebra/Module/CoefficientChange/Basic.lean` ← 1749–1822
- `OAI/Algebra/Module/Free/ScalarDivisibility.lean` ← 892–949
- `OAI/Algebra/Module/Graded/DualAndShift.lean` ← 559–613, 1658–1690, 1620–1650, 1347–1402, 1830–1883
- `OAI/Algebra/Module/ReflectionPair/TensorKernel.lean` ← 526–550, 699–736, 1202–1269
- `OAI/LinearAlgebra/TensorProduct/Coordinates.lean` ← 12–47, 793–806
- `OAI/RepresentationTheory/BottSamelson/Stalks.lean` ← 54–81, 231–321, 743–787, 331–404, 958–1047, 414–517, 91–221, 1413–1494, 622–689, 813–885, 1054–1102, 1276–1338, 1110–1195, 1504–1537, 1547–1611, 1893–1934, 1945–2021, 1700–1740

### Bruhat.lean

- `OAI/Data/Polynomial/ReciprocalRigidity.lean` ← 138–148
- `OAI/GroupTheory/Coxeter/Bruhat/Basic.lean` ← 10–43, 71–109, 210–527
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/SelectedR.lean` ← 45–57
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/Unique.lean` ← 110–137, 149–208

### CanonicalKL.lean

- `OAI/Data/Polynomial/LowPart.lean` ← 22–67
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/Canonical.lean` ← 68–469

### CharacterReciprocity.lean

- `OAI/Algebra/Module/Graded/ModuleData/CharacterDual.lean` ← 2049–2075, 1046–1066
- `OAI/Algebra/Module/Graded/ModuleData/CoefficientChange.lean` ← 1578–1600, 1522–1571, 1662–1691
- `OAI/Combinatorics/MomentGraph/Boundary/Models.lean` ← 1156–1190, 1693–1724
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Models.lean` ← 568–629, 1602–1655, 780–796, 1835–1906, 64–89, 1285–1311, 636–773, 1971–2004
- `OAI/Combinatorics/MomentGraph/Sheaf/Models.lean` ← 340–429, 436–559
- `OAI/LinearAlgebra/Dual/BalancedCut.lean` ← 38–57
- `OAI/RepresentationTheory/BottSamelson/Character.lean` ← 1320–1372, 1381–1425, 1200–1278, 1434–1480, 1489–1515, 858–930, 1075–1147
- `OAI/RepresentationTheory/BottSamelson/CharacterDecomposition.lean` ← 2011–2042
- `OAI/RepresentationTheory/Hecke/PositiveWord.lean` ← 939–1015, 1022–1039
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/FreeModel.lean` ← 11–29, 97–123, 133–330, 798–849, 2082–2115, 2122–2188
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/Reciprocity.lean` ← 1732–1764, 1772–1828, 1913–1964

### Comparison.lean

- `OAI/Combinatorics/DirectedPaths/PositiveTransfer.lean` ← 66–144
- `OAI/Data/Polynomial/ReciprocalRigidity.lean` ← 21–65

### Coxeter.lean

- `OAI/GroupTheory/Coxeter/Exchange.lean` ← 12–237

### Decomposition.lean

- `OAI/Algebra/Algebra/ReflectionFrobenius/Basic.lean` ← 1428–1697
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Character.lean` ← 11–88
- `OAI/GroupTheory/Coxeter/Bruhat/Diamonds.lean` ← 1342–1418
- `OAI/GroupTheory/Coxeter/Dihedral/PlaneSystem.lean` ← 235–370, 1239–1273
- `OAI/GroupTheory/Coxeter/Roots/PlaneBasis.lean` ← 374–1237, 1275–1340
- `OAI/LinearAlgebra/PairProjection/Basic.lean` ← 144–226
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/LowerCharacter.lean` ← 95–134

### Dihedral.lean

- `OAI/GroupTheory/Coxeter/Bruhat/Transport.lean` ← 11–66
- `OAI/GroupTheory/Coxeter/Dihedral/Words.lean` ← 68–134, 136–187
- `OAI/RepresentationTheory/Hecke/Dihedral.lean` ← 189–277, 279–379, 482–565, 567–662
- `OAI/RepresentationTheory/Hecke/DualR.lean` ← 381–480
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/Normalization.lean` ← 668–798

### DihedralIntervals.lean

- `OAI/Combinatorics/Dihedral/SignedCount.lean` ← 914–1064, 1452–1600, 1609–1757
- `OAI/Combinatorics/MomentGraph/Bruhat/DihedralModel.lean` ← 218–323, 454–594
- `OAI/Combinatorics/MomentGraph/Sheaf/FlowDown.lean` ← 333–445
- `OAI/GroupTheory/Coxeter/Dihedral/SignedWords.lean` ← 11–120, 640–689, 696–793, 1765–1783, 800–816, 1072–1081, 1276–1367, 1374–1444
- `OAI/GroupTheory/Coxeter/Roots/DihedralOrder.lean` ← 818–905, 1083–1219, 1226–1269
- `OAI/GroupTheory/Coxeter/Roots/LaterCount.lean` ← 1785–1884, 1891–1987, 1994–2074, 2081–2242
- `OAI/GroupTheory/Coxeter/Roots/Splines.lean` ← 129–208
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/PlaneModel.lean` ← 603–631

### DyerPaths.lean

- `OAI/Algebra/BigOperators/FiniteCharacterCancellation.lean` ← 11–40
- `OAI/Combinatorics/DirectedPaths/Subpaths.lean` ← 1655–1702, 1777–1819, 1821–1852
- `OAI/GroupTheory/Coxeter/Bruhat/Diamonds.lean` ← 168–247, 625–666
- `OAI/GroupTheory/Coxeter/Dihedral/IntervalTransport.lean` ← 336–372, 952–1066, 1556–1653, 483–623
- `OAI/GroupTheory/Coxeter/Parabolic/InversionList.lean` ← 112–166
- `OAI/GroupTheory/Coxeter/Roots/PlaneTransport.lean` ← 255–334, 374–481, 668–723, 725–829
- `OAI/GroupTheory/Coxeter/Roots/RatioOrder.lean` ← 1130–1546, 837–950, 1068–1120, 1704–1775, 1854–1929
- `OAI/RepresentationTheory/Hecke/DyerPaths/Adapted.lean` ← 1939–2495
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/StalkReciprocity.lean` ← 50–103

### EdgeLocalization.lean

- `OAI/Algebra/Module/Graded/ModuleData/CoverUniqueness.lean` ← 472–504
- `OAI/Algebra/Module/Graded/RegularScalar.lean` ← 1035–1088
- `OAI/Combinatorics/DirectedPaths/ScalarMap.lean` ← 136–153
- `OAI/Combinatorics/MomentGraph/Boundary/Uniqueness.lean` ← 640–685, 734–770
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean` ← 585–631, 692–727, 933–959, 777–799
- `OAI/Combinatorics/MomentGraph/Sheaf/Uniqueness.lean` ← 511–578
- `OAI/LinearAlgebra/Dual/IntegralSupport.lean` ← 1096–1117
- `OAI/RepresentationTheory/BottSamelson/CanonicalPairing.lean` ← 809–854, 863–926, 969–996
- `OAI/RepresentationTheory/KazhdanLusztig/Comparison/Transport.lean` ← 253–284, 293–345, 11–127, 197–245, 998–1024, 353–462
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/ScaledReciprocity.lean` ← 155–195

### Frobenius.lean

- `OAI/Algebra/Algebra/ReflectionFrobenius/Basis.lean` ← 1130–1193, 513–545, 447–504, 657–759
- `OAI/Algebra/Module/Graded/AlgebraMap.lean` ← 843–928, 632–655, 429–445
- `OAI/Algebra/Module/ReflectionPair/Twist.lean` ← 2038–2215
- `OAI/LinearAlgebra/Dual/Frobenius.lean` ← 103–187, 189–212, 221–282, 290–376, 554–625
- `OAI/LinearAlgebra/PairProjection/Kernel.lean` ← 1840–1865
- `OAI/RepresentationTheory/BottSamelson/Words.lean` ← 11–93, 387–420, 1349–1385, 769–834, 938–1033, 1625–1663, 1043–1121, 1204–1300, 1672–1733, 1309–1340, 1395–1479, 1490–1616, 1744–1831, 1875–2028

### GradedModules.lean

- `OAI/Algebra/Module/Graded/Generators.lean` ← 675–877, 11–483, 582–668, 884–1038
- `OAI/Algebra/Module/Graded/ModuleData/Basic.lean` ← 1045–1212, 1220–1313, 1322–1448
- `OAI/Algebra/Module/Projective/ScalarQuotient.lean` ← 486–575

### GradedSheaves.lean

- `OAI/Algebra/Module/Cover/Product.lean` ← 868–886
- `OAI/Algebra/Module/Graded/ModuleData/Equality.lean` ← 246–259, 371–387
- `OAI/Algebra/Module/Quotient/EdgeEquiv.lean` ← 907–947
- `OAI/Algebra/Module/Submodule/ScaledImage.lean` ← 650–675
- `OAI/Combinatorics/MomentGraph/Boundary/Basic.lean` ← 1129–1242
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Basic.lean` ← 13–92, 99–239, 261–364, 389–508
- `OAI/Combinatorics/MomentGraph/Sheaf/Isomorphism.lean` ← 516–648, 683–806, 813–866, 957–1043, 888–900, 1050–1122

### Hecke.lean

- `OAI/Data/Polynomial/ReflectEvaluation.lean` ← 1100–1114
- `OAI/GroupTheory/Coxeter/Bruhat/LowerFinset.lean` ← 1039–1049
- `OAI/RepresentationTheory/Hecke/Inverse.lean` ← 1050–1098
- `OAI/RepresentationTheory/Hecke/Operators.lean` ← 19–505, 508–1037

### HilbertSeries.lean

- `OAI/Algebra/Module/Graded/Hilbert/Series.lean` ← 11–114, 122–330, 338–420, 427–543

### IntegralPairings.lean

- `OAI/Algebra/Module/Graded/Adjoint.lean` ← 2275–2324, 2331–2356
- `OAI/Algebra/Module/Graded/Hilbert/RationalFunction.lean` ← 11–68
- `OAI/Algebra/Module/Localization/FiniteCharacters.lean` ← 1658–1858
- `OAI/Algebra/Module/Localization/ProjectiveLattice.lean` ← 1866–1934
- `OAI/Algebra/Module/Projective/Range.lean` ← 482–547, 1326–1359
- `OAI/Algebra/Module/Projective/Transport.lean` ← 985–1007
- `OAI/Algebra/Module/ReflectionPair/TensorDescent.lean` ← 554–582, 754–779
- `OAI/LinearAlgebra/CoordinateProjection.lean` ← 314–369
- `OAI/LinearAlgebra/Dual/Adjoint.lean` ← 2212–2267
- `OAI/LinearAlgebra/KernelCoordinates.lean` ← 589–613, 1014–1072
- `OAI/LinearAlgebra/PairProjection/Lifting.lean` ← 786–803
- `OAI/LinearAlgebra/Reflection/Classification.lean` ← 1435–1474
- `OAI/RepresentationTheory/BottSamelson/Pairings.lean` ← 1484–1556, 1565–1649, 377–474, 1943–2068, 621–747, 812–882, 889–978, 1251–1319, 1079–1138, 1145–1242, 1366–1426, 78–137, 2077–2118, 228–305, 2127–2203
- `OAI/RepresentationTheory/Hecke/Coefficients.lean` ← 147–219

### Invariance.lean

- `OAI/RepresentationTheory/KazhdanLusztig/Invariance/Finite.lean` ← 257–317, 325–384, 64–114, 125–209, 395–460
- `OAI/RepresentationTheory/KazhdanLusztig/Invariance/FiniteModel.lean` ← 470–531
- `OAI/RepresentationTheory/KazhdanLusztig/Invariance/Induction.lean` ← 11–55, 217–255
- `OAI/RepresentationTheory/KazhdanLusztig/Invariance/Main.lean` ← 541–565

### MinimalExtensions.lean

- `OAI/Algebra/Module/Graded/ModuleData/Transport.lean` ← 428–456, 177–201
- `OAI/Combinatorics/MomentGraph/Boundary/Extension.lean` ← 792–874
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Extension.lean` ← 12–76, 85–101, 203–259, 515–639, 1634–1727, 458–506, 648–735
- `OAI/Combinatorics/MomentGraph/Sheaf/Extension.lean` ← 982–1047, 1094–1186, 882–975, 1054–1087, 1319–1411, 1194–1310, 1582–1625, 1413–1442, 103–170, 744–783
- `OAI/Combinatorics/MomentGraph/Sheaf/Zero.lean` ← 266–369, 1452–1575, 376–421

### Model.lean

- `OAI/GroupTheory/Coxeter/Bruhat/Defs.lean` ← 14–47
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/Normalized.lean` ← 48–79

### ModuleAlgebra.lean

- `OAI/Algebra/Module/Cover/Local.lean` ← 157–235
- `OAI/Algebra/Module/Graded/Components.lean` ← 275–370, 434–487
- `OAI/Algebra/Module/Graded/Hilbert/Basic.lean` ← 494–615
- `OAI/Algebra/Module/Localization/Lattice.lean` ← 12–147
- `OAI/Algebra/Module/Projective/ReverseFiltration.lean` ← 238–272
- `OAI/Algebra/Module/Quotient/EdgeImage.lean` ← 373–428

### OrdinaryR.lean

- `OAI/RepresentationTheory/Hecke/OrdinaryR.lean` ← 10–297

### PlaneLocalization.lean

- `OAI/Algebra/Module/Localization/Products.lean` ← 1482–1536
- `OAI/Combinatorics/MomentGraph/Sheaf/Localization.lean` ← 529–546, 783–849, 614–662, 283–304, 139–190, 851–887, 197–259
- `OAI/LinearAlgebra/PlaneReduction.lean` ← 1263–1288
- `OAI/LinearAlgebra/SymmetricAlgebra/Quotient.lean` ← 11–132
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/Ambient.lean` ← 268–281, 1348–1475, 1685–1705, 1204–1222
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/Embed.lean` ← 338–397, 1297–1341, 1543–1618
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/Plane.lean` ← 430–519, 306–329, 548–605, 399–421, 934–982, 671–774, 1087–1127, 1625–1678, 989–1080, 1134–1197, 1224–1253, 1707–1749
- `OAI/RingTheory/Localization/RelativePrime.lean` ← 897–925

### PositiveTransfer.lean

- `OAI/Algebra/Module/Graded/Hilbert/Increment.lean` ← 254–344
- `OAI/Algebra/Module/Projective/ScalarKernel.lean` ← 922–1008
- `OAI/Combinatorics/DirectedPaths/Monotone.lean` ← 216–247, 816–915
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Hilbert.lean` ← 351–460
- `OAI/Data/Polynomial/ScaledComparison.lean` ← 531–573
- `OAI/RepresentationTheory/KazhdanLusztig/Comparison/Propagation.lean` ← 467–524, 1015–1071, 11–73, 580–656, 666–756, 764–808, 1078–1199, 1210–1324, 85–207

### ReflectionOrders.lean

- `OAI/Combinatorics/DirectedPaths/SortedSchedule.lean` ← 575–693
- `OAI/Combinatorics/DirectedPaths/Transfer.lean` ← 11–248
- `OAI/Data/Polynomial/Avoidance.lean` ← 815–846
- `OAI/GroupTheory/Coxeter/Roots/ReflectionOrder.lean` ← 257–358, 848–966
- `OAI/RepresentationTheory/Hecke/DyerPaths/LexicographicOrder.lean` ← 702–806
- `OAI/RepresentationTheory/Hecke/DyerPaths/PlaneCoordinates.lean` ← 367–567
- `OAI/RepresentationTheory/Hecke/DyerPaths/Wall.lean` ← 974–1143, 1152–1237

### ReflectionPlane.lean

- `OAI/LinearAlgebra/Reflection/Plane.lean` ← 12–95

### ReflectionSchedules.lean

- `OAI/Combinatorics/DirectedPaths/Basic.lean` ← 1154–1300
- `OAI/Data/Polynomial/Avoidance.lean` ← 12–77
- `OAI/GroupTheory/Coxeter/Bruhat/DiamondClosure.lean` ← 1553–1578
- `OAI/GroupTheory/Coxeter/Dihedral/Diamonds.lean` ← 1582–1692, 1694–1771
- `OAI/GroupTheory/Coxeter/Roots/Order.lean` ← 79–157, 159–288, 290–366, 368–493, 632–693, 495–630
- `OAI/GroupTheory/Coxeter/Roots/PlaneLength.lean` ← 695–751, 887–1001, 1106–1151
- `OAI/GroupTheory/Coxeter/Roots/ReflectionLabels.lean` ← 1360–1393, 1396–1521
- `OAI/LinearAlgebra/Reflection/Plane.lean` ← 1302–1358
- `OAI/LinearAlgebra/SymmetricAlgebra/RootIdeal.lean` ← 753–885, 1003–1039, 1041–1104
- `OAI/Order/Interval/Diamonds.lean` ← 1523–1552

### SheafMorphisms.lean

- `OAI/Algebra/Module/Graded/ModuleData/Character.lean` ← 1702–1726, 1735–1842
- `OAI/Algebra/Module/Graded/ModuleData/MinimalCover.lean` ← 956–980, 1161–1203, 1306–1327, 1417–1476, 447–496, 1034–1076
- `OAI/Algebra/Module/Graded/ModuleData/QuotientHom.lean` ← 533–556
- `OAI/Algebra/Module/Graded/NonnegativeBasis.lean` ← 110–128, 413–445, 11–103
- `OAI/Algebra/Module/Quotient/EdgeHom.lean` ← 503–531
- `OAI/Combinatorics/MomentGraph/Boundary/Hom.lean` ← 1078–1152, 1238–1299, 1363–1407
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Hom.lean` ← 989–1032, 1212–1236, 563–701, 708–799, 1329–1361, 809–892, 1553–1621, 899–946, 1628–1693
- `OAI/Combinatorics/MomentGraph/Sheaf/Hom.lean` ← 1483–1546
- `OAI/GroupTheory/Coxeter/Bruhat/Descent.lean` ← 237–326
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/Boundary.lean` ← 130–185, 193–228, 336–406

### Sheaves.lean

- `OAI/Combinatorics/MomentGraph/Sheaf/Basic.lean` ← 17–147, 153–244

### SimultaneousInvariance.lean

- `OAI/Data/Polynomial/ScaledComparison.lean` ← 460–474, 321–375
- `OAI/RepresentationTheory/KazhdanLusztig/Comparison/Freeness.lean` ← 155–233, 11–97, 106–148, 242–313, 386–458

### Support.lean

- `OAI/Algebra/Module/CoefficientChange/Dual.lean` ← 1762–1833
- `OAI/Algebra/Module/Graded/Hilbert/Images.lean` ← 1115–1202, 1209–1288
- `OAI/Algebra/Module/Graded/HomogeneousDual.lean` ← 1514–1534, 696–730
- `OAI/Algebra/Module/Graded/ModuleData/Duality.lean` ← 220–233, 11–60, 739–806
- `OAI/Combinatorics/MomentGraph/GradedSheaf/Duality.lean` ← 1474–1507, 864–877, 1295–1334, 319–400, 1842–1910, 136–213
- `OAI/Combinatorics/MomentGraph/Sheaf/Duality.lean` ← 813–862, 884–1046
- `OAI/LinearAlgebra/Dual/BalancedCut.lean` ← 583–603
- `OAI/LinearAlgebra/Dual/IntegralSupport.lean` ← 470–575
- `OAI/RepresentationTheory/BottSamelson/Support.lean` ← 110–127, 664–689, 611–657, 70–102, 242–312, 409–462
- `OAI/RepresentationTheory/KazhdanLusztig/Sheaves/Support.lean` ← 1627–1675, 1053–1108, 1341–1392, 1400–1466, 1542–1618, 1683–1755

### TerminalKernels.lean

- `OAI/Algebra/Module/Flat/Kernel.lean` ← 272–302
- `OAI/Algebra/Module/Localization/Membership.lean` ← 901–930
- `OAI/Algebra/Module/Quotient/ScalarImage.lean` ← 564–646, 861–894
- `OAI/Combinatorics/DirectedPaths/Suffix.lean` ← 1368–1400
- `OAI/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean` ← 773–807, 309–375, 11–45, 937–977, 52–102
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/Edge.lean` ← 508–555, 653–717, 724–766, 814–854, 984–1025, 450–501, 1033–1103, 1111–1188, 1196–1251, 1260–1361
- `OAI/RepresentationTheory/KazhdanLusztig/Localization/Terminal.lean` ← 190–223, 109–182, 231–264, 382–441

### Tits.lean

- `OAI/Combinatorics/MomentGraph/Bruhat/Basic.lean` ← 15–101
- `OAI/GroupTheory/Coxeter/Parabolic/Standard.lean` ← 1395–1510, 1519–1587
- `OAI/GroupTheory/Coxeter/Parabolic/Support.lean` ← 753–804, 629–751
- `OAI/GroupTheory/Coxeter/Realization/Cotangent.lean` ← 1308–1393
- `OAI/GroupTheory/Coxeter/Realization/Faithful.lean` ← 1109–1233, 1235–1304
- `OAI/GroupTheory/Coxeter/Realization/Geometric.lean` ← 296–356
- `OAI/GroupTheory/Coxeter/Realization/Positivity.lean` ← 806–902, 904–1008
- `OAI/GroupTheory/Coxeter/Realization/Tits.lean` ← 358–432, 547–627
- `OAI/GroupTheory/Coxeter/Roots/Basic.lean` ← 1649–1830, 1832–1974, 1976–2082
- `OAI/GroupTheory/Coxeter/Roots/PlaneSubgroup.lean` ← 2084–2155, 2157–2266
- `OAI/LinearAlgebra/Reflection/Forms.lean` ← 1010–1107, 105–188, 192–294, 434–545
- `OAI/RepresentationTheory/KazhdanLusztig/Polynomials/Parabolic.lean` ← 1588–1645

## Semantic modules → direct OAI imports

Every implementation also imports the pinned Mathlib.

- `OAI.Algebra.Algebra.ReflectionFrobenius.Basic`: (Mathlib only)
- `OAI.Algebra.Algebra.ReflectionFrobenius.Basis`: `OAI.Algebra.Algebra.ReflectionFrobenius.Basic`, `OAI.Algebra.Module.Graded.AlgebraMap`
- `OAI.Algebra.BigOperators.FiniteCharacterCancellation`: (Mathlib only)
- `OAI.Algebra.Module.CoefficientChange.Basic`: (Mathlib only)
- `OAI.Algebra.Module.CoefficientChange.Dual`: `OAI.Algebra.Module.CoefficientChange.Basic`
- `OAI.Algebra.Module.Cover.Local`: (Mathlib only)
- `OAI.Algebra.Module.Cover.Product`: (Mathlib only)
- `OAI.Algebra.Module.Flat.Kernel`: (Mathlib only)
- `OAI.Algebra.Module.Free.ScalarDivisibility`: (Mathlib only)
- `OAI.Algebra.Module.Graded.Adjoint`: `OAI.Algebra.Module.Graded.Generators`, `OAI.LinearAlgebra.Dual.Adjoint`
- `OAI.Algebra.Module.Graded.AlgebraMap`: `OAI.Algebra.Module.Graded.Generators`
- `OAI.Algebra.Module.Graded.Components`: (Mathlib only)
- `OAI.Algebra.Module.Graded.DualAndShift`: `OAI.Algebra.Module.CoefficientChange.Basic`, `OAI.Algebra.Module.Graded.AlgebraMap`, `OAI.Algebra.Module.Graded.ModuleData.Basic`, `OAI.LinearAlgebra.PairProjection.Basic`
- `OAI.Algebra.Module.Graded.Generators`: `OAI.Algebra.Module.Graded.Components`
- `OAI.Algebra.Module.Graded.Hilbert.Basic`: (Mathlib only)
- `OAI.Algebra.Module.Graded.Hilbert.Images`: `OAI.Algebra.Module.Graded.Hilbert.Series`
- `OAI.Algebra.Module.Graded.Hilbert.Increment`: `OAI.Algebra.Module.Graded.Hilbert.Series`
- `OAI.Algebra.Module.Graded.Hilbert.RationalFunction`: (Mathlib only)
- `OAI.Algebra.Module.Graded.Hilbert.Series`: `OAI.Algebra.Module.Graded.Generators`, `OAI.Algebra.Module.Graded.Hilbert.Basic`
- `OAI.Algebra.Module.Graded.HomogeneousDual`: `OAI.Algebra.Module.Graded.DualAndShift`
- `OAI.Algebra.Module.Graded.ModuleData.Basic`: `OAI.Algebra.Module.Graded.Generators`
- `OAI.Algebra.Module.Graded.ModuleData.Character`: `OAI.Algebra.Module.Graded.ModuleData.Basic`, `OAI.Algebra.Module.Graded.NonnegativeBasis`
- `OAI.Algebra.Module.Graded.ModuleData.CharacterDual`: `OAI.Algebra.Module.Graded.ModuleData.Duality`
- `OAI.Algebra.Module.Graded.ModuleData.CoefficientChange`: `OAI.Algebra.Module.Graded.ModuleData.Duality`
- `OAI.Algebra.Module.Graded.ModuleData.CoverUniqueness`: `OAI.Algebra.Module.Graded.ModuleData.Basic`
- `OAI.Algebra.Module.Graded.ModuleData.Duality`: `OAI.Algebra.Module.Graded.HomogeneousDual`, `OAI.Algebra.Module.Graded.ModuleData.Character`, `OAI.Algebra.Module.Graded.ModuleData.Equality`, `OAI.Algebra.Module.Graded.ModuleData.Transport`
- `OAI.Algebra.Module.Graded.ModuleData.Equality`: `OAI.Algebra.Module.Graded.ModuleData.Basic`
- `OAI.Algebra.Module.Graded.ModuleData.MinimalCover`: `OAI.Algebra.Module.Cover.Local`, `OAI.Algebra.Module.Graded.ModuleData.Equality`, `OAI.Algebra.Module.Graded.NonnegativeBasis`
- `OAI.Algebra.Module.Graded.ModuleData.QuotientHom`: `OAI.Algebra.Module.Graded.ModuleData.Basic`, `OAI.Algebra.Module.Quotient.EdgeHom`
- `OAI.Algebra.Module.Graded.ModuleData.Range`: `OAI.Algebra.Module.Graded.DualAndShift`, `OAI.LinearAlgebra.Descent`
- `OAI.Algebra.Module.Graded.ModuleData.Transport`: `OAI.Algebra.Module.Graded.ModuleData.Basic`, `OAI.Algebra.Module.Quotient.EdgeEquiv`
- `OAI.Algebra.Module.Graded.NonnegativeBasis`: `OAI.Algebra.Module.Graded.Hilbert.Series`
- `OAI.Algebra.Module.Graded.RegularScalar`: `OAI.Algebra.Module.Graded.HomogeneousDual`
- `OAI.Algebra.Module.Localization.FiniteCharacters`: (Mathlib only)
- `OAI.Algebra.Module.Localization.Lattice`: (Mathlib only)
- `OAI.Algebra.Module.Localization.Membership`: (Mathlib only)
- `OAI.Algebra.Module.Localization.Products`: (Mathlib only)
- `OAI.Algebra.Module.Localization.ProjectiveLattice`: (Mathlib only)
- `OAI.Algebra.Module.Projective.Range`: (Mathlib only)
- `OAI.Algebra.Module.Projective.ReverseFiltration`: (Mathlib only)
- `OAI.Algebra.Module.Projective.ScalarKernel`: `OAI.Algebra.Module.Graded.Hilbert.Images`, `OAI.Algebra.Module.Projective.ReverseFiltration`
- `OAI.Algebra.Module.Projective.ScalarQuotient`: `OAI.Algebra.Module.Projective.ReverseFiltration`
- `OAI.Algebra.Module.Projective.Transport`: `OAI.Algebra.Module.ReflectionPair.Twist`
- `OAI.Algebra.Module.Quotient.EdgeEquiv`: (Mathlib only)
- `OAI.Algebra.Module.Quotient.EdgeHom`: (Mathlib only)
- `OAI.Algebra.Module.Quotient.EdgeImage`: (Mathlib only)
- `OAI.Algebra.Module.Quotient.ScalarImage`: `OAI.Algebra.Module.Free.ScalarDivisibility`, `OAI.Algebra.Module.Quotient.EdgeEquiv`
- `OAI.Algebra.Module.ReflectionPair.TensorDescent`: `OAI.Algebra.Module.ReflectionPair.TensorKernel`
- `OAI.Algebra.Module.ReflectionPair.TensorKernel`: `OAI.Algebra.Module.ReflectionPair.Twist`
- `OAI.Algebra.Module.ReflectionPair.Twist`: `OAI.LinearAlgebra.PairProjection.Basic`
- `OAI.Algebra.Module.Submodule.ScaledImage`: (Mathlib only)
- `OAI.Combinatorics.Dihedral.SignedCount`: (Mathlib only)
- `OAI.Combinatorics.DirectedPaths.Basic`: (Mathlib only)
- `OAI.Combinatorics.DirectedPaths.Monotone`: `OAI.Combinatorics.DirectedPaths.Basic`
- `OAI.Combinatorics.DirectedPaths.PositiveTransfer`: (Mathlib only)
- `OAI.Combinatorics.DirectedPaths.ScalarMap`: `OAI.Combinatorics.DirectedPaths.Basic`
- `OAI.Combinatorics.DirectedPaths.SortedSchedule`: `OAI.Combinatorics.DirectedPaths.Transfer`
- `OAI.Combinatorics.DirectedPaths.Subpaths`: `OAI.Combinatorics.DirectedPaths.Basic`
- `OAI.Combinatorics.DirectedPaths.Suffix`: (Mathlib only)
- `OAI.Combinatorics.DirectedPaths.Transfer`: `OAI.Combinatorics.DirectedPaths.Subpaths`
- `OAI.Combinatorics.MomentGraph.Boundary.Basic`: `OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism`
- `OAI.Combinatorics.MomentGraph.Boundary.Extension`: `OAI.Combinatorics.MomentGraph.Sheaf.Extension`
- `OAI.Combinatorics.MomentGraph.Boundary.Hom`: `OAI.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `OAI.Combinatorics.MomentGraph.Boundary.Models`: `OAI.Combinatorics.MomentGraph.Boundary.Summand`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Models`
- `OAI.Combinatorics.MomentGraph.Boundary.Summand`: `OAI.Combinatorics.MomentGraph.Boundary.Hom`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Summand`
- `OAI.Combinatorics.MomentGraph.Boundary.Uniqueness`: `OAI.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`, `OAI.Combinatorics.MomentGraph.Sheaf.Uniqueness`
- `OAI.Combinatorics.MomentGraph.Bruhat.Basic`: `OAI.Combinatorics.MomentGraph.Sheaf.Basic`, `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.Combinatorics.MomentGraph.Bruhat.DihedralModel`: `OAI.Combinatorics.MomentGraph.Bruhat.Basic`, `OAI.Combinatorics.MomentGraph.Sheaf.FlowDown`, `OAI.GroupTheory.Coxeter.Bruhat.Descent`, `OAI.GroupTheory.Coxeter.Dihedral.Diamonds`, `OAI.GroupTheory.Coxeter.Roots.Splines`, `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Basic`: `OAI.Algebra.Module.Graded.ModuleData.Equality`, `OAI.Combinatorics.MomentGraph.Sheaf.Basic`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Character`: `OAI.Algebra.Module.Graded.ModuleData.Character`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`: `OAI.Algebra.Module.CoefficientChange.Dual`, `OAI.Algebra.Module.Graded.Adjoint`, `OAI.Algebra.Module.Graded.Hilbert.Images`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Summand`, `OAI.Combinatorics.MomentGraph.Sheaf.Duality`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension`: `OAI.Algebra.Module.Graded.Hilbert.Series`, `OAI.Algebra.Module.Graded.ModuleData.Transport`, `OAI.Combinatorics.MomentGraph.Boundary.Basic`, `OAI.Combinatorics.MomentGraph.Sheaf.Zero`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Hilbert`: `OAI.Algebra.Module.Graded.Hilbert.Increment`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Hom`: `OAI.Algebra.Module.Graded.ModuleData.QuotientHom`, `OAI.Combinatorics.MomentGraph.Sheaf.Hom`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Models`: `OAI.Algebra.Module.Graded.ModuleData.CoefficientChange`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Character`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`, `OAI.Combinatorics.MomentGraph.Sheaf.Extension`, `OAI.Combinatorics.MomentGraph.Sheaf.Models`, `OAI.LinearAlgebra.Dual.BalancedCut`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Summand`: `OAI.Algebra.Module.Graded.ModuleData.Range`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `OAI.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`: `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`
- `OAI.Combinatorics.MomentGraph.Sheaf.Basic`: (Mathlib only)
- `OAI.Combinatorics.MomentGraph.Sheaf.Duality`: `OAI.Algebra.Module.Free.ScalarDivisibility`, `OAI.Combinatorics.MomentGraph.Sheaf.Basic`, `OAI.LinearAlgebra.Dual.IntegralSupport`
- `OAI.Combinatorics.MomentGraph.Sheaf.Extension`: `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `OAI.Combinatorics.MomentGraph.Sheaf.FlowDown`: `OAI.Combinatorics.MomentGraph.Sheaf.Extension`
- `OAI.Combinatorics.MomentGraph.Sheaf.Hom`: `OAI.Algebra.Module.Graded.ModuleData.MinimalCover`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism`: `OAI.Algebra.Module.Cover.Local`, `OAI.Algebra.Module.Cover.Product`, `OAI.Algebra.Module.Quotient.EdgeEquiv`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Basic`
- `OAI.Combinatorics.MomentGraph.Sheaf.Localization`: `OAI.Combinatorics.MomentGraph.Sheaf.Extension`, `OAI.Combinatorics.MomentGraph.Sheaf.Models`
- `OAI.Combinatorics.MomentGraph.Sheaf.Models`: `OAI.Combinatorics.MomentGraph.Sheaf.Zero`
- `OAI.Combinatorics.MomentGraph.Sheaf.ScaledImages`: `OAI.Algebra.Module.Flat.Kernel`, `OAI.Algebra.Module.Localization.Membership`, `OAI.Algebra.Module.Localization.Products`, `OAI.Combinatorics.MomentGraph.Sheaf.Localization`
- `OAI.Combinatorics.MomentGraph.Sheaf.Uniqueness`: `OAI.Algebra.Module.Graded.ModuleData.CoverUniqueness`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `OAI.Combinatorics.MomentGraph.Sheaf.Zero`: `OAI.Combinatorics.MomentGraph.Sheaf.Isomorphism`
- `OAI.Data.Polynomial.Avoidance`: (Mathlib only)
- `OAI.Data.Polynomial.LowPart`: (Mathlib only)
- `OAI.Data.Polynomial.ReciprocalRigidity`: (Mathlib only)
- `OAI.Data.Polynomial.ReflectEvaluation`: (Mathlib only)
- `OAI.Data.Polynomial.ScaledComparison`: `OAI.Data.Polynomial.ReciprocalRigidity`
- `OAI.GroupTheory.Coxeter.Bruhat.Basic`: `OAI.GroupTheory.Coxeter.Bruhat.Defs`, `OAI.GroupTheory.Coxeter.Exchange`
- `OAI.GroupTheory.Coxeter.Bruhat.Defs`: (Mathlib only)
- `OAI.GroupTheory.Coxeter.Bruhat.Descent`: `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset`
- `OAI.GroupTheory.Coxeter.Bruhat.DiamondClosure`: `OAI.Order.Interval.Diamonds`, `OAI.GroupTheory.Coxeter.Roots.ReflectionLabels`
- `OAI.GroupTheory.Coxeter.Bruhat.Diamonds`: `OAI.GroupTheory.Coxeter.Parabolic.InversionList`, `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`
- `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset`: `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.GroupTheory.Coxeter.Bruhat.Transport`: `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.GroupTheory.Coxeter.Dihedral.Diamonds`: `OAI.GroupTheory.Coxeter.Dihedral.Words`, `OAI.Order.Interval.Diamonds`, `OAI.GroupTheory.Coxeter.Bruhat.DiamondClosure`
- `OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport`: `OAI.Combinatorics.MomentGraph.Bruhat.Basic`, `OAI.GroupTheory.Coxeter.Dihedral.Diamonds`
- `OAI.GroupTheory.Coxeter.Dihedral.PlaneSystem`: `OAI.GroupTheory.Coxeter.Dihedral.Diamonds`
- `OAI.GroupTheory.Coxeter.Dihedral.SignedWords`: `OAI.Combinatorics.Dihedral.SignedCount`, `OAI.GroupTheory.Coxeter.Bruhat.Descent`, `OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport`, `OAI.GroupTheory.Coxeter.Dihedral.PlaneSystem`
- `OAI.GroupTheory.Coxeter.Dihedral.Words`: `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.GroupTheory.Coxeter.Exchange`: (Mathlib only)
- `OAI.GroupTheory.Coxeter.Parabolic.InversionList`: `OAI.GroupTheory.Coxeter.Parabolic.Standard`
- `OAI.GroupTheory.Coxeter.Parabolic.Standard`: `OAI.GroupTheory.Coxeter.Realization.Cotangent`
- `OAI.GroupTheory.Coxeter.Parabolic.Support`: `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.GroupTheory.Coxeter.Realization.Cotangent`: `OAI.GroupTheory.Coxeter.Realization.Positivity`
- `OAI.GroupTheory.Coxeter.Realization.Faithful`: `OAI.GroupTheory.Coxeter.Realization.Positivity`
- `OAI.GroupTheory.Coxeter.Realization.Geometric`: `OAI.LinearAlgebra.Reflection.Forms`
- `OAI.GroupTheory.Coxeter.Realization.Positivity`: `OAI.GroupTheory.Coxeter.Parabolic.Support`, `OAI.GroupTheory.Coxeter.Realization.Tits`
- `OAI.GroupTheory.Coxeter.Realization.Tits`: `OAI.GroupTheory.Coxeter.Realization.Geometric`
- `OAI.GroupTheory.Coxeter.Roots.Basic`: `OAI.GroupTheory.Coxeter.Realization.Faithful`, `OAI.LinearAlgebra.Reflection.Plane`
- `OAI.GroupTheory.Coxeter.Roots.DihedralOrder`: `OAI.GroupTheory.Coxeter.Dihedral.SignedWords`, `OAI.GroupTheory.Coxeter.Roots.RatioOrder`
- `OAI.GroupTheory.Coxeter.Roots.LaterCount`: `OAI.GroupTheory.Coxeter.Roots.DihedralOrder`, `OAI.GroupTheory.Coxeter.Roots.PlaneTransport`
- `OAI.GroupTheory.Coxeter.Roots.Order`: `OAI.Data.Polynomial.Avoidance`, `OAI.GroupTheory.Coxeter.Roots.Basic`
- `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`: `OAI.GroupTheory.Coxeter.Dihedral.PlaneSystem`, `OAI.GroupTheory.Coxeter.Roots.PlaneLength`, `OAI.GroupTheory.Coxeter.Roots.PlaneSubgroup`
- `OAI.GroupTheory.Coxeter.Roots.PlaneLength`: `OAI.GroupTheory.Coxeter.Roots.Order`, `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal`
- `OAI.GroupTheory.Coxeter.Roots.PlaneSubgroup`: `OAI.GroupTheory.Coxeter.Roots.Basic`
- `OAI.GroupTheory.Coxeter.Roots.PlaneTransport`: `OAI.GroupTheory.Coxeter.Bruhat.Diamonds`, `OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport`
- `OAI.GroupTheory.Coxeter.Roots.RatioOrder`: `OAI.Combinatorics.DirectedPaths.Subpaths`, `OAI.GroupTheory.Coxeter.Dihedral.IntervalTransport`, `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`
- `OAI.GroupTheory.Coxeter.Roots.ReflectionLabels`: `OAI.GroupTheory.Coxeter.Roots.Order`
- `OAI.GroupTheory.Coxeter.Roots.ReflectionOrder`: `OAI.Data.Polynomial.Avoidance`, `OAI.GroupTheory.Coxeter.Roots.Basic`, `OAI.GroupTheory.Coxeter.Roots.Order`, `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`
- `OAI.GroupTheory.Coxeter.Roots.Splines`: `OAI.GroupTheory.Coxeter.Roots.Basic`
- `OAI.LinearAlgebra.ConjugateRange`: (Mathlib only)
- `OAI.LinearAlgebra.CoordinateProjection`: (Mathlib only)
- `OAI.LinearAlgebra.Descent`: (Mathlib only)
- `OAI.LinearAlgebra.Dual.Adjoint`: `OAI.LinearAlgebra.Dual.Summand`
- `OAI.LinearAlgebra.Dual.BalancedCut`: (Mathlib only)
- `OAI.LinearAlgebra.Dual.Frobenius`: `OAI.Algebra.Algebra.ReflectionFrobenius.Basis`
- `OAI.LinearAlgebra.Dual.IntegralSupport`: (Mathlib only)
- `OAI.LinearAlgebra.Dual.Summand`: (Mathlib only)
- `OAI.LinearAlgebra.Dual.TransportPairing`: (Mathlib only)
- `OAI.LinearAlgebra.KernelCoordinates`: `OAI.Algebra.Module.Projective.Transport`, `OAI.Algebra.Module.ReflectionPair.TensorKernel`, `OAI.LinearAlgebra.CoordinateProjection`
- `OAI.LinearAlgebra.PairProjection.Basic`: (Mathlib only)
- `OAI.LinearAlgebra.PairProjection.Kernel`: `OAI.LinearAlgebra.PairProjection.Basic`
- `OAI.LinearAlgebra.PairProjection.Lifting`: `OAI.LinearAlgebra.PairProjection.Basic`
- `OAI.LinearAlgebra.PlaneReduction`: (Mathlib only)
- `OAI.LinearAlgebra.Reflection.Classification`: (Mathlib only)
- `OAI.LinearAlgebra.Reflection.Forms`: (Mathlib only)
- `OAI.LinearAlgebra.Reflection.Plane`: (Mathlib only)
- `OAI.LinearAlgebra.SymmetricAlgebra.Quotient`: (Mathlib only)
- `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal`: (Mathlib only)
- `OAI.LinearAlgebra.TensorProduct.Coordinates`: (Mathlib only)
- `OAI.Order.Interval.Diamonds`: (Mathlib only)
- `OAI.RepresentationTheory.BottSamelson.AdjointSheaf`: `OAI.Algebra.Module.Graded.Adjoint`, `OAI.Algebra.Module.Localization.Lattice`, `OAI.Combinatorics.MomentGraph.Boundary.Summand`, `OAI.LinearAlgebra.ConjugateRange`, `OAI.LinearAlgebra.Dual.TransportPairing`, `OAI.RepresentationTheory.BottSamelson.Pairings`
- `OAI.RepresentationTheory.BottSamelson.CanonicalPairing`: `OAI.Combinatorics.MomentGraph.Boundary.Uniqueness`, `OAI.RepresentationTheory.BottSamelson.Character`
- `OAI.RepresentationTheory.BottSamelson.Character`: `OAI.Combinatorics.MomentGraph.Boundary.Models`, `OAI.RepresentationTheory.BottSamelson.Support`, `OAI.RepresentationTheory.Hecke.PositiveWord`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.FreeModel`
- `OAI.RepresentationTheory.BottSamelson.CharacterDecomposition`: `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Reciprocity`
- `OAI.RepresentationTheory.BottSamelson.Pairings`: `OAI.Algebra.Module.Graded.Hilbert.RationalFunction`, `OAI.Algebra.Module.Localization.FiniteCharacters`, `OAI.Algebra.Module.Localization.ProjectiveLattice`, `OAI.Algebra.Module.Projective.Range`, `OAI.Algebra.Module.ReflectionPair.TensorDescent`, `OAI.LinearAlgebra.KernelCoordinates`, `OAI.LinearAlgebra.PairProjection.Lifting`, `OAI.LinearAlgebra.Reflection.Classification`, `OAI.RepresentationTheory.BottSamelson.Stalks`, `OAI.RepresentationTheory.Hecke.Coefficients`
- `OAI.RepresentationTheory.BottSamelson.Stalks`: `OAI.Algebra.Module.Free.ScalarDivisibility`, `OAI.Algebra.Module.Graded.DualAndShift`, `OAI.Algebra.Module.Graded.NonnegativeBasis`, `OAI.Algebra.Module.ReflectionPair.TensorKernel`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Basic`, `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal`, `OAI.LinearAlgebra.TensorProduct.Coordinates`, `OAI.RepresentationTheory.BottSamelson.Words`, `OAI.RepresentationTheory.KazhdanLusztig.KernelTransportCompat`
- `OAI.RepresentationTheory.BottSamelson.Support`: `OAI.Algebra.Module.Graded.ModuleData.Duality`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`, `OAI.LinearAlgebra.Dual.BalancedCut`, `OAI.RepresentationTheory.BottSamelson.AdjointSheaf`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.LowerCharacter`
- `OAI.RepresentationTheory.BottSamelson.Words`: `OAI.Combinatorics.MomentGraph.Bruhat.Basic`, `OAI.GroupTheory.Coxeter.Bruhat.Descent`, `OAI.GroupTheory.Coxeter.Roots.Basic`, `OAI.LinearAlgebra.Dual.Frobenius`, `OAI.LinearAlgebra.PairProjection.Kernel`
- `OAI.RepresentationTheory.Hecke.Coefficients`: `OAI.RepresentationTheory.Hecke.Operators`
- `OAI.RepresentationTheory.Hecke.Dihedral`: `OAI.GroupTheory.Coxeter.Dihedral.Words`, `OAI.RepresentationTheory.Hecke.DualR`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `OAI.RepresentationTheory.Hecke.DualR`: `OAI.RepresentationTheory.Hecke.Operators`
- `OAI.RepresentationTheory.Hecke.DyerPaths.Adapted`: `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset`, `OAI.GroupTheory.Coxeter.Roots.RatioOrder`, `OAI.RepresentationTheory.Hecke.Operators`
- `OAI.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`: `OAI.Combinatorics.DirectedPaths.Basic`, `OAI.Combinatorics.DirectedPaths.SortedSchedule`, `OAI.GroupTheory.Coxeter.Bruhat.Defs`, `OAI.GroupTheory.Coxeter.Roots.Basic`, `OAI.GroupTheory.Coxeter.Roots.Order`, `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`, `OAI.GroupTheory.Coxeter.Roots.ReflectionOrder`, `OAI.RepresentationTheory.Hecke.DyerPaths.Adapted`, `OAI.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`
- `OAI.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`: `OAI.Combinatorics.DirectedPaths.Transfer`, `OAI.GroupTheory.Coxeter.Roots.PlaneTransport`, `OAI.RepresentationTheory.Hecke.DyerPaths.Adapted`
- `OAI.RepresentationTheory.Hecke.DyerPaths.Wall`: `OAI.GroupTheory.Coxeter.Roots.ReflectionOrder`, `OAI.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`
- `OAI.RepresentationTheory.Hecke.Inverse`: `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset`, `OAI.RepresentationTheory.Hecke.Operators`
- `OAI.RepresentationTheory.Hecke.Operators`: `OAI.GroupTheory.Coxeter.Bruhat.Basic`
- `OAI.RepresentationTheory.Hecke.OrdinaryR`: `OAI.Data.Polynomial.ReflectEvaluation`, `OAI.RepresentationTheory.Hecke.Inverse`
- `OAI.RepresentationTheory.Hecke.PositiveWord`: `OAI.GroupTheory.Coxeter.Bruhat.LowerFinset`, `OAI.RepresentationTheory.Hecke.Coefficients`, `OAI.RepresentationTheory.Hecke.DualR`
- `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Freeness`: `OAI.Combinatorics.DirectedPaths.Suffix`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Edge`
- `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Propagation`: `OAI.Algebra.Module.Graded.RegularScalar`, `OAI.Algebra.Module.Projective.ScalarKernel`, `OAI.Combinatorics.DirectedPaths.Monotone`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Hilbert`, `OAI.Data.Polynomial.ScaledComparison`, `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Transport`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Ambient`
- `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Transport`: `OAI.Combinatorics.DirectedPaths.ScalarMap`, `OAI.Combinatorics.MomentGraph.Boundary.Extension`, `OAI.RepresentationTheory.BottSamelson.CanonicalPairing`, `OAI.RepresentationTheory.Hecke.DyerPaths.Wall`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.StalkReciprocity`
- `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Finite`: `OAI.GroupTheory.Coxeter.Bruhat.Transport`, `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Freeness`, `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Induction`
- `OAI.RepresentationTheory.KazhdanLusztig.Invariance.FiniteModel`: `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`
- `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Induction`: `OAI.Data.Polynomial.ScaledComparison`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`
- `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Main`: `OAI.RepresentationTheory.KazhdanLusztig.Invariance.Finite`, `OAI.RepresentationTheory.KazhdanLusztig.Invariance.FiniteModel`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.Ambient`: `OAI.GroupTheory.Coxeter.Roots.LaterCount`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Support`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.Edge`: `OAI.Algebra.Module.Quotient.ScalarImage`, `OAI.RepresentationTheory.KazhdanLusztig.Comparison.Propagation`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Terminal`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.Embed`: `OAI.GroupTheory.Coxeter.Roots.Splines`, `OAI.LinearAlgebra.PlaneReduction`, `OAI.LinearAlgebra.SymmetricAlgebra.Quotient`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Ambient`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.Plane`: `OAI.Combinatorics.MomentGraph.Sheaf.Localization`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Embed`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.PlaneModel`, `OAI.RingTheory.Localization.RelativePrime`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.PlaneModel`: `OAI.Combinatorics.MomentGraph.Bruhat.DihedralModel`, `OAI.GroupTheory.Coxeter.Roots.PlaneBasis`
- `OAI.RepresentationTheory.KazhdanLusztig.Localization.Terminal`: `OAI.Combinatorics.MomentGraph.Sheaf.ScaledImages`, `OAI.RepresentationTheory.KazhdanLusztig.Localization.Plane`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`: `OAI.Data.Polynomial.LowPart`, `OAI.RepresentationTheory.Hecke.OrdinaryR`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`: `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`: `OAI.GroupTheory.Coxeter.Bruhat.Defs`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`: `OAI.GroupTheory.Coxeter.Parabolic.Standard`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`: `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`: `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`: `OAI.Data.Polynomial.ReciprocalRigidity`, `OAI.GroupTheory.Coxeter.Bruhat.Basic`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Boundary`: `OAI.Algebra.Module.Graded.NonnegativeBasis`, `OAI.Combinatorics.MomentGraph.Bruhat.Basic`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Extension`, `OAI.GroupTheory.Coxeter.Bruhat.Descent`, `OAI.GroupTheory.Coxeter.Roots.Basic`, `OAI.LinearAlgebra.SymmetricAlgebra.RootIdeal`, `OAI.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.FreeModel`: `OAI.Algebra.Module.Graded.ModuleData.CharacterDual`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Models`, `OAI.RepresentationTheory.Hecke.OrdinaryR`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.LowerCharacter`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Support`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.LowerCharacter`: `OAI.Combinatorics.MomentGraph.GradedSheaf.Character`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Boundary`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Reciprocity`: `OAI.RepresentationTheory.BottSamelson.Character`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.StalkReciprocity`: `OAI.Algebra.BigOperators.FiniteCharacterCancellation`, `OAI.RepresentationTheory.BottSamelson.CharacterDecomposition`
- `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Support`: `OAI.Algebra.Module.Graded.HomogeneousDual`, `OAI.Combinatorics.MomentGraph.GradedSheaf.Duality`, `OAI.GroupTheory.Coxeter.Roots.Order`, `OAI.RepresentationTheory.KazhdanLusztig.Sheaves.Boundary`
- `OAI.RingTheory.Localization.RelativePrime`: (Mathlib only)
