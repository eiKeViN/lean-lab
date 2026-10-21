# Source migration index

Reference: Git `7ddc53ba8a09ed902fefff86e67a87217518c1d4:experiments/kl-kernel-transport` (historical source, no checkout required).
Ranges below are inclusive, 1-based reference lines. Mathematical bodies are unchanged. Partition records cover their immutable parent exactly; only existing scope frames are copied.
Existing anonymous instance names are pinned explicitly; Hecke inverse proofs restore their original local instance attribute.
Original 34 KL entrypoints and kernel entrypoints are compatibility imports. Earlier semantic paths are recoverable from the pinned Git history, not maintained checkouts.

## Old file → semantic homes

### BalancedPairings.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/Range.lean` ← 839–862, 1513–1522, 626–680
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Summand.lean` ← 1965–2001
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Summand.lean` ← 1524–1552, 1629–1679, 466–515, 864–908, 918–964, 1305–1396, 1770–1907, 1917–1963
- `ForMathlib/LinearAlgebra/ConjugateRange.lean` ← 971–1005
- `ForMathlib/LinearAlgebra/Dual/Adjoint.lean` ← 1687–1699, 1126–1151, 1158–1180
- `ForMathlib/LinearAlgebra/Dual/Summand.lean` ← 1016–1117
- `ForMathlib/LinearAlgebra/Dual/TransportPairing.lean` ← 306–328
- `ForMathlib/LinearAlgebra/Quotient/Transport.lean` ← 594–619
- `OAI/KL/BottSamelson/AdjointSheaf.lean` ← 1187–1199, 167–299, 339–404, 11–84, 414–456, 94–157, 2043–2098, 524–587, 691–756, 766–830, 1209–1295, 1454–1506, 1562–1620, 1406–1443, 1701–1760, 2011–2033

### BottSamelson.lean

- `ForMathlib/Algebra/Module/CoefficientChange/Basic.lean` ← 1749–1822
- `ForMathlib/Algebra/Module/Free/ScalarDivisibility.lean` ← 892–949
- `ForMathlib/Algebra/Module/Graded/FinitePieces.lean` ← 1658–1690
- `ForMathlib/Algebra/Module/Graded/HomogeneousEquiv.lean` ← 559–613, 1620–1650
- `ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange/Basic.lean` ← 1830–1883
- `ForMathlib/Algebra/Module/Graded/ModuleData/PairProjection.lean` ← 1347–1402
- `ForMathlib/Algebra/Module/ReflectionPair/TensorKernel.lean` ← 526–550, 699–736, 1202–1269
- `ForMathlib/LinearAlgebra/TensorProduct/Coordinates.lean` ← 12–47, 793–806
- `OAI/KL/BottSamelson/Stalks.lean` ← 54–81, 231–321, 743–787, 331–404, 958–1047, 414–517, 91–221, 1413–1494, 622–689, 813–885, 1054–1102, 1276–1338, 1110–1195, 1504–1537, 1547–1611, 1893–1934, 1945–2021, 1700–1740

### Bruhat.lean

- `ForMathlib/Algebra/Polynomial/Reciprocal.lean` ← 138–148
- `ForMathlib/GroupTheory/Coxeter/Bruhat/Basic.lean` ← 10–43, 71–109, 210–527
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/SelectedR.lean` ← 45–57
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Unique.lean` ← 110–137, 149–208

### CanonicalKL.lean

- `ForMathlib/Algebra/Polynomial/LowPart.lean` ← 22–67
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Canonical.lean` ← 68–469

### CharacterReciprocity.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/CharacterDual.lean` ← 2049–2075, 1046–1066
- `ForMathlib/Algebra/Module/Graded/ModuleData/CoefficientChange.lean` ← 1578–1600, 1522–1571, 1662–1691
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Models.lean` ← 1156–1190, 1693–1724
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Models.lean` ← 568–629, 1602–1655, 780–796, 1835–1906, 64–89, 1285–1311, 636–773, 1971–2004
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Models.lean` ← 340–429, 436–559
- `ForMathlib/LinearAlgebra/Dual/BalancedCut.lean` ← 38–57
- `ForMathlib/RepresentationTheory/Hecke/PositiveWord.lean` ← 939–1015, 1022–1039
- `OAI/KL/BottSamelson/Character.lean` ← 1320–1372, 1381–1425, 1200–1278, 1434–1480, 1489–1515, 858–930, 1075–1147
- `OAI/KL/BottSamelson/CharacterDecomposition.lean` ← 2011–2042
- `OAI/KL/Sheaves/FreeModel.lean` ← 11–29, 97–123, 133–330, 798–849, 2082–2115, 2122–2188
- `OAI/KL/Sheaves/Reciprocity.lean` ← 1732–1764, 1772–1828, 1913–1964

### Comparison.lean

- `ForMathlib/Algebra/Polynomial/Reciprocal.lean` ← 21–65
- `ForMathlib/Combinatorics/DirectedPaths/PositiveTransfer.lean` ← 66–144

### Coxeter.lean

- `ForMathlib/GroupTheory/Coxeter/Exchange.lean` ← 12–237

### Decomposition.lean

- `ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basic.lean` ← 1428–1697
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Character.lean` ← 11–88
- `ForMathlib/GroupTheory/Coxeter/Bruhat/Diamonds.lean` ← 1342–1418
- `ForMathlib/GroupTheory/Coxeter/Dihedral/PlaneSystem.lean` ← 235–370, 1239–1273
- `ForMathlib/GroupTheory/Coxeter/Roots/PlaneBasis.lean` ← 374–1237, 1275–1340
- `ForMathlib/LinearAlgebra/PairProjection.lean` ← 144–226
- `OAI/KL/Sheaves/LowerCharacter.lean` ← 95–134

### Dihedral.lean

- `ForMathlib/GroupTheory/Coxeter/Bruhat/Transport.lean` ← 11–66
- `ForMathlib/GroupTheory/Coxeter/Dihedral/Words.lean` ← 68–134, 136–187
- `ForMathlib/RepresentationTheory/Hecke/DualR.lean` ← 381–480
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Dihedral.lean` ← 189–277, 279–379, 482–565, 567–662
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Normalization.lean` ← 668–798

### DihedralIntervals.lean

- `ForMathlib/Combinatorics/Dihedral/SignedCount.lean` ← 914–1064, 1452–1600, 1609–1757
- `ForMathlib/Combinatorics/MomentGraph/Bruhat/DihedralModel.lean` ← 218–323, 454–594
- `ForMathlib/Combinatorics/MomentGraph/Bruhat/PlaneModel.lean` ← 603–631
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/FlowDown.lean` ← 333–445
- `ForMathlib/GroupTheory/Coxeter/Dihedral/SignedWords.lean` ← 11–120, 640–689, 696–793, 1765–1783, 800–816, 1072–1081, 1276–1367, 1374–1444
- `ForMathlib/GroupTheory/Coxeter/Roots/DihedralOrder.lean` ← 818–905, 1083–1219, 1226–1269
- `ForMathlib/GroupTheory/Coxeter/Roots/LaterCount.lean` ← 1785–1884, 1891–1987, 1994–2074, 2081–2242
- `ForMathlib/GroupTheory/Coxeter/Roots/Splines.lean` ← 129–208

### DyerPaths.lean

- `ForMathlib/Algebra/BigOperators/SingleCoordinate.lean` ← 11–40
- `ForMathlib/Combinatorics/DirectedPaths/Subpaths.lean` ← 1655–1702, 1777–1819, 1821–1852
- `ForMathlib/GroupTheory/Coxeter/Bruhat/Diamonds.lean` ← 168–247, 625–666
- `ForMathlib/GroupTheory/Coxeter/Dihedral/IntervalTransport.lean` ← 336–372, 952–1066, 1556–1653, 483–623
- `ForMathlib/GroupTheory/Coxeter/Parabolic/InversionList.lean` ← 112–166
- `ForMathlib/GroupTheory/Coxeter/Roots/PlaneTransport.lean` ← 255–334, 374–481, 668–723, 725–829
- `ForMathlib/GroupTheory/Coxeter/Roots/RatioOrder.lean` ← 1130–1546, 837–950, 1068–1120, 1704–1775, 1854–1929
- `ForMathlib/RepresentationTheory/Hecke/DyerPaths/Adapted.lean` ← 1939–2495
- `OAI/KL/Sheaves/StalkReciprocity.lean` ← 50–103

### EdgeLocalization.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/CoverUniqueness.lean` ← 472–504
- `ForMathlib/Algebra/Module/Graded/RegularScalar.lean` ← 1035–1088
- `ForMathlib/Combinatorics/DirectedPaths/ScalarMap.lean` ← 136–153
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Uniqueness.lean` ← 640–685, 734–770
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Uniqueness.lean` ← 585–631, 692–727, 933–959, 777–799
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Uniqueness.lean` ← 511–578
- `ForMathlib/LinearAlgebra/Dual/IntegralSupport.lean` ← 1096–1117
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/ScaledReciprocity.lean` ← 155–195
- `OAI/KL/BottSamelson/CanonicalPairing.lean` ← 809–854, 863–926, 969–996
- `OAI/KL/Comparison/Transport.lean` ← 253–284, 293–345, 11–127, 197–245, 998–1024, 353–462

### Frobenius.lean

- `ForMathlib/Algebra/Algebra/ReflectionFrobenius/Basis.lean` ← 1130–1193, 513–545, 447–504, 657–759
- `ForMathlib/Algebra/Module/Graded/Basis.lean` ← 843–928
- `ForMathlib/Algebra/Module/Graded/HomogeneousMul.lean` ← 429–445
- `ForMathlib/Algebra/Module/Graded/PolynomialMap.lean` ← 632–655
- `ForMathlib/Algebra/Module/ReflectionPair/Twist.lean` ← 2038–2215
- `ForMathlib/LinearAlgebra/Dual/Frobenius.lean` ← 103–187, 189–212, 221–282, 290–376, 554–625
- `ForMathlib/LinearAlgebra/PairProjection.lean` ← 1840–1865
- `ForMathlib/RepresentationTheory/BottSamelson/TitsWords.lean` ← 11–93, 387–420, 1349–1385, 769–834, 938–1033, 1625–1663, 1043–1121, 1204–1300, 1672–1733, 1309–1340, 1395–1479, 1490–1616, 1744–1831, 1875–2028

### GradedModules.lean

- `ForMathlib/Algebra/Module/Graded/Generators.lean` ← 675–877, 11–483, 582–668, 884–1038
- `ForMathlib/Algebra/Module/Graded/ModuleData/Basic.lean` ← 1045–1212, 1220–1313, 1322–1448
- `ForMathlib/Algebra/Module/Projective/ScalarQuotient.lean` ← 486–575

### GradedSheaves.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/Equality.lean` ← 246–259, 371–387
- `ForMathlib/Algebra/Module/Submodule/PiIdeal.lean` ← 868–886
- `ForMathlib/Algebra/Module/Submodule/ScaledImage.lean` ← 650–675
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Basic.lean` ← 1129–1242
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/AttachBottom.lean` ← 99–239
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Defs.lean` ← 13–92
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Properties.lean` ← 389–508
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Reindex.lean` ← 261–364
- `ForMathlib/Combinatorics/MomentGraph/OrderedGraph/VertexDeletion.lean` ← 1050–1122
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Iso.lean` ← 516–648, 683–806, 957–1043
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Pi.lean` ← 813–866, 888–900
- `ForMathlib/LinearAlgebra/Quotient/Transport.lean` ← 907–947

### Hecke.lean

- `ForMathlib/Algebra/Polynomial/Reciprocal.lean` ← 1100–1114
- `ForMathlib/GroupTheory/Coxeter/Bruhat/LowerFinset.lean` ← 1039–1049
- `ForMathlib/RepresentationTheory/Hecke/Inverse.lean` ← 1050–1098
- `ForMathlib/RepresentationTheory/Hecke/Operators.lean` ← 19–505, 508–1037

### HilbertSeries.lean

- `ForMathlib/Algebra/Module/Graded/Hilbert/Series.lean` ← 11–114, 122–330, 338–420, 427–543

### IntegralPairings.lean

- `ForMathlib/Algebra/Module/Graded/Adjoint.lean` ← 2275–2324, 2331–2356
- `ForMathlib/Algebra/Module/Graded/Hilbert/Numerator.lean` ← 11–68
- `ForMathlib/Algebra/Module/Localization/FiniteCharacters.lean` ← 1658–1858
- `ForMathlib/Algebra/Module/Localization/ProjectiveLattice.lean` ← 1866–1934
- `ForMathlib/Algebra/Module/Projective/Range.lean` ← 482–547, 1326–1359
- `ForMathlib/Algebra/Module/Projective/Transport.lean` ← 985–1007
- `ForMathlib/Algebra/Module/ReflectionPair/TensorDescent.lean` ← 554–582, 754–779
- `ForMathlib/LinearAlgebra/CoordinateProjection.lean` ← 314–369
- `ForMathlib/LinearAlgebra/Dual/Adjoint.lean` ← 2212–2267
- `ForMathlib/LinearAlgebra/KernelCoordinates.lean` ← 589–613, 1014–1072
- `ForMathlib/LinearAlgebra/PairProjection.lean` ← 786–803
- `ForMathlib/LinearAlgebra/Reflection/Classification.lean` ← 1435–1474
- `ForMathlib/RepresentationTheory/Hecke/Coefficients.lean` ← 147–219
- `OAI/KL/BottSamelson/Flabby.lean` ← 2127–2203
- `OAI/KL/BottSamelson/StalkCharacter.lean` ← 78–137, 228–305
- `OAI/KL/BottSamelson/UpperSections.lean` ← 1484–1556, 1565–1649, 377–474, 1943–2068, 621–747, 812–882, 889–978, 1251–1319, 1079–1138, 1145–1242, 1366–1426, 2077–2118

### Invariance.lean

- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/FiniteRankReduction.lean` ← 470–531
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/IntervalTransport.lean` ← 11–55, 217–255
- `OAI/KL/Invariance/Finite.lean` ← 257–317, 325–384, 64–114, 125–209, 395–460
- `OAI/KL/Invariance/Main.lean` ← 541–565

### MinimalExtensions.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/Transport.lean` ← 428–456, 177–201
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Extension.lean` ← 792–874
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Extension.lean` ← 12–76, 85–101, 103–170, 203–259, 515–639, 1634–1727, 458–506, 648–735, 744–783
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/BaseChange.lean` ← 982–1047, 1094–1186, 1054–1087
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Products.lean` ← 266–369, 376–421
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Pullback.lean` ← 1452–1575, 1582–1625
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Restriction.lean` ← 1319–1411, 1413–1442
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Structure.lean` ← 882–975, 1194–1310

### Model.lean

- `ForMathlib/GroupTheory/Coxeter/Bruhat/Defs.lean` ← 14–47
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Normalized.lean` ← 48–79

### ModuleAlgebra.lean

- `ForMathlib/Algebra/Module/Cover/Local.lean` ← 157–235
- `ForMathlib/Algebra/Module/Graded/Components.lean` ← 275–370, 434–487
- `ForMathlib/Algebra/Module/Graded/Hilbert/Basic.lean` ← 494–615
- `ForMathlib/Algebra/Module/Localization/Lattice.lean` ← 12–147
- `ForMathlib/Algebra/Module/Projective/ReverseFiltration.lean` ← 238–272
- `ForMathlib/Algebra/Module/Quotient/KernelReduction.lean` ← 373–428

### OrdinaryR.lean

- `ForMathlib/RepresentationTheory/Hecke/OrdinaryR.lean` ← 10–297

### PlaneLocalization.lean

- `ForMathlib/Algebra/Module/Submodule/ProductScaling.lean` ← 1482–1536
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Localization.lean` ← 529–546, 783–849, 614–662, 283–304, 139–190, 851–887, 197–259
- `ForMathlib/LinearAlgebra/PlaneReduction.lean` ← 1263–1288
- `ForMathlib/LinearAlgebra/SymmetricAlgebra/Quotient.lean` ← 11–132
- `ForMathlib/RingTheory/Localization/RelativePrime.lean` ← 897–925
- `OAI/KL/Localization/Ambient.lean` ← 268–281, 1348–1475, 1685–1705, 1204–1222
- `OAI/KL/Localization/GraphEmbedding.lean` ← 338–397, 1297–1341, 1543–1618
- `OAI/KL/Localization/Plane.lean` ← 430–519, 306–329, 548–605, 399–421, 934–982, 671–774, 1087–1127, 1625–1678, 989–1080, 1134–1197, 1224–1253, 1707–1749

### PositiveTransfer.lean

- `ForMathlib/Algebra/Module/Graded/Hilbert/Increment.lean` ← 254–344
- `ForMathlib/Algebra/Module/Projective/ScalarKernel.lean` ← 922–1008
- `ForMathlib/Algebra/Order/Field/RealScaling.lean` ← 531–573
- `ForMathlib/Combinatorics/DirectedPaths/Monotone.lean` ← 216–247, 816–915
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hilbert.lean` ← 351–460
- `OAI/KL/Comparison/Propagation.lean` ← 467–524, 1015–1071, 11–73, 580–656, 666–756, 764–808, 1078–1199, 1210–1324, 85–207

### ReflectionOrders.lean

- `ForMathlib/Combinatorics/DirectedPaths/SortedSchedule.lean` ← 575–693
- `ForMathlib/Combinatorics/DirectedPaths/Transfer.lean` ← 11–248
- `ForMathlib/GroupTheory/Coxeter/Roots/ReflectionOrder.lean` ← 257–358, 848–966
- `ForMathlib/LinearAlgebra/Avoidance.lean` ← 815–846
- `ForMathlib/RepresentationTheory/Hecke/DyerPaths/LexicographicOrder.lean` ← 702–806
- `ForMathlib/RepresentationTheory/Hecke/DyerPaths/PlaneCoordinates.lean` ← 367–567
- `ForMathlib/RepresentationTheory/Hecke/DyerPaths/Wall.lean` ← 974–1143, 1152–1237

### ReflectionPlane.lean

- `ForMathlib/LinearAlgebra/Reflection/Plane.lean` ← 12–95

### ReflectionSchedules.lean

- `ForMathlib/Combinatorics/DirectedPaths/Basic.lean` ← 1154–1300
- `ForMathlib/GroupTheory/Coxeter/Bruhat/DiamondClosure.lean` ← 1553–1578
- `ForMathlib/GroupTheory/Coxeter/Dihedral/Diamonds.lean` ← 1582–1692, 1694–1771
- `ForMathlib/GroupTheory/Coxeter/Roots/Order.lean` ← 79–157, 159–288, 290–366, 368–493, 632–693, 495–630
- `ForMathlib/GroupTheory/Coxeter/Roots/PlaneLength.lean` ← 695–751, 887–1001, 1106–1151
- `ForMathlib/GroupTheory/Coxeter/Roots/ReflectionLabels.lean` ← 1360–1393, 1396–1521
- `ForMathlib/LinearAlgebra/Avoidance.lean` ← 12–77
- `ForMathlib/LinearAlgebra/Reflection/Plane.lean` ← 1302–1358
- `ForMathlib/LinearAlgebra/SymmetricAlgebra/RootIdeal.lean` ← 753–885, 1003–1039, 1041–1104
- `ForMathlib/Order/Interval/Diamonds.lean` ← 1523–1552

### SheafMorphisms.lean

- `ForMathlib/Algebra/Module/Graded/ModuleData/Character.lean` ← 1702–1726, 1735–1842
- `ForMathlib/Algebra/Module/Graded/ModuleData/MinimalCover.lean` ← 956–980, 1161–1203, 1306–1327, 1417–1476, 447–496, 1034–1076
- `ForMathlib/Algebra/Module/Graded/ModuleData/QuotientHom.lean` ← 533–556
- `ForMathlib/Algebra/Module/Graded/NonnegativeBasis.lean` ← 110–128, 413–445, 11–103
- `ForMathlib/Combinatorics/MomentGraph/Boundary/Hom.lean` ← 1078–1152, 1238–1299, 1363–1407
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Hom.lean` ← 989–1032, 1212–1236, 563–701, 708–799, 1329–1361, 809–892, 1553–1621, 899–946, 1628–1693
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Hom.lean` ← 1483–1546
- `ForMathlib/GroupTheory/Coxeter/Bruhat/Descent.lean` ← 237–326
- `ForMathlib/LinearAlgebra/Quotient/Transport.lean` ← 503–531
- `OAI/KL/Sheaves/Boundary.lean` ← 130–185, 193–228, 336–406

### Sheaves.lean

- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Basic.lean` ← 17–147, 153–244

### SimultaneousInvariance.lean

- `ForMathlib/Algebra/BigOperators/SingleCoordinate.lean` ← 350–375
- `ForMathlib/Algebra/Polynomial/ScaledEvaluation.lean` ← 321–349
- `ForMathlib/Algebra/Polynomial/TransferEvaluation.lean` ← 460–474
- `OAI/KL/Comparison/SuffixFreeness.lean` ← 155–233, 11–97, 106–148, 242–313, 386–458

### Support.lean

- `ForMathlib/Algebra/Module/CoefficientChange/Dual.lean` ← 1762–1833
- `ForMathlib/Algebra/Module/Graded/Hilbert/Images.lean` ← 1115–1202, 1209–1288
- `ForMathlib/Algebra/Module/Graded/HomogeneousDual.lean` ← 1514–1534, 696–730
- `ForMathlib/Algebra/Module/Graded/ModuleData/Duality.lean` ← 220–233, 11–60, 739–806
- `ForMathlib/Combinatorics/MomentGraph/GradedSheaf/Duality.lean` ← 1474–1507, 864–877, 1295–1334, 319–400, 1842–1910, 136–213
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/Duality.lean` ← 813–862, 884–1046
- `ForMathlib/LinearAlgebra/Dual/BalancedCut.lean` ← 583–603
- `ForMathlib/LinearAlgebra/Dual/IntegralSupport.lean` ← 470–575
- `OAI/KL/BottSamelson/Support.lean` ← 110–127, 664–689, 611–657, 70–102, 242–312, 409–462
- `OAI/KL/Sheaves/Support.lean` ← 1627–1675, 1053–1108, 1341–1392, 1400–1466, 1542–1618, 1683–1755

### TerminalKernels.lean

- `ForMathlib/Algebra/Module/Flat/Kernel.lean` ← 272–302
- `ForMathlib/Algebra/Module/Localization/Membership.lean` ← 901–930
- `ForMathlib/Algebra/Module/Quotient/ScalarImage.lean` ← 564–646, 861–894
- `ForMathlib/Combinatorics/DirectedPaths/Suffix.lean` ← 1368–1400
- `ForMathlib/Combinatorics/MomentGraph/Sheaf/ScaledImages.lean` ← 773–807, 309–375, 11–45, 937–977, 52–102
- `OAI/KL/Localization/Edge.lean` ← 508–555, 653–717, 724–766, 814–854, 984–1025, 450–501, 1033–1103, 1111–1188, 1196–1251, 1260–1361
- `OAI/KL/Localization/TerminalImages.lean` ← 190–223, 109–182, 231–264, 382–441

### Tits.lean

- `ForMathlib/Combinatorics/MomentGraph/Bruhat/Basic.lean` ← 15–101
- `ForMathlib/GroupTheory/Coxeter/Parabolic/Standard.lean` ← 1395–1510, 1519–1587
- `ForMathlib/GroupTheory/Coxeter/Parabolic/Support.lean` ← 753–804, 629–751
- `ForMathlib/GroupTheory/Coxeter/Realization/Cotangent.lean` ← 1308–1393
- `ForMathlib/GroupTheory/Coxeter/Realization/Faithful.lean` ← 1109–1233, 1235–1304
- `ForMathlib/GroupTheory/Coxeter/Realization/Geometric.lean` ← 296–356
- `ForMathlib/GroupTheory/Coxeter/Realization/Positivity.lean` ← 806–902, 904–1008
- `ForMathlib/GroupTheory/Coxeter/Realization/Tits.lean` ← 358–432, 547–627
- `ForMathlib/GroupTheory/Coxeter/Roots/Basic.lean` ← 1649–1830, 1832–1974, 1976–2082
- `ForMathlib/GroupTheory/Coxeter/Roots/PlaneSubgroup.lean` ← 2084–2155, 2157–2266
- `ForMathlib/LinearAlgebra/BilinearForm/NondegenerateExtension.lean` ← 434–545
- `ForMathlib/LinearAlgebra/Reflection/Bilinear.lean` ← 1010–1107, 105–188, 192–294
- `ForMathlib/RepresentationTheory/KazhdanLusztig/Polynomials/Parabolic.lean` ← 1588–1645

## Implementation modules → direct local imports

Every implementation also imports the pinned Mathlib.

- `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic`: (Mathlib only)
- `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis`: `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basic`, `ForMathlib.Algebra.Module.Graded.Basis`, `ForMathlib.Algebra.Module.Graded.PolynomialMap`, `ForMathlib.Algebra.Module.Graded.HomogeneousMul`
- `ForMathlib.Algebra.BigOperators.SingleCoordinate`: (Mathlib only)
- `ForMathlib.Algebra.Module.CoefficientChange.Basic`: (Mathlib only)
- `ForMathlib.Algebra.Module.CoefficientChange.Dual`: `ForMathlib.Algebra.Module.CoefficientChange.Basic`
- `ForMathlib.Algebra.Module.Cover.Local`: (Mathlib only)
- `ForMathlib.Algebra.Module.Flat.Kernel`: (Mathlib only)
- `ForMathlib.Algebra.Module.Free.ScalarDivisibility`: (Mathlib only)
- `ForMathlib.Algebra.Module.Graded.Adjoint`: `ForMathlib.Algebra.Module.Graded.Generators`, `ForMathlib.LinearAlgebra.Dual.Adjoint`
- `ForMathlib.Algebra.Module.Graded.Basis`: `ForMathlib.Algebra.Module.Graded.Generators`
- `ForMathlib.Algebra.Module.Graded.Components`: (Mathlib only)
- `ForMathlib.Algebra.Module.Graded.FinitePieces`: `ForMathlib.Algebra.Module.Graded.Generators`
- `ForMathlib.Algebra.Module.Graded.Generators`: `ForMathlib.Algebra.Module.Graded.Components`
- `ForMathlib.Algebra.Module.Graded.Hilbert.Basic`: (Mathlib only)
- `ForMathlib.Algebra.Module.Graded.Hilbert.Images`: `ForMathlib.Algebra.Module.Graded.Hilbert.Series`
- `ForMathlib.Algebra.Module.Graded.Hilbert.Increment`: `ForMathlib.Algebra.Module.Graded.Hilbert.Series`
- `ForMathlib.Algebra.Module.Graded.Hilbert.Numerator`: (Mathlib only)
- `ForMathlib.Algebra.Module.Graded.Hilbert.Series`: `ForMathlib.Algebra.Module.Graded.Generators`, `ForMathlib.Algebra.Module.Graded.Hilbert.Basic`
- `ForMathlib.Algebra.Module.Graded.HomogeneousDual`: `ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`
- `ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`: `ForMathlib.Algebra.Module.Graded.Basis`
- `ForMathlib.Algebra.Module.Graded.HomogeneousMul`: `ForMathlib.Algebra.Module.Graded.Generators`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`: `ForMathlib.Algebra.Module.Graded.Generators`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Character`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`
- `ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual`: `ForMathlib.Algebra.Module.Graded.ModuleData.Duality`
- `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange`: `ForMathlib.Algebra.Module.Graded.ModuleData.Duality`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`
- `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`: `ForMathlib.Algebra.Module.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`
- `ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Duality`: `ForMathlib.Algebra.Module.Graded.HomogeneousDual`, `ForMathlib.Algebra.Module.Graded.ModuleData.Character`, `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`, `ForMathlib.Algebra.Module.Graded.ModuleData.Transport`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`
- `ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover`: `ForMathlib.Algebra.Module.Cover.Local`, `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`, `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`
- `ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.LinearAlgebra.PairProjection`
- `ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.LinearAlgebra.Quotient.Transport`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Range`: `ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`, `ForMathlib.LinearAlgebra.Quotient.Transport`
- `ForMathlib.Algebra.Module.Graded.ModuleData.Transport`: `ForMathlib.Algebra.Module.Graded.ModuleData.Basic`, `ForMathlib.LinearAlgebra.Quotient.Transport`
- `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`: `ForMathlib.Algebra.Module.Graded.Hilbert.Series`
- `ForMathlib.Algebra.Module.Graded.PolynomialMap`: `ForMathlib.Algebra.Module.Graded.Generators`
- `ForMathlib.Algebra.Module.Graded.RegularScalar`: `ForMathlib.Algebra.Module.Graded.HomogeneousDual`
- `ForMathlib.Algebra.Module.Localization.FiniteCharacters`: (Mathlib only)
- `ForMathlib.Algebra.Module.Localization.Lattice`: (Mathlib only)
- `ForMathlib.Algebra.Module.Localization.Membership`: (Mathlib only)
- `ForMathlib.Algebra.Module.Localization.ProjectiveLattice`: (Mathlib only)
- `ForMathlib.Algebra.Module.Projective.Range`: (Mathlib only)
- `ForMathlib.Algebra.Module.Projective.ReverseFiltration`: (Mathlib only)
- `ForMathlib.Algebra.Module.Projective.ScalarKernel`: `ForMathlib.Algebra.Module.Graded.Hilbert.Images`, `ForMathlib.Algebra.Module.Projective.ReverseFiltration`
- `ForMathlib.Algebra.Module.Projective.ScalarQuotient`: `ForMathlib.Algebra.Module.Projective.ReverseFiltration`
- `ForMathlib.Algebra.Module.Projective.Transport`: `ForMathlib.Algebra.Module.ReflectionPair.Twist`
- `ForMathlib.Algebra.Module.Quotient.KernelReduction`: (Mathlib only)
- `ForMathlib.Algebra.Module.Quotient.ScalarImage`: `ForMathlib.Algebra.Module.Free.ScalarDivisibility`, `ForMathlib.LinearAlgebra.Quotient.Transport`
- `ForMathlib.Algebra.Module.ReflectionPair.TensorDescent`: `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`
- `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`: `ForMathlib.Algebra.Module.ReflectionPair.Twist`
- `ForMathlib.Algebra.Module.ReflectionPair.Twist`: `ForMathlib.LinearAlgebra.PairProjection`
- `ForMathlib.Algebra.Module.Submodule.PiIdeal`: (Mathlib only)
- `ForMathlib.Algebra.Module.Submodule.ProductScaling`: (Mathlib only)
- `ForMathlib.Algebra.Module.Submodule.ScaledImage`: (Mathlib only)
- `ForMathlib.Algebra.Order.Field.RealScaling`: (Mathlib only)
- `ForMathlib.Algebra.Polynomial.LowPart`: (Mathlib only)
- `ForMathlib.Algebra.Polynomial.Reciprocal`: (Mathlib only)
- `ForMathlib.Algebra.Polynomial.ScaledEvaluation`: `ForMathlib.Algebra.Polynomial.Reciprocal`
- `ForMathlib.Algebra.Polynomial.TransferEvaluation`: (Mathlib only)
- `ForMathlib.Combinatorics.Dihedral.SignedCount`: (Mathlib only)
- `ForMathlib.Combinatorics.DirectedPaths.Basic`: (Mathlib only)
- `ForMathlib.Combinatorics.DirectedPaths.Monotone`: `ForMathlib.Combinatorics.DirectedPaths.Basic`
- `ForMathlib.Combinatorics.DirectedPaths.PositiveTransfer`: (Mathlib only)
- `ForMathlib.Combinatorics.DirectedPaths.ScalarMap`: `ForMathlib.Combinatorics.DirectedPaths.Basic`
- `ForMathlib.Combinatorics.DirectedPaths.SortedSchedule`: `ForMathlib.Combinatorics.DirectedPaths.Transfer`
- `ForMathlib.Combinatorics.DirectedPaths.Subpaths`: `ForMathlib.Combinatorics.DirectedPaths.Basic`
- `ForMathlib.Combinatorics.DirectedPaths.Suffix`: (Mathlib only)
- `ForMathlib.Combinatorics.DirectedPaths.Transfer`: `ForMathlib.Combinatorics.DirectedPaths.Subpaths`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Basic`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`, `ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Extension`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Hom`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Models`: `ForMathlib.Combinatorics.MomentGraph.Boundary.Summand`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Summand`: `ForMathlib.Combinatorics.MomentGraph.Boundary.Hom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand`
- `ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness`
- `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel`: `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`, `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`, `ForMathlib.GroupTheory.Coxeter.Roots.Splines`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`
- `ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel`: `ForMathlib.Combinatorics.MomentGraph.Bruhat.DihedralModel`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character`: `ForMathlib.Algebra.Module.Graded.ModuleData.Character`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`: `ForMathlib.Algebra.Module.Graded.ModuleData.Equality`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`: `ForMathlib.Algebra.Module.CoefficientChange.Dual`, `ForMathlib.Algebra.Module.Graded.Adjoint`, `ForMathlib.Algebra.Module.Graded.Hilbert.Images`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`: `ForMathlib.Algebra.Module.Graded.Hilbert.Series`, `ForMathlib.Algebra.Module.Graded.ModuleData.Transport`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Basic`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert`: `ForMathlib.Algebra.Module.Graded.Hilbert.Increment`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`: `ForMathlib.Algebra.Module.Graded.ModuleData.QuotientHom`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models`: `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Models`, `ForMathlib.LinearAlgebra.Dual.BalancedCut`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Summand`: `ForMathlib.Algebra.Module.Graded.ModuleData.Range`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hom`
- `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Uniqueness`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`
- `ForMathlib.Combinatorics.MomentGraph.OrderedGraph.VertexDeletion`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`: (Mathlib only)
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Duality`: `ForMathlib.Algebra.Module.Free.ScalarDivisibility`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`, `ForMathlib.LinearAlgebra.Dual.IntegralSupport`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.FlowDown`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Hom`: `ForMathlib.Algebra.Module.Graded.ModuleData.MinimalCover`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`: `ForMathlib.Algebra.Module.Cover.Local`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Basic`, `ForMathlib.LinearAlgebra.Quotient.Transport`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Models`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Models`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`, `ForMathlib.Algebra.Module.Submodule.PiIdeal`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Products`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pi`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Iso`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Restriction`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Pullback`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages`: `ForMathlib.Algebra.Module.Flat.Kernel`, `ForMathlib.Algebra.Module.Localization.Membership`, `ForMathlib.Algebra.Module.Submodule.ProductScaling`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Structure`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.BaseChange`
- `ForMathlib.Combinatorics.MomentGraph.Sheaf.Uniqueness`: `ForMathlib.Algebra.Module.Graded.ModuleData.CoverUniqueness`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`, `ForMathlib.GroupTheory.Coxeter.Exchange`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`: (Mathlib only)
- `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`: `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure`: `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels`, `ForMathlib.Order.Interval.Diamonds`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds`: `ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.GroupTheory.Coxeter.Bruhat.Transport`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`: `ForMathlib.GroupTheory.Coxeter.Bruhat.DiamondClosure`, `ForMathlib.GroupTheory.Coxeter.Dihedral.Words`, `ForMathlib.Order.Interval.Diamonds`
- `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`: `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`, `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`
- `ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem`: `ForMathlib.GroupTheory.Coxeter.Dihedral.Diamonds`
- `ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords`: `ForMathlib.Combinatorics.Dihedral.SignedCount`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`, `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`, `ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem`
- `ForMathlib.GroupTheory.Coxeter.Dihedral.Words`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.GroupTheory.Coxeter.Exchange`: (Mathlib only)
- `ForMathlib.GroupTheory.Coxeter.Parabolic.InversionList`: `ForMathlib.GroupTheory.Coxeter.Parabolic.Standard`
- `ForMathlib.GroupTheory.Coxeter.Parabolic.Standard`: `ForMathlib.GroupTheory.Coxeter.Realization.Cotangent`
- `ForMathlib.GroupTheory.Coxeter.Parabolic.Support`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.GroupTheory.Coxeter.Realization.Cotangent`: `ForMathlib.GroupTheory.Coxeter.Realization.Positivity`
- `ForMathlib.GroupTheory.Coxeter.Realization.Faithful`: `ForMathlib.GroupTheory.Coxeter.Realization.Positivity`
- `ForMathlib.GroupTheory.Coxeter.Realization.Geometric`: `ForMathlib.LinearAlgebra.Reflection.Bilinear`
- `ForMathlib.GroupTheory.Coxeter.Realization.Positivity`: `ForMathlib.GroupTheory.Coxeter.Parabolic.Support`, `ForMathlib.GroupTheory.Coxeter.Realization.Tits`
- `ForMathlib.GroupTheory.Coxeter.Realization.Tits`: `ForMathlib.GroupTheory.Coxeter.Realization.Geometric`, `ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension`
- `ForMathlib.GroupTheory.Coxeter.Roots.Basic`: `ForMathlib.GroupTheory.Coxeter.Realization.Faithful`, `ForMathlib.LinearAlgebra.Reflection.Plane`
- `ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder`: `ForMathlib.GroupTheory.Coxeter.Dihedral.SignedWords`, `ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder`
- `ForMathlib.GroupTheory.Coxeter.Roots.LaterCount`: `ForMathlib.GroupTheory.Coxeter.Roots.DihedralOrder`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport`
- `ForMathlib.GroupTheory.Coxeter.Roots.Order`: `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.LinearAlgebra.Avoidance`
- `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`: `ForMathlib.GroupTheory.Coxeter.Dihedral.PlaneSystem`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup`
- `ForMathlib.GroupTheory.Coxeter.Roots.PlaneLength`: `ForMathlib.GroupTheory.Coxeter.Roots.Order`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`
- `ForMathlib.GroupTheory.Coxeter.Roots.PlaneSubgroup`: `ForMathlib.GroupTheory.Coxeter.Roots.Basic`
- `ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Diamonds`, `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`
- `ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder`: `ForMathlib.Combinatorics.DirectedPaths.Subpaths`, `ForMathlib.GroupTheory.Coxeter.Dihedral.IntervalTransport`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`
- `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionLabels`: `ForMathlib.GroupTheory.Coxeter.Roots.Order`
- `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder`: `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.GroupTheory.Coxeter.Roots.Order`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`, `ForMathlib.LinearAlgebra.Avoidance`
- `ForMathlib.GroupTheory.Coxeter.Roots.Splines`: `ForMathlib.GroupTheory.Coxeter.Roots.Basic`
- `ForMathlib.LinearAlgebra.Avoidance`: (Mathlib only)
- `ForMathlib.LinearAlgebra.BilinearForm.NondegenerateExtension`: (Mathlib only)
- `ForMathlib.LinearAlgebra.ConjugateRange`: (Mathlib only)
- `ForMathlib.LinearAlgebra.CoordinateProjection`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Dual.Adjoint`: `ForMathlib.LinearAlgebra.Dual.Summand`
- `ForMathlib.LinearAlgebra.Dual.BalancedCut`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Dual.Frobenius`: `ForMathlib.Algebra.Algebra.ReflectionFrobenius.Basis`
- `ForMathlib.LinearAlgebra.Dual.IntegralSupport`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Dual.Summand`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Dual.TransportPairing`: (Mathlib only)
- `ForMathlib.LinearAlgebra.KernelCoordinates`: `ForMathlib.Algebra.Module.Projective.Transport`, `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`, `ForMathlib.LinearAlgebra.CoordinateProjection`
- `ForMathlib.LinearAlgebra.PairProjection`: (Mathlib only)
- `ForMathlib.LinearAlgebra.PlaneReduction`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Quotient.Transport`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Reflection.Bilinear`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Reflection.Classification`: (Mathlib only)
- `ForMathlib.LinearAlgebra.Reflection.Plane`: (Mathlib only)
- `ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient`: (Mathlib only)
- `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`: (Mathlib only)
- `ForMathlib.LinearAlgebra.TensorProduct.Coordinates`: (Mathlib only)
- `ForMathlib.Order.Interval.Diamonds`: (Mathlib only)
- `ForMathlib.RepresentationTheory.BottSamelson.TitsWords`: `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`, `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.LinearAlgebra.Dual.Frobenius`, `ForMathlib.LinearAlgebra.PairProjection`
- `ForMathlib.RepresentationTheory.Hecke.Coefficients`: `ForMathlib.RepresentationTheory.Hecke.Operators`
- `ForMathlib.RepresentationTheory.Hecke.DualR`: `ForMathlib.RepresentationTheory.Hecke.Operators`
- `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted`: `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`, `ForMathlib.GroupTheory.Coxeter.Roots.RatioOrder`, `ForMathlib.RepresentationTheory.Hecke.Operators`
- `ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`: `ForMathlib.Combinatorics.DirectedPaths.Basic`, `ForMathlib.Combinatorics.DirectedPaths.SortedSchedule`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`, `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.GroupTheory.Coxeter.Roots.Order`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneBasis`, `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`
- `ForMathlib.RepresentationTheory.Hecke.DyerPaths.PlaneCoordinates`: `ForMathlib.Combinatorics.DirectedPaths.Transfer`, `ForMathlib.GroupTheory.Coxeter.Roots.PlaneTransport`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Adapted`
- `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall`: `ForMathlib.GroupTheory.Coxeter.Roots.ReflectionOrder`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.LexicographicOrder`
- `ForMathlib.RepresentationTheory.Hecke.Inverse`: `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`, `ForMathlib.RepresentationTheory.Hecke.Operators`
- `ForMathlib.RepresentationTheory.Hecke.Operators`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`
- `ForMathlib.RepresentationTheory.Hecke.OrdinaryR`: `ForMathlib.Algebra.Polynomial.Reciprocal`, `ForMathlib.RepresentationTheory.Hecke.Inverse`
- `ForMathlib.RepresentationTheory.Hecke.PositiveWord`: `ForMathlib.GroupTheory.Coxeter.Bruhat.LowerFinset`, `ForMathlib.RepresentationTheory.Hecke.Coefficients`, `ForMathlib.RepresentationTheory.Hecke.DualR`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`: `ForMathlib.Algebra.Polynomial.LowPart`, `ForMathlib.RepresentationTheory.Hecke.OrdinaryR`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Dihedral`: `ForMathlib.GroupTheory.Coxeter.Dihedral.Words`, `ForMathlib.RepresentationTheory.Hecke.DualR`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction`: `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport`: `ForMathlib.Algebra.Polynomial.ScaledEvaluation`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`: `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`: `ForMathlib.GroupTheory.Coxeter.Bruhat.Defs`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Parabolic`: `ForMathlib.GroupTheory.Coxeter.Parabolic.Standard`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Canonical`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`: `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalization`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.SelectedR`: `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Unique`: `ForMathlib.Algebra.Polynomial.Reciprocal`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Basic`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `ForMathlib.RingTheory.Localization.RelativePrime`: (Mathlib only)
- `OAI.KL.BottSamelson.AdjointSheaf`: `ForMathlib.Algebra.Module.Graded.Adjoint`, `ForMathlib.Algebra.Module.Localization.Lattice`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Summand`, `ForMathlib.LinearAlgebra.ConjugateRange`, `ForMathlib.LinearAlgebra.Dual.TransportPairing`, `OAI.KL.BottSamelson.UpperSections`
- `OAI.KL.BottSamelson.CanonicalPairing`: `ForMathlib.Combinatorics.MomentGraph.Boundary.Uniqueness`, `OAI.KL.BottSamelson.Character`
- `OAI.KL.BottSamelson.Character`: `ForMathlib.Combinatorics.MomentGraph.Boundary.Models`, `ForMathlib.RepresentationTheory.Hecke.PositiveWord`, `OAI.KL.BottSamelson.Support`, `OAI.KL.Sheaves.FreeModel`, `OAI.KL.BottSamelson.StalkCharacter`, `OAI.KL.BottSamelson.Flabby`
- `OAI.KL.BottSamelson.CharacterDecomposition`: `OAI.KL.Sheaves.Reciprocity`
- `OAI.KL.BottSamelson.Flabby`: `OAI.KL.BottSamelson.UpperSections`
- `OAI.KL.BottSamelson.StalkCharacter`: `ForMathlib.Algebra.Module.Graded.Hilbert.Numerator`, `ForMathlib.RepresentationTheory.Hecke.Coefficients`, `OAI.KL.BottSamelson.Stalks`
- `OAI.KL.BottSamelson.Stalks`: `ForMathlib.Algebra.Module.Free.ScalarDivisibility`, `ForMathlib.Algebra.Module.Graded.HomogeneousEquiv`, `ForMathlib.Algebra.Module.Graded.FinitePieces`, `ForMathlib.Algebra.Module.Graded.ModuleData.PairProjection`, `ForMathlib.Algebra.Module.Graded.ModuleData.CoefficientChange.Basic`, `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`, `ForMathlib.Algebra.Module.ReflectionPair.TensorKernel`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Defs`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.AttachBottom`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Reindex`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Properties`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`, `ForMathlib.LinearAlgebra.TensorProduct.Coordinates`, `ForMathlib.RepresentationTheory.BottSamelson.TitsWords`, `OAI.KL.Compatibility.KernelTransport`
- `OAI.KL.BottSamelson.Support`: `ForMathlib.Algebra.Module.Graded.ModuleData.Duality`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`, `ForMathlib.LinearAlgebra.Dual.BalancedCut`, `OAI.KL.BottSamelson.AdjointSheaf`, `OAI.KL.Sheaves.LowerCharacter`, `OAI.KL.BottSamelson.Flabby`
- `OAI.KL.BottSamelson.UpperSections`: `ForMathlib.Algebra.Module.Localization.FiniteCharacters`, `ForMathlib.Algebra.Module.Localization.ProjectiveLattice`, `ForMathlib.Algebra.Module.Projective.Range`, `ForMathlib.Algebra.Module.ReflectionPair.TensorDescent`, `ForMathlib.LinearAlgebra.KernelCoordinates`, `ForMathlib.LinearAlgebra.PairProjection`, `ForMathlib.LinearAlgebra.Reflection.Classification`, `OAI.KL.BottSamelson.Stalks`
- `OAI.KL.Comparison.Propagation`: `ForMathlib.Algebra.Module.Graded.RegularScalar`, `ForMathlib.Algebra.Module.Projective.ScalarKernel`, `ForMathlib.Algebra.Order.Field.RealScaling`, `ForMathlib.Combinatorics.DirectedPaths.Monotone`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Hilbert`, `OAI.KL.Comparison.Transport`, `OAI.KL.Localization.Ambient`
- `OAI.KL.Comparison.SuffixFreeness`: `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `ForMathlib.Combinatorics.DirectedPaths.Suffix`, `OAI.KL.Localization.Edge`
- `OAI.KL.Comparison.Transport`: `ForMathlib.Combinatorics.DirectedPaths.ScalarMap`, `ForMathlib.Combinatorics.MomentGraph.Boundary.Extension`, `ForMathlib.RepresentationTheory.Hecke.DyerPaths.Wall`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.ScaledReciprocity`, `OAI.KL.BottSamelson.CanonicalPairing`, `OAI.KL.Sheaves.StalkReciprocity`
- `OAI.KL.Invariance.Finite`: `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `ForMathlib.Algebra.Polynomial.ScaledEvaluation`, `ForMathlib.Algebra.Polynomial.TransferEvaluation`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Transport`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.IntervalTransport`, `OAI.KL.Comparison.SuffixFreeness`
- `OAI.KL.Invariance.Main`: `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.FiniteRankReduction`, `OAI.KL.Invariance.Finite`
- `OAI.KL.Localization.Ambient`: `ForMathlib.GroupTheory.Coxeter.Roots.LaterCount`, `OAI.KL.Sheaves.Support`
- `OAI.KL.Localization.Edge`: `ForMathlib.Algebra.Module.Quotient.ScalarImage`, `OAI.KL.Comparison.Propagation`, `OAI.KL.Localization.TerminalImages`
- `OAI.KL.Localization.GraphEmbedding`: `ForMathlib.GroupTheory.Coxeter.Roots.Splines`, `ForMathlib.LinearAlgebra.PlaneReduction`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.Quotient`, `OAI.KL.Localization.Ambient`
- `OAI.KL.Localization.Plane`: `ForMathlib.Combinatorics.MomentGraph.Bruhat.PlaneModel`, `ForMathlib.Combinatorics.MomentGraph.Sheaf.Localization`, `ForMathlib.RingTheory.Localization.RelativePrime`, `OAI.KL.Localization.GraphEmbedding`
- `OAI.KL.Localization.TerminalImages`: `ForMathlib.Combinatorics.MomentGraph.Sheaf.ScaledImages`, `OAI.KL.Localization.Plane`
- `OAI.KL.Sheaves.Boundary`: `ForMathlib.Algebra.Module.Graded.NonnegativeBasis`, `ForMathlib.Combinatorics.MomentGraph.Bruhat.Basic`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Extension`, `ForMathlib.GroupTheory.Coxeter.Bruhat.Descent`, `ForMathlib.GroupTheory.Coxeter.Roots.Basic`, `ForMathlib.LinearAlgebra.SymmetricAlgebra.RootIdeal`, `ForMathlib.RepresentationTheory.KazhdanLusztig.Polynomials.Normalized`
- `OAI.KL.Sheaves.FreeModel`: `ForMathlib.Algebra.Module.Graded.ModuleData.CharacterDual`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Models`, `ForMathlib.RepresentationTheory.Hecke.OrdinaryR`, `OAI.KL.Sheaves.LowerCharacter`, `OAI.KL.Sheaves.Support`
- `OAI.KL.Sheaves.LowerCharacter`: `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Character`, `OAI.KL.Sheaves.Boundary`
- `OAI.KL.Sheaves.Reciprocity`: `OAI.KL.BottSamelson.Character`
- `OAI.KL.Sheaves.StalkReciprocity`: `ForMathlib.Algebra.BigOperators.SingleCoordinate`, `OAI.KL.BottSamelson.CharacterDecomposition`
- `OAI.KL.Sheaves.Support`: `ForMathlib.Algebra.Module.Graded.HomogeneousDual`, `ForMathlib.Combinatorics.MomentGraph.GradedSheaf.Duality`, `ForMathlib.GroupTheory.Coxeter.Roots.Order`, `OAI.KL.Sheaves.Boundary`
