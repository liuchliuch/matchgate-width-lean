# Paper correspondence

This review is for [arXiv:2610.00079v1](https://arxiv.org/abs/2610.00079v1). The downloaded TeX matches `paper/ITCS-arxiv.tex` byte for byte (SHA-256 `1f594d297f74f5d267182a4773816f425b37e9fdb996bfccf81e5d80fff27bfd`). Numbering follows the shared theorem/lemma/proposition/corollary/definition/remark counter in the TeX. There are 30 numbered theorem-level results, four definitions and three remarks.

`PaperStatements.lean` gives 41 explicit contracts: 33 contracts cover the 30 theorem-level results, six check definitions, and two cover substantive remark witnesses. Parts of 3.3, 4.3 and 10.9 are separate contracts. Remark 7.2 explains results already covered by 7.1 and 4.2. `PaperProofs.lean` connects each contract to its implementation.

Source correspondence is a mathematical review in the documented geometric model. Compilation, axiom auditing and Comparator check the formal statements and proofs; they do not mechanically establish equivalence to English or TeX.

| Paper | Result | Formal contracts | TeX lines |
|---|---|---|---|
| 2.1 | Definition: Exact labelled equivalence | `claim_2_1` | 495–505 |
| 2.2 | Definition: Minimum exact common width | `claim_2_2_existence`, `claim_2_2_minimum` | 517–524 |
| 3.1 | Theorem: Unbounded exact width with a flag presentation | `claim_3_1` | 570–616 |
| 3.2 | Corollary: Untitled | `claim_3_2` | 626–636 |
| 3.3 | Theorem: Support-geometry trichotomy and an unbounded flag family | `claim_3_3`, `claim_3_3_family` | 643–673 |
| 3.4 | Remark: Structural trichotomy versus width characterization | `claim_3_4` | 675–688 |
| 4.1 | Lemma: Reflection reversal | `claim_4_1` | 929–936 |
| 4.2 | Lemma: Field-preserving matchgate realization | `claim_4_2` | 1046–1053 |
| 4.3 | Lemma: Ordered transpose and Clifford-lift realization | `claim_4_3_transpose`, `claim_4_3_pin` | 1230–1243 |
| 4.4 | Definition: Valid holographic presentation | `claim_4_4` | 1634–1656 |
| 4.5 | Definition: Monomial flag and connection-primality | `claim_4_5_flag`, `claim_4_5_prime` | 1730–1742 |
| 5.1 | Lemma: Coordinate transcendence bound | `claim_5_1` | 1786–1794 |
| 5.2 | Proposition: Sampled star-table bound | `claim_5_2` | 1843–1865 |
| 5.3 | Lemma: Dimension of the matchgate variety | `claim_5_3` | 1912–1919 |
| 5.4 | Proposition: Algebraic star-table bound | `claim_5_4` | 1996–2006 |
| 6.1 | Lemma: Independent prime-root exponentials | `claim_6_1` | 2073–2080 |
| 6.2 | Proposition: Explicit transcendental obstruction | `claim_6_2` | 2133–2147 |
| 6.3 | Lemma: Density of the positive integer grid | `claim_6_3` | 2167–2171 |
| 6.4 | Proposition: Positive-integer obstruction | `claim_6_4` | 2183–2206 |
| 6.5 | Remark: Effectivity and height of the integer table | `claim_6_5` | 2247–2255 |
| 7.1 | Theorem: Block-Pfaffian interpolation | `claim_7_1` | 2271–2302 |
| 7.2 | Remark: Exact realization versus parameter matrix | Contracts 7.1 and 4.2 | 2428–2440 |
| 8.1 | Proposition: Exact restriction and rational presentation | `claim_8_1` | 2548–2563 |
| 8.2 | Proposition: Deficiency and essentiality | `claim_8_2` | 2595–2601 |
| 8.3 | Proposition: A genuinely coupled two-center gadget | `claim_8_3` | 2634–2658 |
| 8.4 | Proposition: Closed-form companion presentation | `claim_8_4` | 2702–2711 |
| 9.1 | Corollary: Explicit transcendental companion | `claim_9_1` | 2856–2879 |
| 10.1 | Lemma: Boundary-support monotonicity | `claim_10_1` | 2947–2955 |
| 10.2 | Lemma: Transformed block supports | `claim_10_2` | 2979–2987 |
| 10.3 | Lemma: Rank-two Gaussian hull | `claim_10_3` | 3013–3026 |
| 10.4 | Lemma: Full-row-rank matchgate decoder | `claim_10_4` | 3105–3112 |
| 10.5 | Lemma: Exact-labelled cover compression | `claim_10_5` | 3138–3149 |
| 10.6 | Lemma: Isotropic-kernel cover | `claim_10_6` | 3175–3184 |
| 10.7 | Theorem: Connection-prime collapse | `claim_10_7` | 3236–3249 |
| 10.8 | Lemma: Rank-two block decoding | `claim_10_8` | 3357–3380 |
| 10.9 | Lemma: Rank-one stripping and flag normal form | `claim_10_9_lines`, `claim_10_9_flag` | 3409–3448 |
| 10.10 | Corollary: Binary-context alternative | `claim_10_10` | 3525–3545 |

## Quantifiers and qualifications

- **3.1 and 3.2:** the competitor can change its finite nonempty domain, base, tensors and complex weights. Labels, arities, local port orders and every tested planar instance value are preserved. Width zero is included. The construction, ranks, essentiality, coupling, flag normal form and lower bound use the same selected integer table.
- **3.1 and 9.1:** the class parameter `C` may be any instance predicate containing the chosen ordered-planar model. A self-presentation gives a finite-width witness before taking the actual minimum for that class. No equality between minima for different classes is assumed.
- **3.3:** structural alternatives are mutually exclusive and exhaustive under full base rank, deficiency and essentiality. The uniform fixed-basis all-arity flag normal form and the unbounded-family clause are both included. The ray branch is not a width classification.
- **4.3:** transpose is ordinary transpose. The second contract covers every element of the actual Pin group and every nonzero normalization scalar, including the inverse coefficient matrix.
- **5.3 and 5.4:** dimension is Krull dimension of the reduced vanishing-ideal coordinate ring. Rational definability is equality with a rational zero locus, not containment in a hypersurface.
- **6.1:** the finite-family contract proves the paper statement. The library additionally proves algebraic independence for arbitrary indexed families of distinct primes.
- **6.3:** polynomial-defined Zariski closure is used, not analytic closure. The proof also includes dimension zero.
- **6.5 and 7.2:** effective existence and exact field-preserving realization do not assert useful running time, graph size, coefficient height or bit-length bounds.
- **8.1–8.3:** the literal common-base right restriction, rational edge witnesses, exact coordinate support, all ranks, and connected ordered two-center graph are proved. Generic local wrappers may use any nowhere-zero table; 3.1 assembles every property on one common table.
- **10.1:** the finite-network theorem proves boundary support containment without needing a drawing hypothesis. Its all-left wrapper uses the actual primitive endpoint and preserves incidence.
- **10.8–10.9:** one endpoint encoder is fixed before the tensor or its arity is chosen. The normal form retains the original port order, pure-ray factors, scalar nullaries and full ranks of nonempty cores.
- **10.10:** the three generators are arbitrary nonzero vectors on the specified rays. Invertibility and invariance under independent rescaling are proved, not assumed.

## Unnumbered mathematical interfaces

| Paper content | Library interface |
|---|---|
| Signed pair-partition Pfaffian and permutation signs | `PfaffianPairPartitions`, `PfaffianPairPartitionSign`, `PfaffianGeneralPermutation` |
| Matchgate identities, parity, exact realization and closure | `DiskMatchgateCharacterization`, `StrongExteriorAccess`, `MGIOperations`, `MatchingBoundaryIdentity` |
| Ordered composition, inverse, Gaussian charts and pure-spinor geometry | `MGIMatrixComposition`, `MGIMatrixInverse`, `GaussianMatrixCharts`, `PureSpinorAnnihilator` |
| Unique bounded power-of-two rank, attainment, standard inclusion | `SourceRankRange` |
| Same-order star extraction and arbitrary equivalent presentations | `StarContraction`, `LabelledStarExtraction`, `LabelledInstanceClasses` |
| Holographic identity and arbitrary all-left gadget substitution | `AllLeftGadget.leftTransform_value`, `AllLeftSubstitutionRouting` |
| Symmetry of every left label in the main family | `LeftLabelSymmetry` |
| Finite width maximum with fixed domain, arity, label count and coefficient bound | `FiniteCatalogWidthBound` |

The introduction summarizes 3.1 and 3.3. Section 11 poses open questions about bounded arity, the ray branch, effective height and broader equivalence; these are not claimed as proved. Stronger results from cited literature are replaced by direct proofs of the consequences used here.
