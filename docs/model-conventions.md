# Mathematical representation conventions

## Ordered exact matchgates

`ExactMatchgate` witnesses a finite weighted plane graph with ordered external vertices and simultaneous simple disjoint exterior-access arcs to a surrounding circle. The arcs avoid graph vertices and edges away from their own starting vertices and retain one global order, including for disconnected graphs. This follows the external-order convention in [Cai and Gorenstein, Matchgates Revisited, p. 178](https://theoryofcomputing.org/articles/v010a007/v010a007.pdf).

The library proves equality of the signature classes described by this model, ordered disk realizations and the literal matchgate identities, with the same `Fin s` tensor coordinates. Disk-to-access uses radial arcs. Access-to-disk uses identities and a constructed realization; the realizing graph may change. Field-preserving realization preserves the specified edge-weight subfield.

Bare cofaciality or independently rotated connected components would lose the global order. The model does not claim unchanged-graph normalization from an independently encoded facial-walk or rotation-system representation.

## Ordered planar instances and all-left gadgets

`LabelledInstance.OrderedPlanar` and `AllLeftGadget.OrderedPlanar` use finite crossing-free disk drawings, original marked local port orders and the inherited ordered boundary. Positive radial germs near vertices specify the local representative. Partition functions depend on incidences, labels and argument order, not coordinates, speed or parameterization.

This is the finite plane-graph convention admitting polygonal representatives, as in [Diestel, Graph Theory, sections 4.1–4.2](https://www.emis.de/monographs/Diestel/en/GraphTheoryII.pdf). It is an explicit modelling choice. A machine-checked equivalence with a separately defined type of every arbitrary non-radial continuous embedding is not included.

`allLeftSubstitutionRouting` quantifies over every existing `OrderedPlanar` witness. It constructs collars, polygonal corridors, parallel wires, connectors and ordered exterior access. Input ribbons or a completed substitution certificate are not assumed. The zero-width case is covered in the actual substitution theorem.

## Labels, equivalence and width

Finite labelled families distinguish coincident tensors with different labels. Exact equivalence preserves the graph, incidences, marked first ports, arities and linearized cyclic orders, with arity-preserving label bijections. Every instance value is equal exactly, including zero tensors and scalar nullaries. Gadget substitution or equality up to a scalar is not part of this equivalence.

Alternative presentations may change the finite nonempty domain, base and all complex coefficients, without a rank restriction. Width zero has a singleton Boolean alphabet but still retains declared domain arity.

The class-based negative theorems also hold for any larger instance predicate containing the explicit ordered-planar model. They prove finite-width witnesses and lower bounds for that class's own minimum, without identifying minima across different models. Positive gadget statements quantify over the chosen `OrderedPlanar` representation.

## Coordinates, fields and Clifford action

`BooleanInput t` is `Fin t → Fin 2`; some geometric interfaces use the equivalent `Bool` words. Conversions retain increasing coordinate positions. Matchgate matrices place increasing input ports before reversed output ports. Tensor blocks and their internal wire order remain explicit.

Pfaffians use increasing selected indices and the recursive expansion, with proved equality to the signed pair-partition sum and the general permutation formula. Clifford matrices use signed insertion/deletion in the ordered exterior-monomial basis. Cover theorems construct the joint-kernel row space directly; no unproved Witt extension or canonical-form premise is imported.

The local Lindemann and multiquadratic developments prove the exponential-independence consequence needed for the paper. They do not claim a complete formalization of every stronger background theorem cited in the manuscript.
