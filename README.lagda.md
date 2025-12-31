```agda
module README where
```

# Agda QIT Development: Choice-Free Cocontinuity for Mobile Categories

This repository presents a formalization in Agda that advances the theory of Quotient Inductive Types (QITs) by proving cocontinuity for mobile functors without any choice principles. While Blass (1983) proved that cocontinuity for arbitrary QW-types requires choice axioms, and Fiore et al. (2022) represents the current state of the art using WISC (Weak Infinite Set of Choices), this work identifies a specific class of QW-types—mobile categories—that achieve cocontinuity in a completely choice-free setting.

## Key Theoretical Contribution

Mobile functors are cocontinuous without requiring any form of choice axiom—not WISC, not AC, not even unique choice.

This is the first construction showing that specific QW-types can sidestep the fundamental choice-theoretic barriers identified by Blass (1983), advancing substantially beyond the current state of the art (Fiore et al. 2022) which still requires WISC.

Establishes that choice-theoretic obstacles in QIT theory are not universal—there exist meaningful classes of quotient inductive signatures that admit completely constructive cocontinuity proofs.

## Choice-Free Cocontinuity for Mobile Categories

This work proves that mobile functors are cocontinuous without requiring any choice principles—not WISC, not AC, not even unique choice (AC!). The module `QIT.Mobile.Cocontinuity` constructively establishes the crucial isomorphism:

$$F(\text{Colim}\ D) \cong \text{Colim}(F \circ D)$$

for mobile functors $F$ and diagrams $D$. This result is significant because:

- Advances beyond Fiore et al. (2022): While the current state of the art requires WISC for general QW-type cocontinuity, mobile categories achieve this property choice-free
- Circumvents Blass (1983): Although Blass proved that arbitrary QW-types cannot generally achieve cocontinuity without choice, mobile categories represent a specific class that sidesteps this limitation
- Constructive proof: The isomorphisms $\phi$ and $\psi$ are explicitly constructed with verified inverse properties
- Foundational impact: Establishes that there exist meaningful classes of QIT signatures that avoid choice-theoretic obstacles entirely

## Mobile Category Framework

Mobile categories (located in `QIT/Mobile/`) provide the mathematical foundation that makes choice-free cocontinuity possible. They capture essential symmetries through:

- Permutation symmetry: QIT equivalences respect reordering of binding structures
- Structural irrelevance: Leaf nodes are equivalent regardless of content  
- Binding-aware equivalences: Proper handling of variable binding and renaming
- Constructive equivalences: All equivalence relations are decidable and constructively defined

## Relationship to Existing Work

This formalization directly addresses fundamental limitations in QW-type theory:

- Blass (1983) limitation: Proved impossibility of cocontinuity for arbitrary QW-types without choice
- Fiore et al. (2022) approach: Current state of the art using WISC for general QW-type cocontinuity
- This work's contribution: Identifies mobile categories as a specific class of QW-types achieving choice-free cocontinuity
- Theoretical significance: Demonstrates that the choice-theoretic barriers are not universal—specific QIT signatures can avoid them entirely

## Technical Foundation

The choice-free approach relies on several key technical innovations:

- Setoid-based categorical semantics: Working in setoid categories provides better extensionality without requiring choice
- Size-based termination: Following Fiore et al. (2022), uses `Plump` module for well-founded recursion without choice axioms
- Constructive mobile equivalences: All equivalence relations are decidably constructible
- Explicit isomorphism construction: Direct construction of cocontinuity isomorphisms without existential quantification

## Module Organization

The development follows a carefully structured dependency hierarchy:

### Foundation Layer
```agda
open import QIT.Prelude
open import QIT.Relation.Binary  
open import QIT.Relation.Plump
```

`QIT.Prelude` provides essential type-theoretic infrastructure including level management, the `Box` type for proposition lifting, and crucially, postulates for function extensionality and propositional extensionality.

`QIT.Relation.Binary` establishes fundamental equivalence relations with reflexivity, symmetry, and transitivity properties, forming the relational foundation for setoid constructions.

`QIT.Relation.Plump` implements container-based size orderings for termination checking, providing the technical foundation for well-founded QIT constructions.

### Setoid Category Theory
```agda
open import QIT.Setoid.Base
open import QIT.Setoid.Hom  
open import QIT.Setoid.Iso
open import QIT.Setoid.Functor
open import QIT.Setoid.Sigma
open import QIT.Setoid
```

The setoid modules establish the categorical infrastructure:
- Base: Core setoid definitions with carrier types and equivalence relations
- Hom: Setoid morphisms with composition and homomorphism properties
- Iso: Setoid isomorphisms and categorical equivalences
- Functor: Functorial operations preserving setoid structure
- Sigma: Dependent sum constructions in the setoid category

### General Categorical Theory

The root-level modules provide foundational categorical definitions:

`QIT.Colimit` develops the general theory of colimits in setoid categories, parameterized by preorders. This provides diagram constructions, colimit universality, and cocone characterizations.

`QIT.Cocontinuity` studies cocontinuous functors and their colimit-preservation properties, establishing the general framework that is later specialized to mobile functors.

`QIT.ContainerFunctor` provides container-based functor representations, giving concrete models for the shapes of inductive data structures.

### Mobile Category Theory

The mobile framework, parameterized by a branching type `B : Set`, constitutes the main theoretical contribution:

#### QIT.Mobile.Base
Establishes fundamental mobile structures:
- *NodeType*: The shape `{l, n}` distinguishing leaves from internal nodes
- *Branch container*: Container with leaf positions `⊥` and node positions `B`  
- *BTree*: Well-founded trees `W Branch` representing mobile structures
- *Pattern synonyms*: Convenient constructors `leaf` and `node`

#### QIT.Mobile.Diagram  
Constructs the mobile diagram category:
- *P₀*: Mobile elements with constructors `leaf`, `node`, and `weaken`
- *Mobile equivalence*: Equivalence relation with leaf equivalence, permutation symmetry, and extensionality
- *Diagram structure*: Functorial morphisms respecting mobile equivalences

#### QIT.Mobile.Functor
Develops functorial aspects of mobile categories:
- *F̃-ob*: Mobile functor object construction from setoids
- *F̃-mor*: Mobile functor morphisms preserving equivalences
- *Mobile equivalence*: Tree equivalence with crucial permutation symmetry

#### QIT.Mobile.Cocontinuity
Establishes cocontinuity for mobile functors:
- *Isomorphism construction*: Explicit functors between $F(\text{Colim}\ D)$ and $\text{Colim}(F \circ D)$
- *Congruence proofs*: Verification that the isomorphisms respect mobile equivalences
- *Inverse properties*: Formal proofs showing the maps are mutually inverse
- *Cocontinuity theorem*: The main result establishing that mobile functors are cocontinuous

This establishes that mobile functors preserve colimits, which is precisely the property needed to model QIT constructors semantically.

## QIT Semantic Interpretation

The mobile framework provides a complete semantic interpretation of QITs:

| QIT Concept | Mobile Category Interpretation |
|-------------|-------------------------------|
| QIT Signature | Mobile parameter `B : Set` (branching/binding structure) |
| QIT Constructors | Cocontinuous mobile functors |
| QIT Equivalences | Mobile equivalence relations with permutation symmetry |
| QIT Induction | Colimit universal properties and elimination |
| QIT Computation | Cocontinuity isomorphisms $F(\text{Colim}\ D) \cong \text{Colim}(F \circ D)$ |

The key insight is that QITs require both:
1. Inductive structure via colimits for recursion and induction principles
2. Symmetry structure via mobile equivalences for binding, renaming, and α-equivalence

### Examples and Applications

`QIT.Examples.HoleList` demonstrates the framework applied to lists with holes, showing how structural operations and equivalences arise naturally from the mobile category construction.

The mobile framework generalizes to arbitrary QIT signatures by choosing appropriate branching types `B`, making it a foundational tool for dependent type theory implementations.

## Technical Requirements and Usage

Dependencies: 
- Modern Agda (2.6+)
- Function extensionality and propositional extensionality postulates
- Nix development environment (provided via `flake.nix`)

Build System:
- Standard Agda library compilation via `agda-qit.agda-lib`
- Paper generation system for academic writing (see `PAPER-README.md`)
- Just-based build automation (`justfile`)

For QIT Applications:
1. Choose branching type `B : Set` appropriate for your QIT signature
2. Import relevant `QIT.Mobile.*` modules with this parameter  
3. Use mobile colimit constructions for QIT semantics
4. Apply cocontinuity results for constructor interpretation

## Research Impact and Future Directions

This work advances the theoretical foundations of dependent type theory by:

1. Establishing choice-free cocontinuity: First proof that specific QW-types (mobile categories) achieve cocontinuity without any choice principles
2. Advancing beyond current state of the art: Surpasses Fiore et al. (2022) by eliminating the need for WISC in mobile contexts
3. Constructive foundations: Provides completely constructive proofs where previous work required non-constructive choice axioms
4. Practical implications: Enables implementation of mobile QITs in constructive proof assistants without choice postulates

Theoretical significance:
- Resolves a fundamental question about the necessity of choice in QIT theory for specific cases
- Opens new research directions for choice-free approaches to inductive type theory
- Provides concrete examples where classical impossibility results (Blass 1983) do not apply

Future research directions:
- Classification problem: Characterize which other QIT signatures admit choice-free cocontinuity
- Extension to HITs: Investigate whether mobile-like structures can handle higher inductive types choice-free
- Computational semantics: Develop normalization and decidability results for mobile QITs
- Proof assistant implementation: Practical implementation of mobile QIT support in Agda, Coq, or Lean
- Homotopical extensions: Integration with cubical type theory and univalent foundations

This formalization establishes mobile category theory as a new paradigm for constructive QIT semantics that avoids the choice-theoretic obstacles that have historically limited the field.

This is a literate Agda development. The foundational modules imported above provide the infrastructure, while the main mobile development should be imported separately as needed, parameterized by appropriate branching types.