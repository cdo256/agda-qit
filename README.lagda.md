```agda
module README where
```

# Agda QIT Development

This repository contains a formalization of Quotient Inductive Types (QITs) in Agda, exploring their categorical structure through setoids, colimits, and mobile functors. The main theoretical contribution is the **mobile category framework** developed in the `Mobile/` directory, which provides the proper categorical semantics for QITs.

## Module Organization

The development follows a carefully structured dependency order, building from foundational concepts to the advanced mobile category theory that forms the core of the QIT construction.

### 1. Foundational Infrastructure

First, we establish basic utilities and type-theoretic foundations:

```agda
open import QIT.Prelude
```

The `Prelude` module provides essential utilities including level management, propositional equality, the `Box` type for lifting propositions, and crucially, postulates for function extensionality and propositional extensionality that are needed throughout the development.

```agda
open import QIT.Relation.Binary
```

The `Equivalence` module defines fundamental notions of equivalence relations including reflexivity, symmetry, and transitivity properties. This provides the basic relational foundation for working with setoids and mobile equivalences.

```agda
open import QIT.Relation.Binary
```

The `Order` module provides accessibility predicates and well-founded recursion principles essential for defining inductive types and proving termination of QIT eliminators.

### 2. Setoid Category

Building on equivalence relations, we develop the category of setoids:

```agda
open import QIT.Setoid.Base
open import QIT.Setoid.Hom
open import QIT.Setoid.Iso
open import QIT.Setoid.Functor
open import QIT.Setoid.Sigma
```

The setoid modules establish the categorical infrastructure:
- **Base**: Core setoid definitions, carrier types, and equivalence relations
- **Hom**: Morphisms between setoids, homomorphism properties, and composition
- **Iso**: Isomorphisms and equivalences of setoids for categorical equivalence
- **Functor**: Functorial operations on setoids, preserving structure
- **Sigma**: Dependent sum types in the setoid category for dependent constructions

```agda
open import QIT.Setoid
```

The main `Setoid` module provides a unified interface to all setoid constructions, serving as the entry point to setoid category theory.

```agda
open import QIT.Relation.Plump
```

The `Plump` module implements size-based termination checking using container-based sizes, following Fiore et al. 2022. This provides the technical foundation for ensuring termination in QIT eliminators and is crucial for the mobile construction.

## 3. General Categorical Definitions

The root-level modules provide general definitions that are later specialized in the mobile setting:

### Colimit Theory (General Framework)

The `Colimit` module develops the general theory of colimits in categories of setoids, parameterized by a preorder. This provides:
- Diagram definitions over arbitrary preorders
- Colimit construction as quotients of disjoint unions
- Cocone definitions and universal properties
- The foundational colimit machinery that is specialized in the mobile setting

### Cocontinuity Theory (General Framework)

```agda
-- Note: Cocontinuity module is parameterized and not imported directly
-- open import Cocontinuity ≤p  -- where ≤p is a preorder
```

The `Cocontinuity` module studies cocontinuous functors and their interaction with colimits:
- Preservation of colimits by functors
- Cocontinuity conditions and characterizations
- The general framework for functors that preserve the colimit structure

### Container Functors

```agda
-- Note: ContainerFunctor module is parameterized and not imported directly
-- open import ContainerFunctor C  -- where C is a container
```

The `ContainerFunctor` module provides a setoid-based treatment of container functors, giving concrete representations for the shapes of data structures that can be turned into QITs.

### Tree Ordinals

```agda
-- Note: TreeOrdinals has naming conflicts with standard library
-- open import TreeOrdinals  -- import separately when needed
```

The `TreeOrdinals` module develops tree-based ordinal representations using binary trees, providing a concrete model for well-founded relations used in QIT constructions. Note: This module has naming conflicts with the standard library's `Setoid` and should be imported separately when needed.

## 4. The Mobile Construction (Main Development)

The core theoretical contribution lies in the `Mobile/` directory, which develops the mobile category framework specifically designed for QIT semantics. Due to the parameterized nature of these modules, they are described here but not imported directly.

### Mobile Base Theory

**`Mobile.Base`** introduces the fundamental mobile structures parameterized by a branching type `B : Set`:

```agda
-- Example usage (not imported to avoid parameter conflicts):
-- open import Mobile.Base B
```

- **`NodeType`**: The basic shape `{l, n}` distinguishing leaves from nodes
- **`Branch` container**: The container `Branch : Container` with:
  - Shape = `NodeType`
  - Positions: `l` has no positions (empty), `n` has positions indexed by `B`
- **`BTree`**: The well-founded trees `W Branch` representing mobile structures
- **Pattern synonyms**: `leaf` and `node` for convenient tree construction

This establishes the basic mobile data structures where `B` represents the branching/binding structure of the QIT being constructed.

### Mobile Equivalence Relations

**`Mobile.Equivalence`** defines the crucial mobile equivalence `_≈ᵗ_` that captures the essential QIT equivalences:

```agda
-- Example usage (not imported to avoid parameter conflicts):
-- open import Mobile.Equivalence B
```

- **`≈leaf`**: All leaves are equivalent (structural irrelevance of leaf data)
- **`≈node`**: Node equivalence respects the underlying setoid structure pointwise
- **`≈perm`**: Critical symmetry - nodes are equivalent up to permutation of branches indexed by `B`
- **`≈trans`**: Transitivity closure to make it a proper equivalence

This equivalence relation encodes the key QIT properties: structural equivalence, respect for the underlying type structure, and most importantly, **symmetry under permutations** which is essential for handling the symmetries in QIT constructions.

### Mobile Colimit Construction

**`Mobile.Colimit`** constructs colimits in the mobile setting using the plump/size-based approach:

```agda
-- Example usage (not imported to avoid parameter conflicts):
-- open import Mobile.Colimit B
```

- **Size-based indexing**: Uses the `_<_` relation from `Plump Branch` to create well-founded size orderings
- **`Sz` setoids**: For each tree `t`, constructs `Sz t` as the setoid of smaller trees with mobile equivalence
- **`≤p` preorder**: The preorder structure needed for colimit constructions
- **Mobile colimits**: Specializes the general colimit construction to mobile setoids

This provides the categorical colimit structure needed to model QIT constructors as colimits of mobile diagrams.

### Mobile Functor Theory

**`Mobile.Functor`** develops functors in the mobile category setting:

```agda
-- Example usage (not imported to avoid parameter conflicts):
-- open import Mobile.Functor B
```

- **Mobile functor objects**: `F̃-ob` constructed from the branch container applied to setoids
- **Mobile functor morphisms**: Respecting the mobile equivalence structure
- **Branch equivalence**: `_≈ᵇ_` relation with leaf equivalence, permutation symmetry, and extensionality
- **Functorial structure**: Making mobile constructions into proper functors

### Mobile Cocontinuity

**`Mobile.Cocontinuity`** establishes the cocontinuity properties crucial for QIT semantics:

```agda
-- Example usage (not imported to avoid parameter conflicts):
-- open import Mobile.Cocontinuity B
```

- **Isomorphisms**: `ϕ` and `ψ` establishing `Colim(F ∘ D) ≅ F(Colim D)` for mobile functors
- **Cocontinuity verification**: Proving mobile functors preserve colimits
- **QIT constructor semantics**: This isomorphism is exactly what's needed to interpret QIT constructors

The cocontinuity isomorphism is the key technical result that allows mobile functors to properly model QIT constructors while preserving the colimit structure that gives QITs their inductive character.

## Key Theoretical Contributions

This development makes several fundamental contributions to QIT theory:

1. **Mobile Category Framework**: The mobile categories provide the correct categorical setting for QITs, handling the symmetries and structural equivalences that are essential to QIT semantics.

2. **Setoid-Based Approach**: Working in setoid categories rather than plain type categories provides better extensionality properties and proper handling of equivalences.

3. **Size-Based Termination**: Integration of modern size-based termination techniques ensures QIT eliminators are total functions.

4. **Cocontinuity Characterization**: The mobile cocontinuity results show precisely how QIT constructors arise as cocontinuous mobile functors.

5. **Permutation Symmetry**: The critical insight that QIT equivalences must respect permutations of branching structure, encoded in the mobile equivalence relations.

## Development Architecture

The logical development follows these key dependencies:

**Foundation Layer:**
- `Prelude` → `Equivalence` → `Order` → `Plump`

**Setoid Category Layer:**
- `Setoid/{Base,Hom,Iso,Functor,Sigma}` → `Setoid`

**General Category Theory:**
- `Colimit` (general colimits in setoid categories)
- `Cocontinuity` (general cocontinuous functors)
- `ContainerFunctor` (container-based functors)

**Mobile Category Theory (Main Development):**

The mobile modules form the core development, all parameterized by `B : Set`:

- **Mobile.Base** - Fundamental mobile structures (NodeType, Branch, BTree)
- **Mobile.Equivalence** - Mobile equivalences with permutation symmetry
- **Mobile.Colimit** - Size-indexed mobile colimit constructions
- **Mobile.Functor** - Mobile functor theory and constructions
- **Mobile.Cocontinuity** - Cocontinuity isomorphisms F(Colim D) ≅ Colim(F ∘ D)

The parameter `B : Set` represents the "signature" or branching structure of the specific QIT being constructed.

## QIT Semantic Interpretation

The mobile framework provides the semantic foundation for QITs as follows:

1. **QIT Signature** → Mobile parameter `B : Set`
2. **QIT Constructors** → Cocontinuous mobile functors
3. **QIT Equivalences** → Mobile equivalence relations `_≈ᵗ_`
4. **QIT Induction** → Colimit universal properties
5. **QIT Computation** → Cocontinuity isomorphisms

The key insight is that QITs require both the inductive structure (via colimits) and the symmetry structure (via mobile equivalences) to properly handle binding, renaming, and structural equivalences.

## Usage Notes

This is a literate Agda development. The core foundational modules imported in this README provide the basic infrastructure. The main mobile development in `Mobile/` should be imported separately as needed, parameterized by the appropriate branching type `B`.

**Technical Requirements:**
- Requires function extensionality and propositional extensionality postulates
- Built with modern Agda (version 2.6+)

**For QIT Applications:**
1. Choose appropriate branching type `B` for your QIT signature
2. Import relevant `Mobile.*` modules with this parameter
3. Use mobile colimit and cocontinuity constructions for QIT semantics

The development demonstrates how categorical semantics, specifically mobile category theory, provides the correct mathematical foundation for reasoning about quotient inductive types in dependent type theory.
