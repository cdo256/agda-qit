---
aliases:
  - Mobiles as QIIT
  - Plump Ordinals for Mobiles
title: Mobiles as a Quotient-Inductive Type via Plump Ordinals
---

## Abstract

This note describes a construction of infinitary mobiles as a quotient-inductive type. The construction proceeds in two stages. First, we give a setoid-based description in terms of a transfinite diagram indexed by a plump tree ordinal $(T,\le)$. Second, we show that the same construction can be carried out directly in the category **Set**, assuming the availability of non-recursive quotients or colimit higher inductive types.

The key property of the index order $T$ is that it possesses a *definable supremum*: every family of elements indexed by $I$ has a canonical upper bound. This avoids the need for WISC (the Weakly Initial Set of Covers), which is typically required to ensure that polynomial functors preserve colimits in exact completions. Our construction is an instance where these general-purpose axioms are unnecessary.

## Setoid Infrastructure

Before presenting the construction, we establish the fundamental categorical infrastructure based on setoids.

### Setoids

A **setoid** $S = (|S|, {\approx_S})$ consists of a set $|S|$ equipped with an equivalence relation ${\approx_S}$ satisfying:

- **Reflexivity**: $x \approx_S x$ for all $x \in |S|$
- **Symmetry**: $x \approx_S y$ implies $y \approx_S x$
- **Transitivity**: $x \approx_S y$ and $y \approx_S z$ implies $x \approx_S z$

Setoids provide a foundation for working with quotient types while maintaining computational content.

### Setoid Homomorphisms

A **setoid homomorphism** $f: S \to T$ is a function $f: |S| \to |T|$ that respects the equivalence relations:

$$x \approx_S y \implies f(x) \approx_T f(y)$$

Setoid homomorphisms compose in the obvious way, and every setoid has an identity homomorphism.

Two homomorphisms $f, g : S \to T$ are **homomorphically equivalent** if for all $x \approx_S y$, we have $f(x) \approx_T g(y)$. This yields an equivalence relation on the hom-sets, making setoids into a category **Setoid**.

### Setoid Isomorphisms

A **setoid isomorphism** $\phi: S \cong T$ consists of setoid homomorphisms $\phi: S \to T$ and $\phi^{-1}: T \to S$ such that:

$$\phi^{-1} \circ \phi \approx \mathrm{id}_S \quad \text{and} \quad \phi \circ \phi^{-1} \approx \mathrm{id}_T$$

where $\approx$ denotes homomorphic equivalence. Setoid isomorphism defines an equivalence relation on setoids.

### Setoid Functors

A **setoid functor** $F: \mathbf{Setoid} \to \mathbf{Setoid}$ assigns to each setoid $S$ a setoid $F(S)$, and to each homomorphism $f: S \to T$ a homomorphism $F(f): F(S) \to F(T)$, satisfying:

- **Identity**: $F(\mathrm{id}_S) \approx \mathrm{id}_{F(S)}$
- **Composition**: $F(g \circ f) \approx F(g) \circ F(f)$
- **Congruence**: $f \approx g$ implies $F(f) \approx F(g)$

These conditions ensure that $F$ is a proper functor on the category of setoids.

## Raw infinitary trees and plumpness

Fix a set $I\neq \emptyset$, either finite or infinitary. Define the W Type $T$ of $I$-branching trees:

$$\mathsf{leaf} : T, \qquad \mathsf{node} : (I \to T) \to T.$$
Expressed as a container, this is:
$$
S_{T} = \mathbb{2}; \qquad P_{T}=[\bot,I];\qquad T= W~ S_{T}~ P_{T}
$$
We extend this to the plump ordinal trees over the W Type as:
$$
S_{Z} = \mathbb{3}; \qquad P_{Z}=[\bot,\mathbb{2} ,I]; \qquad Z=W~S_{Z}~P_{Z}
$$
This is because two compare two diagrams over ordinals $\alpha$ and $\beta$, we must be able to join the ordinals. This is necessary for proving congruence on the reverse direction of cocontinuity. The exact W type doesn't matter except that it must have sufficient constructors to be able to cover all branching cases, have a $\bot$ constructor (so it's not empty), and a join $\_\vee\_:Z\to Z \to Z$. This gives rise to a natural inclusion:
$$
\begin{aligned}
\iota_T &:&T&\to &Z&\\
\iota_T&:&sup(\bot,f)&\mapsto &sup(\bot,f)&\\
\iota_T&:&sup(I,f)&\mapsto& sup(I,f)&
\end{aligned}
$$
Define the plump order, defined as an inductive-inductive type with two kinds $<,\le:Z\to Z\to Prop$ on $Z$ inductively:

$$
\begin{align*}
\frac{\exists i. \alpha \le f i}{\alpha < sup(s,f) }\qquad\frac{\forall i.f i<\alpha }{sup(s,f)\le \alpha } \qquad \forall i\in b,~s:s_z,~f:p_z~s \to z,~\alpha :z \\
\end{align*}
$$

### Properties of the Plump Ordering

The plump ordering satisfies the following key properties, all proven constructively in the Agda formalization:

**Reflexivity**: For all $i : Z$, we have $i \le i$. This is proven by structural induction:
$$\frac{\forall x. f(x) < \sup(s,f)}{\sup(s,f) \le \sup(s,f)}$$

**Transitivity**: The plump ordering satisfies multiple forms of transitivity, proven by mutual recursion:
- $\le$ is transitive: $i \le j \land j \le k \implies i \le k$ 
- $<$ is transitive: $i < j \land j < k \implies i < k$
- Mixed transitivity: $i \le j \land j < k \implies i < k$ and $i < j \land j \le k \implies i < k$

**Well-foundedness**: The strict ordering $<$ is well-founded, meaning every element is accessible under the relation. This provides the foundation for transfinite induction principles over plump trees.

**Preorder Structure**: The relation $\le$ forms a preorder on $Z$ with reflexivity and transitivity, providing the categorical foundation for diagram indexing.

**Subset Characterization**: We can characterize the ordering using subset relations on the strict predecessors and successors:

For plump trees $i, j : Z$, we define:
- $i \subseteq j$ (downward closure) as $\forall k : Z. k < i \implies k < j$
- $i \supseteq j$ (upward closure) as $\forall k : Z. i < k \implies j < k$

Intuitively, $i \subseteq j$ means that every strict predecessor of $i$ is also a strict predecessor of $j$, while $i \supseteq j$ means that every strict successor of $i$ is also a strict successor of $j$. Since we're working with well-founded trees rather than classical sets, "subset" here refers to inclusion of the strict predecessor sets in the well-founded ordering.

- **Equivalence**: $i \le j \iff i \subseteq j$ and $i \le j \implies j \supseteq i$

**Quasi-extensionality**: The plump ordering is quasi-extensional, meaning:
$$(i \le j \land j \le i) \iff (i \subseteq j \land j \subseteq i)$$

This property connects the ordering structure with the subset structure, providing a foundation for extensional reasoning about plump trees and enabling the definable supremum property crucial for cocontinuity.

We then define $<_T:T\to Z \to Prop$ as
$$t<_T \alpha =\iota_T~ t < \alpha$$
This gives us a way to bound trees by size ordinals.
## Setoid construction of mobiles

### Stage sets

For each $\alpha:Z$, define

$$S(\alpha ) := \{\,u : T \mid u <_T \alpha \,\}.$$

Define an equivalence relation $\approx$ on $S(t)$ by the following generators:

- $\mathsf{leaf} \approx \mathsf{leaf}$
- if $\forall i,\; f(i)\approx g(i)$ then $\mathsf{node}(f)\approx \mathsf{node}(g)$
- for any bijection $\pi : I \cong I$, if $\forall i,\; f(i)\approx g(\pi(i))$ then both $\mathsf{node}(f)\approx \mathsf{node}(g)$ and $\mathsf{node}(g)\approx \mathsf{node}(f)$

Let $P(t)$ be the setoid whose carrier is $S(t)$ and whose relation is $\approx$.

### The diagram $P$

If $p : t \le u$, then $S(t) \subseteq S(u)$, so we obtain a setoid morphism $P(p) : P(t) \to P(u)$ by inclusion. This yields a diagram

$$P : (T,\le) \longrightarrow \mathrm{Setoid}.$$

### The setoid colimit

Define $\mathrm{colim}\,P$ as the quotient of the disjoint union $\sum_{t:T} |P(t)|$ by the equivalence generated by:

$$(t,x) \sim (u,P(p)(x)) \qquad\text{for all } p : t\le u.$$

This gives a setoid $(|\mathrm{colim}\,P|,\sim)$ with injections

$$\iota_t : P(t) \longrightarrow \mathrm{colim}\,P.$$

### The quotient-polynomial functor

Define an endofunctor on setoids:

$$\widetilde F_B(X,\approx_X) := \bigl( 1 + (I \to X) \bigr) / \approx_F,$$

where $\approx_F$ is the smallest equivalence relation generated by:

$$\mathsf{Leaf} \approx_F \mathsf{Leaf},$$

$$\mathsf{Node}(f) \approx_F \mathsf{Node}(g) \;\text{if}\; \forall i,\; f(i)\approx_X g(i),$$

$$\mathsf{Node}(f) \approx_F \mathsf{Node}(g) \;\text{if}\; \exists \pi : I\cong I,\ \forall i,\ f(i)\approx_X g(\pi(i)).$$

### Cocontinuity

A crucial lemma is that for any $g : I \to \mathrm{colim}P$, if $g(i)$ is represented by $(t_i,x_i)$ then the definable supremum

$$t^* := \mathsf{node}(i \mapsto t_i)$$

satisfies $t_i \le t^*$, hence

$$g = \iota_{t^*} \circ h$$

for the unique $h : I \to P(t^*)$ defined by $h(i) := P(t_i\le t^*)(x_i)$. This supplies the factorisation needed to prove that $\widetilde F_B$ preserves this colimit.

## Constructing Mobiles Directly in Set

In this section we reinterpret the construction internally in Set, using a colimit higher inductive type. No use of WISC is required because the index order $(T,\le)$ has a definable supremum.

### Explicit colimit constructors

Define the colimit as a [[Higher Inductive Type]] $M_B$ with constructors:

**Points:**

$$\mathsf{inc}(t,x) : M_B \qquad (t : T,\ x : P(t)).$$

**Paths:**

$$\mathsf{glue}(p,x) : \mathsf{inc}(t,x) = \mathsf{inc}(u, P(p)(x)) \qquad (p : t\le u).$$

No further constructors are required.

### The functor $\widetilde F_B$ on Set

Define

$$\widetilde F_B(X) := \left( 1 + (I \to X) \right) / \approx,$$

where $\approx$ is the same permutation-generated relation as in the setoid case.

### Cocontinuity in Set

Given $g : I \to M_B$, write $g(i)=\mathsf{inc}(t_i,x_i)$. Define $t^* := \mathsf{node}(i \mapsto t_i)$ and

$$h(i) := P(t_i\le t^*)(x_i).$$

Then

$$g(i) = \mathsf{inc}(t^*,h(i))$$

up to paths generated by $\mathsf{glue}$. This provides the factor needed for the $\psi$ map of the cocontinuity equivalence.

### The initial algebra

Cocontinuity yields an isomorphism

$$\widetilde F_B(M_B) \cong \mathrm{Colim}(\widetilde F_B \circ P),$$

from which we obtain a structure map

$$\mathsf{mob}_B : \widetilde F_B(M_B) \to M_B.$$

By transfinite induction along $T$ and the colimit universal property, one obtains a unique algebra morphism into any other $\widetilde F_B$-algebra. Hence:

**Theorem.** $M_B$ is the [[Initial Algebra]] for $\widetilde F_B$.

## Remarks on WISC

In general, proving that a polynomial or quotient-polynomial functor preserves colimits in a quotient completion requires a principle such as [[WISC]] to factor arbitrary maps through a small family of covers. In this specific case, the definable supremum provided by the plump order $(T,\le)$ replaces the need for any choice principle.
