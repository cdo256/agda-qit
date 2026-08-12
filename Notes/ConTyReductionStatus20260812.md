# Proof Status

I have been working on relating two presentations of the ConTy theory and
transferring initiality between them. I have reached a point where I am not
sure whether I am missing a useful displayed-algebra construction, or whether
the category of weakly tagged algebras and its notion of morphism are too weak
for the triangle identity I am trying to prove.

The relevant Agda files are:

- [`QIT/Examples/ConTy/DirectMutualProjectionEquiv.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/DirectMutualProjectionEquiv.agda) - reduction to the mutual essentially algebraic theory.
- [`QIT/Examples/ConTy/MutualProjection.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/MutualProjection.agda) - the many-sorted essentially algebraic algebra `D`.
- [`QIT/Examples/ConTy/MutualWeaklyTagged.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/MutualWeaklyTagged.agda) - the weakly tagged algebra `W` (one sort and no point constructors depending on paths).
- [`QIT/Examples/ConTy/MutualWTToMutual.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/MutualWTToMutual.agda) - the functor `F : W → D`.
- [`QIT/Examples/ConTy/MutualToMutualWT.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/MutualToMutualWT.agda) - the functor `G : D → W`.
- [`QIT/Examples/ConTy/MutualMutualWTEquiv.agda`](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/MutualMutualWTEquiv.agda) - the work-in-progress initiality-transfer proof. The name is misleading: the aim is not to prove an equivalence of categories, but to derive initiality in `D` from initiality in `W`.

## The two presentations

The mutual projection presentation `D` has two sorts:

```agda
Con : Set
Ty  : Set

ty₁ : Ty → Con
```


The point constructors include:

```agda
∙ : Con

▷ : (γ : Con) (a : Ty)
  → ty₁ a ≡ γ
  → Con

u : Con → Ty

π σ : (γ : Con) (a b : Ty)
  → ty₁ a ≡ γ
  → ty₁ b ≡ ▷ γ a _
  → Ty
```

There are also the expected projection and substitution equations.

The category of algebras of this mutual projection form is equivalent to the category of algebras of the direct QIIT presentation by Cartmell's 1986 equivalence of GATs to many-sorted essentially algebraic theories, that I have formalised for ConTy [here](https://github.com/cdo256/agda-qit/blob/main/QIT/Examples/ConTy/DirectMutualProjectionEquiv.agda).

The weakly tagged presentation `W` has one sort `CT`, together with a kinding
operation and three tags:

```agda
CT  : Set
[_] : CT → CT

k̂ ĉ t̂ : CT

kk̂ : [ k̂ ] ≡ k̂
kĉ : [ ĉ ] ≡ k̂
kt̂ : [ t̂ ] ≡ k̂
```

The point operations are total on `CT`, but their kinding equations are
conditional. For example:

```agda
ty₁ : CT → CT

kty₁ : (a : CT)
  → [ a ] ≡ t̂
  → [ ty₁ a ] ≡ ĉ

kty₁-a : (a : CT)
  → [ ty₁ a ] ≡ ĉ
  → [ a ] ≡ t̂

▷ : CT → CT → CT

k▷ : (γ a : CT)
  → [ γ ] ≡ ĉ
  → [ a ] ≡ t̂
  → ty₁ a ≡ γ
  → [ ▷ γ a ] ≡ ĉ

▷-γ : (γ a : CT)
  → [ ▷ γ a ] ≡ ĉ
  → [ γ ] ≡ ĉ

▷-a : (γ a : CT)
  → [ ▷ γ a ] ≡ ĉ
  → [ a ] ≡ t̂

▷-a₁ : (γ a : CT)
  → [ ▷ γ a ] ≡ ĉ
  → ty₁ a ≡ γ
```

There are analogous forward and inversion equations for `u`, `π`, and `σ`.

The morphisms preserve `[_]`, the tags, and `ty₁` unconditionally, but preserve
the other point operations only under their source validity assumptions. For
example:

```agda
Hom.▷ : (γ a : A.CT)
  → A.[ γ ] ≡ A.ĉ
  → A.[ a ] ≡ A.t̂
  → A.ty₁ a ≡ γ
  → θ (A.▷ γ a) ≡ B.▷ (θ γ) (θ a)
```

## The functors

There are functors

```text
F : W → D
G : D → W.
```

Given a weakly tagged algebra `A`, `F A` consists of well-kinded terms:

```agda
F A .Con = ΣP A.CT λ γ → A.[ γ ] ≡ A.ĉ
F A .Ty  = ΣP A.CT λ a → A.[ a ] ≡ A.t̂
```

Given a mutual projection algebra `A`, `G A` uses the following atoms:

```agda
data Atom : Set where
  con : A.Con → Atom
  ty  : A.Ty → Atom
  k̂ ĉ t̂ : Atom
```

Its carrier is the propositional lifting monad:

```agda
CT = Σ (P : Prop). P → Atom
```

A value `P ⊢ x` is defined under `P` and has value `x p : Atom` whenever
`p : P`. This is needed because the validity conditions of the point
operations contain equalities which are not decidable.

The operations of `G A` are partial computations. For instance,
`G A .▷ γ a` is defined exactly when `γ` and `a` are defined and their atoms
satisfy the context, type, and projection equations. When defined, its atom is
`con (...)`. Similarly `u`, `π`, and `σ` return type atoms when their validity
conditions hold:

```agda
▷₀ : (γ a : Atom) 
  → (kγ : [ γ ]₀ ≡ ĉ) 
  → (ka : [ a ]₀ ≡ t̂) 
  → ty₁₀ a ka ≡ γ 
  → Atom
▷₀ (con γ) (ty a) kγ ka a₁ =
  con (MA.▷ γ a (con-inj a₁))

▷ : CT → CT → CT
▷ γʰ aʰ =
  γʰ >>= λ γ →
  aʰ >>= λ a →
  assume ([ γ ]₀ ≡ ĉ) λ kγ →
  assume ([ a ]₀ ≡ t̂) λ ka →
  assume (ty₁₀ a ka ≡ γ) λ ka₁ →
  return (▷₀ γ a kγ ka ka₁)
```

There is a reltively straightforward counit isomorphism, however I doubt that the functors are actually adjoint, due to the junk in W.

```text
ε A : F (G A) ≅ A.
```

It extracts the context or type stored in a well-kinded inhabited atom. The
inverse sends a context or type to the corresponding always-defined atom.

## The desired transfer of initiality

Assume that `I` is an initial `W`-algebra. Let

```agda
FI = F I
GFI = G FI

ι : W.Hom I GFI
ι = rec GFI
```

To show that `F I` is initial in `D`, the central coherence result I need is
the triangle identity

```text
F₁ ι ∘ ε FI ≈ id.
```

Here the types are worth spelling out. We have

```text
                         F₁ ι
                 FI ------------> F(GFI)

                         ε FI
                 F(GFI) ---------> FI,
```

where `GFI = G(FI)`. Thus the displayed composite is the endomorphism

```text
F(GFI) -- ε FI --> FI -- F₁ ι --> F(GFI).
```

The counit map `ε FI` already has a separately constructed inverse
`ε⁻ FI : FI → F(GFI)`. Consequently it is enough to prove the equation above:
it identifies `F₁ ι` with `ε⁻ FI`. Indeed,

```text
F₁ ι
  ≈ F₁ ι ∘ id
  ≈ F₁ ι ∘ (ε FI ∘ ε⁻ FI)
  ≈ (F₁ ι ∘ ε FI) ∘ ε⁻ FI
  ≈ ε⁻ FI.
```

We then also obtain the opposite inverse equation

```text
ε FI ∘ F₁ ι ≈ idFI
```

from the corresponding inverse equation for `ε⁻ FI`. So although the
displayed equation is only one orientation of the triangle, it is sufficient
because `ε FI` is already known to be an isomorphism.

This is the coherence needed in the initiality argument. Define the proposed
recursor out of `FI` by

```text
recᴰ A = ε A ∘ F₁ (recᵂ (G A)) : FI → A.
```

Now take an arbitrary direct homomorphism

```text
f : FI → A.
```

Its image under `G`, composed with the initial map `ι`, gives

```text
G₁ f ∘ ι : I → G A.
```

By initiality of `I`, this must agree with the chosen recursor:

```text
G₁ f ∘ ι ≈ recᵂ (G A).
```

Applying `F` and composing with `ε A` gives

```text
ε A ∘ F₁ (G₁ f) ∘ F₁ ι
  ≈ ε A ∘ F₁ (recᵂ (G A))
  = recᴰ A.
```

Naturality of `ε : F ∘ G ⇒ Id` rewrites the left-hand side as

```text
f ∘ ε FI ∘ F₁ ι.
```

The triangle equation reduces this to `f`. Hence

```text
f ≈ recᴰ A,
```

which is exactly uniqueness of the homomorphism from `FI` to `A`.

Equivalently, one can view the whole argument as saying that `F₁ ι` must be
the canonical inverse of the counit at `FI`. Initiality of `I` supplies the
map `ι`; the difficult part is proving that this particular initial map is
indeed the inverse already suggested by the explicit equivalence
`F(G(FI)) ≅ FI`.

The essential content is a canonical-forms statement. For every well-kinded
term of `I`, `ι` should return the atom containing that same term and its kind
proof:

```agda
conβ : (kx : I.[ x ] ≡ I.ĉ)
  → ι.θ x ≡ return (GFI.con (x , kx))

tyβ : (kx : I.[ x ] ≡ I.t̂)
  → ι.θ x ≡ return (GFI.ty (x , kx))
```

I tried to prove this by section induction using the motive

```agda
record Beta (x : I.CT) : Set where
  field
    conβ : (kx : I.[ x ] ≡ I.ĉ)
      → ι.θ x ≡ return (GFI.con (x , kx))

    tyβ : (kx : I.[ x ] ≡ I.t̂)
      → ι.θ x ≡ return (GFI.ty (x , kx))
```

`Beta x` is a proposition, so all displayed equations are immediate by proof
irrelevance. The tag cases can be handled once and for all using no-confusion
for the atoms of `GFI`.

The valid branches of the point constructors also work. For example, in the
`conβ` branch for context extension we are given

```agda
k▷ : I.[ I.▷ γ a ] ≡ I.ĉ.
```

The inversion equations in `I` give

```agda
kγ : I.[ γ ] ≡ I.ĉ
ka : I.[ a ] ≡ I.t̂
a₁ : I.ty₁ a ≡ γ.
```

The induction hypotheses identify `ι.θ γ` and `ι.θ a` with their returned
context and type atoms. We can then apply `ι.▷` and compute `GFI.▷` on those
returned atoms. This proves the desired canonical context equation.

The corresponding valid branches for `u`, `π`, and `σ` work in the same way.

## The blocker

The opposite-kind branch for context extension appears circular. Its goal is

```agda
  (kx : I.[ I.▷ γ a ] ≡ I.t̂)
  → ι.θ (I.▷ γ a)
  ≡ return (GFI.ty (I.▷ γ a , kx)).
```

Transporting `kx` through the homomorphism gives

```agda
GFI.[ ι.θ (I.▷ γ a) ] ≡ GFI.tʰ,
```

so in particular `ι.θ (I.▷ γ a)` is defined. Intuitively, I would like to
argue that a defined `GFI.▷` must be a context atom, contradicting the type
kind equation.

However, what is defined is

```agda
ι.θ (I.▷ γ a),
```

not yet

```agda
GFI.▷ (ι.θ γ) (ι.θ a).
```

To transport definedness between these terms I need the homomorphism equation

```agda
ι.▷ γ a kγ ka a₁
  : ι.θ (I.▷ γ a) ≡ GFI.▷ (ι.θ γ) (ι.θ a).
```

But this equation itself requires the source validity proofs `kγ`, `ka`, and
`a₁`. The available inversion equations produce those proofs only from

```agda
I.[ I.▷ γ a ] ≡ I.ĉ,
```

which is exactly the kind equation available in the other branch, not this
one.

Thus the attempted argument loops:

```text
ι.θ (I.▷ γ a) is defined
  ⇒ need to identify it with GFI.▷ (ι.θ γ) (ι.θ a)
  ⇒ need the conditional homomorphism equation ι.▷
  ⇒ need source validity of γ and a
  ⇒ currently only obtainable from a context-kind proof for I.▷ γ a.
```

Simply inspecting

```agda
ι.θ (I.▷ γ a) ! definedness
```

only reveals an arbitrary `GFI.Atom`. Without `ι.▷`, I do not see how to
connect that atom to the implementation of `GFI.▷`.

There are symmetric blockers for the other point constructors:

```text
▷ : the type branch is blocked
u : the context branch is blocked
π : the context branch is blocked
σ : the context branch is blocked.
```

By contrast, the analogous argument works for `ty₁`, because morphisms
preserve `ty₁` unconditionally. Definedness of `GFI.ty₁ (ι.θ a)` exposes its
internal condition, from which one can recover that `ι.θ a` is a type and that
the result is a context atom. It also works for `∙`, whose preservation is
unconditional.

## Agda progress

Some helper combinators make the successful cases reasonably short:

```agda
conBeta :
  (ι.θ x ↓ → GFI.[ ι.θ x ] ≡ GFI.cʰ)
  → (∀ kx → extractedCon x kx ≡ (x , kx))
  → Beta x

tyBeta :
  (ι.θ x ↓ → GFI.[ ι.θ x ] ≡ GFI.tʰ)
  → (∀ kx → extractedTy x kx ≡ (x , kx))
  → Beta x
```

There is also an `absurdBeta` helper for tags and applications of `[_]`.
This factors out normalization in `PropLift`, proof irrelevance, and atom
no-confusion. It does not solve the mathematical issue above: for the blocked
constructors, the first argument of `conBeta` or `tyBeta` is precisely the
missing semantic classification.

At present the displayed algebra is complete except for the four
opposite-kind branches listed above. All of its equality fields are solved by
proof irrelevance of the motive Beta, and all valid point-constructor branches typecheck.

## Things I may be missing

I would be very interested in your view on any of the following.

1. Is there a way to obtain the source validity assumptions from semantic
   definedness using a stronger simultaneous displayed motive?

2. Should `Beta` be strengthened with additional logical-relations data, for
   example reflection of semantic definedness or a classification of the atom
   returned by `ι.θ x`? I experimented with adding constructor-specific
   inversion/no-confusion facts to the displayed motive, but this quickly
   becomes large and I have not found the right abstraction.

3. Is there a categorical proof of the triangle identity which avoids this
   pointwise canonical-forms induction?

4. Does the conditional notion of weakly tagged homomorphism leave invalid
   applications too unconstrained for the desired triangle identity to hold?
   In other words, is initiality in this category insufficient to establish
   canonical forms for terms which acquire an unexpected kind?

5. Would an essentially algebraic presentation in which validity witnesses
   are arguments to the point operations make the intended result easier,
   while still retaining the weakly tagged presentation I want?

I suspect there is either a standard gluing/logical-relations construction
which packages exactly the missing reflection property, or a subtle mismatch
between the intended algebraic theory and the category of models I have
defined. At this point I would rather check the setup than continue expanding
the displayed motive blindly.
