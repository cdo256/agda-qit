# Project Status Report - December 20, 2025

## Email Communication with Thorsten

**Date:** December 20, 2025
**Subject:** Progress Update on Higher Coinductive Types and Colimit Construction

Hi Thorsten,

I've had a look at those, thanks for sending them over, the idea looks really interesting, though I imagine there's a lot of challenges to making higher coinductive types work practically. Presumably the path constructors are still inductive?

## Current Progress Summary

I have been working in this repository implementing a colimit construction for setoid diagrams. The main achievements so far:

### ✅ Completed: Colimit Definition and Limiting Cocone

I've successfully defined the colimit using a sigma type construction with an equivalence relation:

```agda
-- The carrier of the colimit (Sigma type)
Colim₀ : Set (ℓI ⊔ ℓB)
Colim₀ = Σ[ i ∈ ⟨ I ⟩ ] ⟨ P̂ i ⟩

data _≈ˡ_ : Colim₀ → Colim₀ → Prop (ℓ≤ ⊔ ℓI ⊔ ℓB ⊔ ℓB') where
  ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ] → (i , x) ≈ˡ (i , x')
  ≈lstep  : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩) → (i , x) ≈ˡ (j , Pf p x)
  ≈lsym   : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
  ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u
```

Where `P` is the diagram over a setoid `I`. **I've proven that this is in fact a limiting cocone as expected, so I'm happy with this part.**

### 🚧 In Progress: Cocontinuity

I'm currently working on proving cocontinuity and have made progress on both directions:

#### Forward Direction (ϕ) - ✅ Completed
I've successfully proven congruence of the forward morphism:

```agda
ϕ₀ : ⟨ Colim (F̃ ∘ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (i , (l , _)) = l , (λ ())
ϕ₀ (i , (n , f)) = n , (λ b → i , f b)
```

#### Backward Direction (ψ) - ⚠️ Challenges
The backward direction is more challenging:

```agda
ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F̃ ∘ D) ⟩
ψ₀ (l , _) = sup (l , (λ ())) , l , (λ ())
ψ₀ (n , f) = sup (n , g) , (n , h)
  where
  g : B → ⟨ MobileSetoid ⟩
  g b = f b .proj₁
  h : B → ⟨ D.D-ob (node g) ⟩
  h b = sz (g b) gb<ng
    where
    gb<ng : g b < node g
    gb<ng = <sup b (≤refl (g b))
```

Note that `node g` is a pattern for `sup (n , g)` where `{n,l}` are atoms for the node/leaf shapes.

## Current Technical Challenges

### Unification Issues in Backward Congruence

The main blocker is proving backward (`ψ`) congruence. The issue is with unification nightmares when trying to show that equations for each branch position can propagate to the whole mobile:

```agda
ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ]
       → Colim (F̃ ∘ D) [ ψ₀ x ≈ ψ₀ y ]
-- easy cases omitted
-- snd≈ tells us that we have equality on each branch.
ψ-cong {n , f1} {n , f2} (mk≈ꟳ ≡.refl snd≈) =
  begin
  ψ₀ (n , f1)
    ≈⟨ C.refl ⟩
  sup (n , g1) , (n , h1)
    ≈⟨ {!!} ⟩  -- STUCK HERE
  sup (n , g2) , (n , h2)
    ≈⟨ C.refl ⟩
  ψ₀ (n , f2) ∎
```

**The Problem:** We can't pattern match on even a single `snd≈ b` because we haven't unified `g1` and `g2`, and I'm not sure what the best approach is to get past it.

### Potential Solutions Being Considered

1. **Redefining the colimit definition** to explicitly use an identity proof. Replacing `≈lstage` with:
   ```agda
   ≈lstage : ∀ {i j} (i I.≈ j) → {x x' : ⟨ P̂ i ⟩} → P̂ i [ x ≈ x' ] → P̂ j [ x ≈ x' ] → (i , x) ≈ˡ (j , x')
   ```
   This should avoid the unification issue, but I haven't had a chance to try it yet.

2. **HoTT Approach:** We can't create a path across `i` even with this without defining `≈ˡ` (limit paths) in the HoTT way as paths, so that we would be defining higher paths instead of setoids, which changes the entire construction.

### Mobile Tree Equivalence Structure

The homogeneity issue is also reflected in the mobile tree equivalence structure:

```agda
data _≈ᵗ_ : BTree → BTree → Prop l0 where
  ≈leaf : leaf ≈ᵗ leaf
  ≈node : ∀ {f g} → (c : ∀ b → f b ≈ᵗ g b)
        → node f ≈ᵗ node g
  ≈perm : ∀ {f} → (π : ≈.Iso Bˢ Bˢ)
        → node f ≈ᵗ node λ b → f (≈.Iso.⟦_⟧ π b)
  ≈trans : ∀ {s t u} → s ≈ᵗ t → t ≈ᵗ u → s ≈ᵗ u
```

## Next Steps

I do want to go through what I've done so far with you at some point just to check I haven't made an obvious mistake, but I think I'm mostly on track.

The immediate priorities are:
1. Resolve the unification issues in backward congruence
2. Complete the cocontinuity proof
3. Potentially explore the HoTT/cubical approach if setoid approach proves too limiting

## Repository State

### Recent Commits
- `c1327ce` - wip (current HEAD)
- `3c54881` - wip paper building system
- `8d3be5e` - Fix flake
- `f27da9e` - Simplify build process
- `cbc6bad` - wip: Add dissertation files

### Modified Files
- `Cocontinuity.agda` - Definition of cocontinuity for arbitrary functors
- `Colimit.agda` - Main colimit definitions
- `Mobile.agda` - Mobile/tree structures
- Various LaTeX files cleaned up

### Key Modules
- **`Colimit.agda`** - Diagram a colimit construction over setoid diagrams
- **`Cocontinuity.agda`** - Functor composition cocontinuity definition.
- **`Mobile.agda`** - Mobile/tree definition. All constructions of mobiles are here.
- **`Setoid/{Base,Hom,Iso,Functor}.agda`** - Setoid definitions.
- **`ContainerFunctor.agda`** - Container functor definitions for generic containers.

The project is well-structured with a clear separation between the mathematical development and the paper writing infrastructure. The main mathematical content is solid, with the primary challenge being the technical unification issues in the cocontinuity proofs.

---

**Status:** Making good progress on the core mathematical development. The colimit construction is complete and proven correct. The main blocker is technical challenges in the cocontinuity proof that may require either clever unification tricks or a shift to a cubical/HoTT approach.
