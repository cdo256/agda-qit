open import QIT.Prelude

module QIT.Mobile.Cocontinuity
  (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓ0 (lsuc ℓ0)
open import QIT.QW.Cocontinuity ≤p
open import QIT.QW.Stage sig

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

module F = ≈.Functor F
module D = Diagram D
module F∘D = Diagram (F ∘ᴰ D)

private
  L = Colim (F ∘ᴰ D)
  R = F.F-ob (Colim D)

ϕ₀ : ⟨ Colim (F ∘ᴰ D) ⟩ → ⟨ F.F-ob (Colim D) ⟩
ϕ₀ (α , (l , _)) = l , (λ ())
ϕ₀ (α , (n , f)) = n , (λ b → α , f b)

ϕ-cong-stage : ∀ α {x y} → F∘D.D-ob α [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ (α , x) ≈ ϕ₀ (α , y) ]
ϕ-cong-stage α {l , f} {l , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl λ()
ϕ-cong-stage α {n , f} {n , g} (mk≈ꟳ ≡.refl snd≈) =
  mk≈ꟳ ≡.refl q
  where
  q : (i : I) → Colim D [ α , f i ≈ α , g i ]
  q i = ≈lstage α u
    where
    u :  α ⊢ f i ≈ᵇ g i
    u = snd≈ i

ϕ-cong : ∀ {x y} → Colim (F ∘ᴰ D) [ x ≈ y ] → F.F-ob (Colim D) [ ϕ₀ x ≈ ϕ₀ y ]
ϕ-cong (≈lstage α e) = ϕ-cong-stage α e
ϕ-cong (≈lstep {α} {j} p (l , _)) = mk≈ꟳ ≡.refl λ()
ϕ-cong (≈lstep {α} {j} (sup≤ p) (n , f)) =
  mk≈ꟳ ≡.refl λ k → ≈lstep (sup≤ p) (f k)
ϕ-cong (≈lsym p) = ≈fsym (Colim D) (ϕ-cong p)
ϕ-cong (≈ltrans p q) = ≈ftrans (Colim D) (ϕ-cong p) (ϕ-cong q)

node≢leaf : ∀ {f g} → _≡_ {A = T} (sup (n , f)) (sup (l , g)) → ⊥p
node≢leaf ()

n≢l : n ≡p l → ⊥p
n≢l ∣ () ∣

shape : T → Sᵀ
shape (sup (s , _)) = s

shape-preserved : ∀ α s t → α ⊢ s ≈ᵇ t → shape (s .fst) ≡p shape (t .fst)
shape-preserved α s t (≈pcong a μ f g r) = reflp
shape-preserved α s t (≈psat e ϕ l≤α r≤α) = reflp
shape-preserved α s t ≈prefl = reflp
shape-preserved α s t (≈psym s≈t) = symp (shape-preserved α t s s≈t)
shape-preserved α s t (≈ptrans {t̂ = u} s≈u u≈t) =
  transp (shape-preserved α s u s≈u) (shape-preserved α u t u≈t)
shape-preserved α s t (≈pweaken α≤β s≈t) = shape-preserved _ _ _ s≈t

node≉ᵇleaf : ∀ α {f g} s t → sup (n , f) ≡ s .fst → sup (l , g) ≡ t .fst → α ⊢ s ≈ᵇ t → ⊥p
node≉ᵇleaf α s t f̂≡s ĝ≡t s≈t = n≢l (substp₂ (λ s t → shape s ≡p shape t) (≡.sym f̂≡s) (≡.sym ĝ≡t)
                                            (shape-preserved α s t s≈t))


-- Fully inductive stage proofs, following the pattern  of the data.
infixl 3 _⊢_≈ˢ_
data _⊢_≈ˢ_ : (α : Z) → D₀ α → D₀ α → Prop ℓ0 where
  ≈sleaf : ∀ {α} → α ⊢ sup (l , λ()) , sup≤ (λ()) ≈ˢ sup (l , λ()) , sup≤ (λ())
  ≈snode : ∀ {α : Z} (μ : I → Z)
         → (μi<α : ∀ i → μ i < α)
         → (f g : I → T)
         → (π : I ↔ I)
         → (fi≤μi : ∀ i → f i ≤ᵀ μ i)
         → (gπi≤μi : ∀ i → g (π .↔.to i) ≤ᵀ μ i)
         → (fi≈gπi : ∀ i → μ i ⊢ f i , fi≤μi i ≈ˢ g (π .↔.to i) , gπi≤μi i)
         → α ⊢  (sup (n , f)) , ≤≤ (sup≤ μi<α) (sup≤sup fi≤μi)
             ≈ˢ (sup (n , g)) , ≤≤ (sup≤ λ i → μi<α (π .↔.from i))
                  (sup≤sup λ i → substp (λ ○ → g ○ ≤ᵀ μ (π .↔.from i)) (π .↔.linv i) (gπi≤μi (π .↔.from i)))

≈ᵇ→≈ˢ : (α : Z) → (ŝ t̂ : D₀ α) → α ⊢ ŝ ≈ᵇ t̂ → α ⊢ ŝ ≈ˢ t̂
≈ᵇ→≈ˢ α (sup (l , f) , s≤α) (sup (n , g) , t≤α) ŝ≈t̂ = absurdp {!shape-preserved!}
≈ᵇ→≈ˢ α (sup (n , f) , s≤α) (sup (l , g) , t≤α) ŝ≈t̂ = {!!}
≈ᵇ→≈ˢ α (sup (l , f) , s≤α) (sup (l , g) , t≤α) ŝ≈t̂ = {!!}
≈ᵇ→≈ˢ α (sup (n , f) , s≤α) (sup (n , g) , t≤α) ŝ≈t̂ = {!!}

strengthen : ∀ {α β} (β≤α : β ≤ α) (s t : T) (s≤β : s ≤ᵀ β) (t≤β : t ≤ᵀ β)
           → α ⊢ s , ≤≤ β≤α s≤β ≈ᵇ t , ≤≤ β≤α t≤β
           → β ⊢ s , s≤β ≈ᵇ t , t≤β
strengthen {α} {β} β≤α s t s≤β t≤β (≈pcong a μ f g r) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈psat e ϕ l≤α r≤α) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β ≈prefl = ≈prefl
strengthen {α} {β} β≤α s t s≤β t≤β (≈psym p) = ≈psym (strengthen β≤α t s t≤β s≤β p)
strengthen {α} {β} β≤α s t s≤β t≤β (≈ptrans {t̂ = u , u≤α} p q) =
  ≈ptrans (strengthen β≤α s u s≤β {!u≤β!} p) {!!}
-- strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α p) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α (≈pcong a μ f g r)) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α (≈psat e ϕ l≤α r≤α)) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α ≈prefl) = ≈prefl
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α (≈psym p)) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α (≈ptrans p p₁)) = {!!}
strengthen {α} {β} β≤α s t s≤β t≤β (≈pweaken {α = γ} {β = α} γ≤α (≈pweaken α≤β p)) = {!!}
  -- ≈pweaken (≤≤ {!!} {!!}) (strengthen {!!} s t {!!} {!!} p)
           

enweaken : ∀ {α β γ} (α≤γ : α ≤ γ) (β≤γ : β ≤ γ) (ŝ : D₀ α) (t̂ : D₀ β)
         → γ ⊢ pweaken α≤γ ŝ ≈ᵇ pweaken β≤γ t̂
         → (α ∨ᶻ β) ⊢ pweaken ∨ᶻ-l ŝ ≈ᵇ pweaken ∨ᶻ-r t̂
enweaken {α} {β} {γ} α≤γ β≤γ ŝ t̂ p = h α≤γ β≤γ ŝ t̂ a≡b p
  where
  a≡b : shape (ŝ .fst) ≡p shape (t̂ .fst) 
  a≡b = shape-preserved γ (pweaken α≤γ ŝ) (pweaken β≤γ t̂) p
  h : ∀ {α β γ} (α≤γ : α ≤ γ) (β≤γ : β ≤ γ) (ŝ : D₀ α) (t̂ : D₀ β)
    → shape (ŝ .fst) ≡p shape (t̂ .fst)
    → γ ⊢ pweaken α≤γ ŝ ≈ᵇ pweaken β≤γ t̂
    → (α ∨ᶻ β) ⊢ pweaken ∨ᶻ-l ŝ ≈ᵇ pweaken ∨ᶻ-r t̂
  h {α} {β} {γ} α≤γ β≤γ (sup (l , f) , af≤α) (sup (l , g) , bg≤β) reflp s≈t =
    substp (λ ○ → α ∨ᶻ β ⊢ v̂ ≈ᵇ ○) (ΣP≡ v̂ (sup (l , g) , _) q) ≈prefl
    where
    q = leaf≡leaf f g
    v̂ = sup (l , f) , ≤≤ ∨ᶻ-l af≤α 
  h {α} {β} {γ} α≤γ β≤γ (sup (n , f) , af≤α) (sup (n , g) , bg≤β) reflp (≈pcong n μ f' g' r) =
    ≈pweaken (≤≤ ∨ᶻ-l af≤α) (≈pcong n {!!} {!!} {!!} {!!})
    where
    μ̂ : I → Z
    f̂ : ∀ i → D₀ {!!}
    ĝ : ∀ i → D₀ {!!}
  h {α} {β} {γ} α≤γ β≤γ (sup (n , f) , af≤α) (sup (n , g) , bg≤β) reflp (≈psat e ϕ l≤α r≤α) = {!!}
  h {α} {β} {γ} α≤γ β≤γ (sup (n , f) , af≤α) (sup (n , g) , bg≤β) reflp ≈prefl = ≈prefl
  h {α} {β} {γ} α≤γ β≤γ ŝ@(sup (n , f) , af≤α) t̂@(sup (n , g) , bg≤β) reflp (≈psym t≈s) =
    {!!}
    where
    u : γ ⊢ pweaken α≤γ ŝ ≈ᵇ pweaken β≤γ t̂
    u = ≈psym t≈s
  h {α} {β} {γ} α≤γ β≤γ (sup (n , f) , af≤α) (sup (n , g) , bg≤β) reflp (≈ptrans s≈t s≈t₁) = {!!}
  h {α} {β} {γ} α≤γ β≤γ (sup (n , f) , af≤α) (sup (n , g) , bg≤β) reflp (≈pweaken α≤β s≈t) = {!!}

ψ₀ : ⟨ F.F-ob (Colim D) ⟩ → ⟨ Colim (F ∘ᴰ D) ⟩
ψ₀ (l , _) = ⊥ᶻ , l , λ()
ψ₀ (n , f) = α , n , g
  where
  μ : I → Z
  μ i = f i .proj₁
  α : Z
  α = sup (ιˢ n , μ)
  h : (i : I) → D₀ (μ i)
  h i = f i .proj₂
  g : I → D₀ α
  g i = pweaken (child≤ (ιˢ n) μ i) (h i)

record Bounded≈ (s t : T) : Set (lsuc ℓ0) where
  constructor mkBounded≈
  field
    γ : Z
    s≤γ : s ≤ᵀ γ
    t≤γ : t ≤ᵀ γ
    s≈t : γ ⊢ (s , s≤γ) ≈ᵇ (t , t≤γ)

ψ-cong : ∀ {x y} → F.F-ob (Colim D) [ x ≈ y ] → Colim (F ∘ᴰ D) [ ψ₀ x ≈ ψ₀ y ]
ψ-cong {l , f} {l , g} (mk≈ꟳ ≡.refl snd≈) = ≈lrefl (F ∘ᴰ D)
ψ-cong {n , f} {n , g} (mk≈ꟳ ≡.refl snd≈) = begin
  ψ₀ (n , f)
    ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
  (αf , n , λ i → tf i , _)
    ≈⟨ ≈lstep ∨ᶻ-l (n , _) ⟩
  (αf ∨ᶻ αg , n , λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ _) (fi≤μi i)))
    ≈⟨ ≈lstage (αf ∨ᶻ αg) inner ⟩
  (αf ∨ᶻ αg , n , λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ _) (gi≤μi i)))
    ≈⟨ ≈lsym (≈lstep ∨ᶻ-r (n , _)) ⟩
  (αg , n , λ i → tg i , _)
    ≈⟨ ≈lrefl (F ∘ᴰ D) ⟩
  ψ₀ (n , g) ∎
  where
  μf : I → Z
  μf i = f i .proj₁
  μg : I → Z
  μg i = g i .proj₁
  αf = sup (ιˢ n , μf)
  αg = sup (ιˢ n , μg)
  α = αf ∨ᶻ αg
  tf : I → T
  tf i = f i .proj₂ .fst
  tg : I → T
  tg i = g i .proj₂ .fst
  fi≤μi : ∀ i → tf i ≤ᵀ μf i
  fi≤μi i = f i .proj₂ .snd
  gi≤μi : ∀ i → tg i ≤ᵀ μg i
  gi≤μi i = g i .proj₂ .snd
  inner : F.F-ob (D.D-ob α) [ n , (λ i → tf i , ≤≤ ∨ᶻ-l (≤≤ (child≤ _ _ i) (fi≤μi i)))
                            ≈ n , (λ i → tg i , ≤≤ ∨ᶻ-r (≤≤ (child≤ _ _ i) (gi≤μi i))) ]
  inner = mk≈ꟳ ≡.refl λ i → v i (u i (snd≈ i))
    where
    v : ∀ i → ∥ Bounded≈ (tf i) (tg i) ∥ → α ⊢ (tf i  , _) ≈ᵇ (tg i , _) 
    v i ∣ mkBounded≈ (sup (αs , μ)) s≤γ t≤γ s≈t ∣ = {!!}
    u : ∀ i → Colim D [ f i ≈ g i ] → ∥ Bounded≈ (tf i) (tg i) ∥ 
    u i x = r (snd≈ i)
      where
      C : ∀ {s t} → Colim D [ s ≈ t ] → Prop (lsuc ℓ0)
      C {α , s , s≤α} {β , t , t≤β} p = ∥ Bounded≈ s t ∥
      c-stage : ∀ α {s t} (e : α ⊢ s ≈ᵇ t) → C (≈lstage α e)
      c-stage α {s} {t} e = ∣ record { γ = α ; s≤γ = s .snd ; t≤γ = t .snd ; s≈t = e } ∣
      c-step : ∀ {α β} (p : α ≤ β) (x : D₀ α) → C (≈lstep p x)
      c-step {α} {β} p (t , t≤α) = ∣ mkBounded≈ α t≤α t≤α ≈prefl ∣
      c-sym : ∀ {s t} → (p : Colim D [ s ≈ t ]) → C p → C (≈lsym p)
      c-sym _ ∣ mkBounded≈ γ s≤γ t≤γ s≈t ∣ =
        ∣ (mkBounded≈ γ t≤γ s≤γ (≈psym s≈t)) ∣
      c-trans : ∀ {s t u} → (p : Colim D [ s ≈ t ]) → (q : Colim D [ t ≈ u ])
              → C p → C q → C (≈ltrans p q)
      c-trans {_ , s} {_ , t} {_ , u} _ _
        ∣ mkBounded≈ α s≤α t≤α s≈t ∣
        ∣ mkBounded≈ β t≤β u≤β t≈u ∣ =
          ∣ (mkBounded≈ (α ∨ᶻ β) (≤≤ ∨ᶻ-l s≤α) (≤≤ ∨ᶻ-r u≤β) s≈ᵇu) ∣
        where
        s≈ᵇu : (α ∨ᶻ β) ⊢ (s .fst , ≤≤ ∨ᶻ-l s≤α) ≈ᵇ (u .fst , ≤≤ ∨ᶻ-r u≤β)
        s≈ᵇu = ≈ptrans (≈pweaken ∨ᶻ-l s≈t) (≈pweaken ∨ᶻ-r t≈u)
      r : ∀ {s t} → (a : Colim D [ s ≈ t ]) → C a
      r = recˡ D C c-stage c-step c-sym c-trans
  open ≈.Hom
  open Setoid (Colim (F ∘ᴰ D))
  open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

-- ψ-cong ≈leaf = ≈lstage ⊥ᶻ ≈leaf
-- ψ-cong (≈node {f} {g} c) = begin
--   nf , n , (λ i → pweaken (sup≤ (λ x → <sup x (f x .proj₂ .snd))) {!!})
--     ≈⟨ {!!} ⟩
--   ng , {!!} ∎
--   where
--   nf : Z
--   nf = sup (ιˢ n , λ i → f i .proj₁)
--   ng : Z
--   ng = sup (ιˢ n , λ i → g i .proj₁)
--   open ≈.Hom
--   open Setoid (Colim (F ∘ᴰ D))
--   open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

-- ψ-cong {x} {y} (≈perm π) = {!!}
-- ψ-cong {x} {y} (≈trans x≈y x≈y₁) = {!!}

-- ψ-cong ≈leaf = ≈lstage 𝟘 ≈leaf
-- ψ-cong (≈node {f} {g} c) = {!begin
--   nf , (n , λ b → weaken (f1 b) nf (fi≤sup n f1 b) (f2 b))
--     ≈⟨ ≈lstep (∨ᵗ-l nf ng) u ⟩
--   nf ∨ᵗ ng , (n , λ b → weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b)))
--     ≈⟨ ≈lstage (nf ∨ᵗ ng) (≈node c') ⟩
--   nf ∨ᵗ ng , (n , λ b → weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)))
--     ≈⟨ ≈lsym (≈lstep (∨ᵗ-r nf ng) (n , (λ b → weaken (g1 b) ng _ (g2 b)))) ⟩
--   ng , (n , λ b → weaken (g1 b) ng (fi≤sup n g1 b) (g2 b)) ∎!}
-- ψ-cong (≈node {f} {g} c) = begin
--   α1 , n , h1
--     ≈⟨ ≈lstep {!!} (n , h1) ⟩
--   {!!} , n , {!!}
--     ≈⟨ {!!} ⟩
--   α2 , n , h2 ∎
--   where
--   open Diagram D
--   f1 : I → Z
--   f1 i = f i .proj₁
--   g1 : ∀ i → P₀ (f1 i)
--   g1 i = f i .proj₂
--   α1 : Z
--   α1 = sup (ιˢ n , f1)
--   h1 : I → P₀ α1
--   h1 i = pweaken (child≤ (ιˢ n) f1 i) (g1 i)
--   f2 : I → Z
--   f2 i = g i .proj₁
--   g2 : ∀ i → P₀ (f2 i)
--   g2 i = g i .proj₂
--   α2 : Z
--   α2 = sup (ιˢ n , f2)
--   h2 : I → P₀ α2
--   h2 i = pweaken (child≤ (ιˢ n) f2 i) (g2 i)
--   t1 : T
--   t1 = sup (n , (λ i → g1 i .fst))
--   t2 : T
--   t2 = sup (n , (λ i → g1 i .fst))
--   d : ∀ {s t} → Colim D [ s ≈ t ] → (s .proj₂ .fst) ≈ᴾᴵ (t .proj₂ .fst)
--   d r = recˡ D C c-stage c-step c-sym c-trans r
--     where
--     C : ∀ {s t} → Colim D [ s ≈ t ] → Prop
--     C {_ , s , _} {_ , t , _} p = s  ≈ᴾᴵ t
--     c-stage : ∀ α {x x'} (e : P α [ x ≈ x' ]) → C (≈lstage α e)
--     c-stage α {x} {x'} e = mkPI α (x .snd) (x' .snd) e
--     c-step : ∀ {α β} (p : α ≤ β) (x : ⟨ P α ⟩) → C (≈lstep p x)
--     c-step {α} {β} α≤β (s , s≤α) = mkPI β (≤≤ α≤β s≤α) (≤≤ α≤β s≤α) ≈prefl
--     c-sym : ∀ {s t} (r : Colim D [ s ≈ t ]) → C r → C (≈lsym r)
--     c-sym _ p = ≈pisym p
--     c-trans : ∀ {s t u} (r₁ : Colim D [ s ≈ t ]) (r₂ : Colim D [ t ≈ u ]) → C r₁ → C r₂ → C (≈ltrans r₁ r₂)
--     c-trans _ _ p q = ≈pitrans p q
--   β : t1 ≈ᴾᴵ t2 → Colim (F ∘ᴰ D) [ α1 , n , h1 ≈ α2 , n , h2 ]
--   β (mkPI α s≤α t≤α e) = begin
--     α1 , n , h1
--       ≈⟨ ≈lstep (≤≤ ∨ᶻ-r ∨ᶻ-l) (n , h1) ⟩
--     α ∨ᶻ (α1 ∨ᶻ α2) , n , (λ b → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (h1 b))
--       ≈⟨ ≈lstage _ u ⟩
--     α ∨ᶻ (α1 ∨ᶻ α2) , n , (λ b → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (h2 b))
--       ≈⟨ ≈lsym (≈lstep (≤≤ ∨ᶻ-r ∨ᶻ-r) (n , h2)) ⟩
--     α2 , n , h2 ∎
--     where
--     v' : ∀ γ1 γ2 γ (p : γ1 ≤ γ) (q : γ2 ≤ γ) {s : P₀ γ1} {t : P₀ γ2}
--        → Colim D [ γ1 , s ≈ γ2 , t ]
--        → γ ⊢ pweaken p s ≈ᴾ pweaken q t
--     v' γ1 .γ1 γ p .p (≈lstage .γ1 r) = ≈pweaken p r
--     v' γ1 γ2 γ p q (≈lstep γ1≤γ2 x) = ≈prefl
--     v' γ1 γ2 γ p q (≈lsym r) = ≈psym (v' γ2 γ1 γ q p r)
--     v' γ1 γ2 γ p q (≈ltrans {t = t} r s) = ≈ptrans {!!} {!!}
--     v : ∀ i → Colim D [ f i ≈ g i ]
--       → (α ∨ᶻ (α1 ∨ᶻ α2)) ⊢  pweaken (≤≤ (≤≤ ∨ᶻ-r ∨ᶻ-l) (child≤ _ f1 i)) (f i .proj₂)
--                           ≈ᴾ pweaken (≤≤ (≤≤ ∨ᶻ-r ∨ᶻ-r) (child≤ _ f2 i)) (g i .proj₂)
--     v i = recˡ D {!!} {!!} {!!} {!!} {!!}
--       where
--       C : ∀ {s t} (p : Colim D [ s ≈ t ]) → {!α ∨ᶻ (α1 ∨ᶻ α2) ⊢ ? ≈ᴾ ?!}
--     u : F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2)) [
--          n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (h1 i)) ≈
--          n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (h2 i)) ]
--     u = begin
--       n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-l) (pweaken (child≤ _ f1 i) (f i .proj₂)))
--         ≈⟨ ≈node (λ i → v i (c i)) ⟩
--       n , (λ i → pweaken (≤≤ ∨ᶻ-r ∨ᶻ-r) (pweaken (child≤ _ f2 i) (g i .proj₂))) ∎
--       where
--       open Setoid (F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2)))
--       open ≈.≈syntax {S = F∘D.D-ob (α ∨ᶻ (α1 ∨ᶻ α2))}
--     open ≈.Hom
--     open Setoid (Colim (F ∘ᴰ D))
--     open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
    
-- --   c' : ∀ b → P (nf ∨ᵗ ng) [ weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b))
-- --                           ≈ weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ]
-- --   c' b = begin
-- --     weaken nf (nf ∨ᵗ ng) _ (weaken (f1 b) nf _ (f2 b))
-- --       ≈⟨ ≈psym (≈pweaken (∨ᵗ-l nf ng) (weaken (f1 b) nf _ (f2 b))) ⟩
-- --     weaken (f1 b) nf _ (f2 b)
-- --       ≈⟨ ≈psym (≈pweaken (child≤ n f1 b) (f2 b)) ⟩
-- --     f2 b
-- --       ≈⟨ d b (c b) ⟩
-- --     g2 b
-- --       ≈⟨ ≈pweaken (child≤ n g1 b) (g2 b) ⟩
-- --     weaken (g1 b) ng _ (g2 b)
-- --       ≈⟨ ≈pweaken (∨ᵗ-r nf ng) (weaken (g1 b) ng _ (g2 b)) ⟩
-- --     weaken ng (nf ∨ᵗ ng) _ (weaken (g1 b) ng _ (g2 b)) ∎
-- --     where
-- --     import QIT.Setoid.Indexed as Indexed
-- --     open Indexed.≈syntax Pᴵ
--   open ≈.Hom
--   open Setoid (Colim (F ∘ᴰ D))
--   open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
-- --   u : ⟨ F∘ᴰD.D-ob nf ⟩
-- --   u = n , (λ b → weaken (f1 b) nf _ (f2 b))
-- -- -- ψ-cong (≈perm {f} π) = u
-- -- --   where
-- -- --   π' : I → I
-- -- --   π' = π .↔.to
-- -- --   g : I → P₀ (sup (n , (λ b → f b .proj₁)))
-- -- --   g b = weaken (f b .proj₁) (sup (n , (λ b → f b .proj₁)))
-- -- --                (child≤ n _ b) (f b .proj₂)
-- -- --   h : I → P₀ (sup (n , (λ b → f (π' b) .proj₁)))
-- -- --   h b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f (π' b) .proj₁)))
-- -- --                 (child≤ n _ b) (f (π' b) .proj₂)
-- -- --   g' : I → P₀ (sup (n , (λ b → f b .proj₁)))
-- -- --   g' b = weaken (f (π' b) .proj₁) (sup (n , (λ b → f b .proj₁)))
-- -- --                 (child≤ n _ (π' b)) (f (π' b) .proj₂)
-- -- --   le : sup (n , λ b → f b .proj₁) ≤ sup (n , λ b → f (π' b) .proj₁)
-- -- --   le = sup≤ λ b → <sup (π .↔.from b)
-- -- --     (substp (λ ○ → f b .proj₁ ≤ f ○ .proj₁) (≡.sym (↔.linv π b)) (≤refl (f b .proj₁)))
-- -- --   u : Colim (F ∘ᴰ D)
-- -- --     [ sup (n , λ b → f b .proj₁) , (n , g)
-- -- --     ≈ sup (n , λ b → f (π' b) .proj₁) , (n , h) ]
-- -- --   u = begin
-- -- --     sup (n , (λ b → f b .proj₁)) , (n , g)
-- -- --       ≈⟨ ≈lstage (sup (n , (λ b → f b .proj₁))) (≈perm π) ⟩
-- -- --     sup (n , (λ b → f b .proj₁)) , (n , g')
-- -- --       ≈⟨ ≈lstep le (n , g') ⟩
-- -- --     sup (n , (λ b → f (π' b) .proj₁)) , (n , λ b → weaken _ _ le (g' b))
-- -- --       ≈⟨ ≈lstage _ (≈node v) ⟩
-- -- --     sup (n , (λ b → f (π' b) .proj₁)) , (n , h) ∎
-- -- --     where
-- -- --     v : ∀ b → weaken _ _ le (g' b) ≈ᴾ h b
-- -- --     v b = begin
-- -- --       weaken _ _ le (g' b)
-- -- --         ≈⟨ ≈psym (≈pweaken le (g' b)) ⟩
-- -- --       g' b
-- -- --         ≈⟨ ≈psym (≈pweaken (child≤ n (λ b₃ → f b₃ .proj₁) (π' b)) (f (π' b) .proj₂)) ⟩
-- -- --       f (π' b) .proj₂
-- -- --         ≈⟨ (≈pweaken (child≤ n (λ b₃ → f (π' b₃) .proj₁) b) (f (π' b) .proj₂)) ⟩
-- -- --       h b ∎
-- -- --       where
-- -- --       import QIT.Setoid.Indexed as Indexed
-- -- --       open Indexed.≈syntax Pᴵ
-- -- --     open Setoid (Colim (F ∘ᴰ D))
-- -- --     open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
-- -- --   open ≈.Hom
-- -- --   open Setoid (Colim (F ∘ᴰ D))
-- -- --   open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
-- -- -- ψ-cong (≈trans p q) = ≈ltrans (ψ-cong p) (ψ-cong q)

-- -- -- linv : ∀ y → F.F-ob (Colim D) [ (ϕ₀ (ψ₀ y)) ≈ y ]
-- -- -- linv (l , f) = begin
-- -- --   ϕ₀ (ψ₀ (l , f))
-- -- --     ≈⟨ refl ⟩
-- -- --   (l , λ ())
-- -- --     ≈⟨ ≈leaf ⟩
-- -- --   (l , f) ∎
-- -- --   where
-- -- --     open ≈.≈syntax {S = (F.F-ob (Colim D))}
-- -- --     open Setoid (F.F-ob (Colim D))
-- -- -- linv (n , g) =
-- -- --   ϕ₀ (ψ₀ (n , g))
-- -- --     ≈⟨ refl ⟩
-- -- --   (n , λ b → t* , weaken (t b) t* _ (f b))
-- -- --     ≈⟨ ≈node (λ b → ≈lsym (≈lstep (child≤ n t b) (f b))) ⟩
-- -- --   (n , λ b → t b , f b)
-- -- --     ≈⟨ refl ⟩
-- -- --   (n , g) ∎
-- -- --   where
-- -- --   open Setoid (F.F-ob (Colim D))
-- -- --   open Diagram D
-- -- --   t : I → BTree
-- -- --   t b = g b .proj₁
-- -- --   f : ∀ b → P₀ (t b)
-- -- --   f b = g b .proj₂
-- -- --   t* : BTree
-- -- --   t* = sup (n , t)
-- -- --   --   open ≈.Hom
-- -- --   open ≈.≈syntax {S = (F.F-ob (Colim D))}

-- -- -- rinv : ∀ x → Colim (F ∘ᴰ D) [ (ψ₀ (ϕ₀ x)) ≈ x ]
-- -- -- rinv (i , (l , f)) = begin
-- -- --   ψ₀ (ϕ₀ (i , (l , f)))
-- -- --     ≈⟨ refl ⟩
-- -- --   ψ₀ (l , g)
-- -- --     ≈⟨ ≈lstage 𝟘 ≈leaf ⟩
-- -- --   𝟘 , (l , h)
-- -- --     ≈⟨ ≈lstep (𝟘≤t i) (l , h) ⟩
-- -- --   i , (l , λ b → weaken 𝟘 i (𝟘≤t i) (h b))
-- -- --     ≈⟨ ≡→≈ (Colim (F ∘ᴰ D)) (≡.cong (λ ○ → i , (l , ○)) (funExt (λ ()))) ⟩
-- -- --   i , (l , f) ∎
-- -- --   where
-- -- --   open Setoid (Colim (F ∘ᴰ D))
-- -- --   open ≈.≈syntax {S = Colim (F ∘ᴰ D)}
-- -- --   g : ⊥* → ⟨ Colim D ⟩
-- -- --   g ()
-- -- --   h : ⊥* → ⟨ D.D-ob 𝟘 ⟩
-- -- --   h ()
-- -- -- rinv (i , (n , g)) = begin
-- -- --   ψ₀ (ϕ₀ (i , (n , g)))
-- -- --     ≈⟨ refl ⟩
-- -- --   ψ₀ (n , (λ b → i , g b))
-- -- --     ≈⟨ refl ⟩
-- -- --   suc i , n , (λ b → weaken i (suc i) (<→≤ (<suc i)) (g b))
-- -- --     ≈⟨ ≈lsym (≈lstep (<→≤ (<suc i)) (n , g)) ⟩
-- -- --   i , (n , g) ∎
-- -- --   where
-- -- --   open Setoid (Colim (F ∘ᴰ D))
-- -- --   open ≈.≈syntax {S = Colim (F ∘ᴰ D)}

-- -- -- cocontinuous : Cocontinuous F D
-- -- -- cocontinuous = ∣ iso ∣
-- -- --   where
-- -- --   iso : ≈.Iso (Colim (F ∘ᴰ D)) (F.F-ob (Colim D))
-- -- --   iso = record
-- -- --     { ⟦_⟧ = ϕ₀
-- -- --     ; ⟦_⟧⁻¹ = ψ₀
-- -- --     ; cong = ϕ-cong
-- -- --     ; cong⁻¹ = ψ-cong
-- -- --     ; linv = linv
-- -- --     ; rinv = rinv
-- -- --     }
