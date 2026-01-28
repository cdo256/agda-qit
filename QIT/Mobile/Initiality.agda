{-# OPTIONS --type-in-type #-}
open import QIT.Prelude

module QIT.Mobile.Initiality
  (I : Set) (inhabI : ∥ I ∥) where

open import QIT.Relation.Binary
open import QIT.Relation.Subset
open import QIT.Mobile.Base I
open import QIT.Mobile.Cocontinuity I inhabI
open import QIT.Setoid as ≈
open import QIT.Container.Base
open import QIT.Relation.Plump Sᵀ Pᵀ
open import QIT.Setoid.Diagram ≤p

open import QIT.QW.Colimit ≤p ℓ0 (lsuc ℓ0) hiding (_≈ˡ_)
open import QIT.QW.Cocontinuity ≤p
open import QIT.QW.Stage sig
open import QIT.QW.Algebra sig
open import QIT.QW.StageColimit sig using (joinTerms; αˡ; tˡ; t≤αˡ)
open import QIT.QW.Equation Sᵀ Pᵀ
open import QIT.QW.W Sᵀ Pᵀ hiding (T)

open import QIT.QW.Signature
open Sig sig

open import QIT.Container.Functor Sᵀ Pᵀ ℓ0 (lsuc ℓ0)

open F-Ob

ϕ : ≈.Hom (Colim (F ∘ᴰ D)) (F.F-ob (Colim D))
ϕ = record { to = ϕ₀ ; cong = ϕ-cong }
ψ : ≈.Hom (F.F-ob (Colim D)) (Colim (F ∘ᴰ D))
ψ = record { to = ψ₀ ; cong = ψ-cong }

θ₀ : ⟨ Colim (F ∘ᴰ D) ⟩ → ⟨ Colim D ⟩
θ₀ (α , a , f) = β , t , t≤β
  module θ where
  β : Z
  β = sup (ιˢ a , λ _ → α)
  t : T
  t = sup (a , λ i → f i .fst)
  t≤β : t ≤ᵀ β
  t≤β = sup≤sup λ i → f i .snd

θ-cong : ∀ {x y} → Colim (F ∘ᴰ D) [ x ≈ y ] → Colim D [ θ₀ x ≈ θ₀ y ]
θ-cong {α , (a , f)} {α , (b , g)} (≈lstage α (mk≈ꟳ ≡.refl snd≈)) =
  ≈lstage (sup (ιˢ a , (λ _ → α))) (≈pcong a (λ _ → α) f g snd≈)
θ-cong {α , (a , f)} {β , (a , g)} (≈lstep p (a , f)) =
  ≈lstep (sup≤sup λ _ → p) (sup (a , (λ i → f i .fst)) , _)
θ-cong {α , (a , f)} {β , (b , g)} (≈lsym p) =
  ≈lsym (θ-cong p)
θ-cong {α , (a , f)} {β , (b , g)} (≈ltrans p q) =
  ≈ltrans (θ-cong p) (θ-cong q)

θ : ≈.Hom (Colim (F ∘ᴰ D)) (Colim D)
θ = record { to = θ₀ ; cong = θ-cong }

θ̂ : ≈.Hom (F.F-ob (Colim D)) (Colim D)
θ̂ = θ ≈.∘ ψ


-- Main theorem: cocontinuous functors give initial algebras
theorem : Cocontinuous F D → ∥ Record ∥
theorem ∣ iso ∣ = ∣ record
  { Xα = record
    { alg = Qθ
    ; sat = sat }
  ; initial = record
    { rec = rec
    ; unique = {!!} } } ∣
  where
  open ≈.Hom θ̂ renaming (to to θ̂₀; cong to θ̂-cong)
  Qθ : ≈.Algebra F
  Qθ = record { X = Colim D ; α = θ̂ }
  sat : Sat Qθ Ξ
  sat π ξ = p
    where
    open Equation (Ξ π)
    p : Colim D [ assign Qθ ξ (lhs (Ξ π)) ≈ assign Qθ ξ (rhs (Ξ π)) ]
    p = begin
      assign Qθ ξ (supᴱ n (λ i → varᴱ i {λ()}))
        ≈⟨ refl ⟩
      θ₀ (ψ₀ (n , λ i → ξ i))
        ≈⟨ refl ⟩
      θ₀ (sup (ιˢ n , λ i → αˡ (ξ i)) , n , λ i →
         tˡ (ξ i) , ≤≤ (child≤ (ιˢ n) (λ i → αˡ (ξ i)) i) (t≤αˡ (ξ i)))
        ≈⟨ refl ⟩
      sup (ιˢ n , λ _ → sup (ιˢ n , λ i → αˡ (ξ i))) , sup (n , λ i → tˡ (ξ i)) , _
        ≈⟨ ≈lstage (sup (ιˢ n , (λ _ → sup (ιˢ n , (λ i → αˡ (ξ i)))))) q ⟩
      sup (ιˢ n , λ _ → sup (ιˢ n , λ i → αˡ (ξ i))) , sup (n , λ i → tˡ (ξ (π.to i))) , _
        ≈⟨ ≈lstep l≤r (sup (n , (λ i → tˡ (ξ (π.to i)))) , _) ⟩
      sup (ιˢ n , λ _ → sup (ιˢ n , λ i → αˡ (ξ (π.to i)))) , sup (n , λ i → tˡ (ξ (π.to i))) , _
        ≈⟨ refl ⟩
      θ₀ (sup (ιˢ n , λ i → αˡ (ξ (π.to i))) , n , λ i →
        tˡ (ξ (π.to i)) , ≤≤ (child≤ (ιˢ n) (λ i → αˡ (ξ (π.to i))) i) (t≤αˡ (ξ (π.to i))))
        ≈⟨ refl ⟩
      θ₀ (ψ₀ (n , λ i → ξ (π.to i)))
        ≈⟨ refl ⟩
      assign Qθ ξ (supᴱ n (λ i → varᴱ (π.to i) {λ()})) ∎
      where
      module π = _↔_ π
      open ≈.≈syntax {S = Colim D}
      open Setoid (Colim D)
      β : Z
      β = sup (ιˢ n , λ _ → sup (ιˢ n , λ i → αˡ (ξ i)))
      l≤r : (sup (ιˢ n , (λ _ → sup (ιˢ n , (λ i → αˡ (ξ i))))))
          ≤ (sup (ιˢ n , (λ _ → sup (ιˢ n , (λ i → αˡ (ξ (π.to i)))))))
      l≤r = sup≤sup λ _ → sup≤ λ i → <sup (π.from i) (≡→≤ (≡.cong (λ ○ → αˡ (ξ ○)) (≡.sym (π.linv i))))
      r≤l : (sup (ιˢ n , (λ _ → sup (ιˢ n , (λ i → αˡ (ξ (π.to i)))))))
          ≤ (sup (ιˢ n , (λ _ → sup (ιˢ n , (λ i → αˡ (ξ i))))))
      r≤l = sup≤sup λ _ → sup≤ λ i → <sup (π.to i) (≤refl (αˡ (ξ (π.to i))))
      q : D̃ β [ sup (n , λ i → tˡ (ξ i)) , _ ≈ sup (n , λ i → tˡ (ξ (π.to i))) , _ ]
      q = ≈psat π (λ i → tˡ (ξ i)) (θ.t≤β (sup (ιˢ n , (λ i → αˡ (ξ i)))) n (λ i → tˡ (ξ i) , _)) _
  rec : (Yβ : Alg) → Hom (record { alg = Qθ ; sat = sat }) Yβ
  rec Yβ = record { hom = ≈.Alg.mkHom r comm }
    where
    open Alg Yβ renaming (X to Y; α to β; sup to βsup; sat to Ysat)
    module Y = Setoid Y
    module β = ≈.Hom β
    c : T → ⟨ Y ⟩
    c (sup (s , f)) = βsup (s , λ i → c (f i))
    r₀ : Colim₀ D → ⟨ Y ⟩
    r₀ (_ , t , _) = c t
    r-cong : ∀ {x y} → Colim D [ x ≈ y ] → Y [ r₀ x ≈ r₀ y ]
    r-cong {α , (s1 , α≤s1)} {α , (s2 , α≤s2)} (≈lstage α p) = r-cong-stage p
      where
      r-cong-stage : ∀ {α ŝ t̂} → α ⊢ ŝ ≈ᵇ t̂ → r₀ (α , ŝ) Y.≈ r₀ (α , t̂)
      r-cong-stage {α} {ŝ} {t̂} (≈pcong a μ f g u) = β.cong (mk≈ꟳ ≡.refl λ i → r-cong-stage (u i))
      r-cong-stage {α} {ŝ} {t̂} (≈psat e ϕ₁ l≤α r≤α) = Ysat e (λ z → c (ϕ₁ z))
      r-cong-stage {α} {ŝ} {t̂} ≈prefl = Y.refl
      r-cong-stage {α} {ŝ} {t̂} (≈psym p) = Y.sym (r-cong-stage p)
      r-cong-stage {α} {ŝ} {t̂} (≈ptrans p q) = Y.trans (r-cong-stage p) (r-cong-stage q)
      r-cong-stage {α} {ŝ} {t̂} (≈pweaken β≤α p) = r-cong-stage p
    r-cong {α1 , (s1 , α≤s1)} {α2 , (s1 , α≤s2)} (≈lstep p (s1 , snd₁)) = Y.refl
    r-cong {α1 , (s1 , α≤s1)} {α2 , (s2 , α≤s2)} (≈lsym p) = Y.sym (r-cong p)
    r-cong {α1 , (s1 , α≤s1)} {α2 , (s2 , α≤s2)} (≈ltrans p q) = Y.trans (r-cong p) (r-cong q)
    r : ≈.Hom (Colim D) Y
    r = record { to = r₀ ; cong = r-cong }
    comm : (β ≈.∘ F-mor r) ≈h (r ≈.∘ θ̂)
    comm {l , f} =
      βsup (l , λ i → r₀ (f i))
        ≈⟨ ≡→≈ Y u ⟩
      βsup (l , λ i → c (g i))
        ≈⟨ refl ⟩
      r₀ (sup (ιˢ l , λ _ → ⊥ᶻ) , sup (l , λ()) , sup≤sup λ ())
        ≈⟨ refl ⟩
      r₀ (θ₀ (⊥ᶻ , l , λ()))
        ≈⟨ refl ⟩
      r₀ (θ₀ (ψ₀ (l , f))) ∎
      where
      open Setoid Y
      open ≈.≈syntax {S = Y}
      g : ⊥* → T
      g = λ ()
      u : βsup (l , λ i → r₀ (f i))
        ≡ βsup (l , λ i → c (g i))
      u = ≡.cong (λ ○ → βsup (l , ○)) (funExt (λ ()))

    comm {n , f} =
      βsup (n , λ i → r₀ (f i))
        ≈⟨ refl ⟩
      βsup (n , λ i → c (tˡ (f i)))
        ≈⟨ refl ⟩
      r₀ (θ₀ (ψ₀ (n , f))) ∎
      where
      open Setoid Y
      open ≈.≈syntax {S = Y}
