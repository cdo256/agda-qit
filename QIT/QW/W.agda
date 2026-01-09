open import QIT.Prelude
open import QIT.Setoid
open import QIT.Container.Base
open import QIT.QW.Signature

module QIT.QW.W {ℓS ℓP ℓE ℓV} (sig : Sig ℓS ℓP ℓE ℓV) where

open Sig sig
open import QIT.Container.Functor S P (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)

T : Set (ℓS ⊔ ℓP)
T = W S P
T̃ : Setoid (ℓS ⊔ ℓP) (ℓS ⊔ ℓP)
T̃ = ≡setoid T

T-alg : ≈.Algebra F
T-alg = record
  { X = T̃
  ; α = record
    { to = sup
    ; cong = α-cong } }
  where
  open F-Ob T̃
  α-cong : ∀ {sf} {tg} → sf ≈ꟳ tg → sup sf ≡p sup tg
  α-cong {s , f} {s , g} (mk≈ꟳ ≡.refl snd≈) = q (funExtp snd≈)
    where
    q : f ≡p g → sup (s , f) ≡p sup (s , g)
    q ∣ ≡.refl ∣ = ∣ ≡.refl ∣
