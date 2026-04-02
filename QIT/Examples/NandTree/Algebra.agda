open import QIT.Prelude
open import QIT.Relation.Nullary

module QIT.Examples.NandTree.Algebra
  (B : Set) (_≟ᴮ_ : Discrete B) (V : Set) where


record Algebra : Set₁ where  
  field
    Tᴬ : Set
    vᴬ : V → Tᴬ
    nᴬ : (B → Tᴬ) → Tᴬ
    
data WL : (A : Set) → Set where
  wlintro : ∀ A → WL (WL A) → WL A
    
{-
[ Tᴬ ]

abc(abc)*

{abc,ac} -- triangle
{abc,adc} -- square
{abd,adb}

-}
