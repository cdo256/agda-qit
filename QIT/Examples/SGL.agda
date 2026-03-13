module QIT.Examples.SGL where

open import QIT.Prelude
open import QIT.Prop
open import QIT.Relation.Subset

record Graph : Set₁ where
  field
    N : Set
    L : N → N → Set
    root : N

zG : Graph
zG = record
  { N = ⊤
  ; L = λ _ _ → ⊥
  ; root = tt }

sG : Graph → Graph
sG G = record
  { N = ⊤ ⊎ G.N
  ; L = L
  ; root = inj₁ tt }
  where
  module G = Graph G
  data L : ⊤ ⊎ G.N → ⊤ ⊎ G.N → Set where
    Lι : ∀ x y → G.L x y → L (inj₂ x) (inj₂ y)
    Lsuc : L (inj₁ tt) (inj₂ G.root)

module _ (G : Graph) where
  open Graph G
  data R : (x y : N) → Prop where
    Rrefl : ∀ x → R x x
    Rext : ∀ x y z → R x y → L y z → R x z

  OutGraph : (x : N) → Graph
  OutGraph x = record
    { N = ΣP N (R x)
    ; L = λ (y , _) (z , _) → L y z
    ; root = x , Rrefl x }

record Hom (G H : Graph) : Set where
  module G = Graph G
  module H = Graph H
  field
    hN : G.N → H.N
    hL : ∀ x y → G.L x y → H.L (hN x) (hN y)
    hroot : hN G.root ≡ H.root

record Iso (G H : Graph) : Set where
  module G = Graph G
  module H = Graph H
  field
    iN : G.N ↔ H.N
  module iN = _↔_ iN 
  field
    iL : ∀ x y → G.L x y ↔ H.L (iN.to x) (iN.to y)
    iroot : iN.to G.root ≡ H.root

data _≈_ : Graph → Graph → Prop₁ where
  ≈iso : ∀ G H
       → Iso (OutGraph G (Graph.root G))
             (OutGraph H (Graph.root H))
       → G ≈ H
