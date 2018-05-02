open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Flip
open import Relation.Binary.Lattice using (Minimum; Maximum)

open import RoutingLib.Relation.Binary

module RoutingLib.Relation.Binary.Flip where

  -- All added to standard library
  
  module _ {a ℓ₁ ℓ₂} {A : Set a} (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂) where
  
    reflexiveᵘ : Symmetric ≈ → ≈ ⇒ ∼ → ≈ ⇒ flip ∼
    reflexiveᵘ sym impl = impl ∘ sym
  
    antisymmetricᵘ : Antisymmetric ≈ ∼ → Antisymmetric ≈ (flip ∼)
    antisymmetricᵘ antisym y∼x x∼y = antisym x∼y y∼x

    irreflexiveᵘ : Symmetric ≈ → Irreflexive ≈ ∼ → Irreflexive ≈ (flip ∼)
    irreflexiveᵘ sym irrefl x≈y y∼x = irrefl (sym x≈y) y∼x

    respects₂ᵘ : ∼ Respects₂ ≈ → (flip ∼) Respects₂ ≈
    respects₂ᵘ (resp₁ , resp₂) = resp₂ , resp₁
    
    trichotomousᵘ : Trichotomous ≈ ∼ → Trichotomous ≈ (flip ∼)
    trichotomousᵘ compare x y with compare x y
    ... | tri< x<y x≉y y≮x = tri> y≮x x≉y x<y
    ... | tri≈ x≮y x≈y y≮x = tri≈ y≮x x≈y x≮y
    ... | tri> x≮y x≉y y<x = tri< y<x x≉y x≮y

  module _ {a ℓ} {A : Set a} (∼ : Rel A ℓ) where
  
    max : ∀ {⊥} → Minimum ∼ ⊥ → Maximum (flip ∼) ⊥
    max min = min

    min : ∀ {⊥} → Maximum ∼ ⊥ → Minimum (flip ∼) ⊥
    min max = max
    
  module _ {a ℓ₁ ℓ₂} {A : Set a} {≈ : Rel A ℓ₁} {∼ : Rel A ℓ₂} where
  
    isPreorderᵘ : IsPreorder ≈ ∼ → IsPreorder ≈ (flip ∼)
    isPreorderᵘ pre = record
      { isEquivalence = Pre.isEquivalence
      ; reflexive     = reflexiveᵘ ≈ ∼ Pre.Eq.sym Pre.reflexive
      ; trans         = transitive ∼ Pre.trans
      }
      where module Pre = IsPreorder pre

    isTotalPreorderᵘ : IsTotalPreorder ≈ ∼ → IsTotalPreorder ≈ (flip ∼)
    isTotalPreorderᵘ pre = record
      { isPreorder = isPreorderᵘ Pre.isPreorder
      ; total      = total ∼ Pre.total
      }
      where module Pre = IsTotalPreorder pre
      
    isPartialOrderᵘ : IsPartialOrder ≈ ∼ → IsPartialOrder ≈ (flip ∼)
    isPartialOrderᵘ po = record
      { isPreorder = isPreorderᵘ Po.isPreorder
      ; antisym    = antisymmetricᵘ ≈ ∼ Po.antisym
      }
      where module Po = IsPartialOrder po

    isStrictPartialOrderᵘ : IsStrictPartialOrder ≈ ∼ → IsStrictPartialOrder ≈ (flip ∼)
    isStrictPartialOrderᵘ spo = record
      { isEquivalence = Spo.isEquivalence
      ; irrefl        = irreflexiveᵘ ≈ ∼ Spo.Eq.sym Spo.irrefl
      ; trans         = transitive ∼ Spo.trans
      ; <-resp-≈      = respects₂ᵘ ≈ ∼ Spo.<-resp-≈
      }
      where module Spo = IsStrictPartialOrder spo

    isTotalOrderᵘ : IsTotalOrder ≈ ∼ → IsTotalOrder ≈ (flip ∼)
    isTotalOrderᵘ to = record
      { isPartialOrder = isPartialOrderᵘ To.isPartialOrder
      ; total          = total ∼ To.total
      }
      where module To = IsTotalOrder to

    isDecTotalOrderᵘ : IsDecTotalOrder ≈ ∼ → IsDecTotalOrder ≈ (flip ∼)
    isDecTotalOrderᵘ dec = record
      { isTotalOrder = isTotalOrderᵘ Dec.isTotalOrder
      ; _≟_          = Dec._≟_
      ; _≤?_         = decidable ∼ Dec._≤?_
      }
      where module Dec = IsDecTotalOrder dec

    isStrictTotalOrderᵘ : IsStrictTotalOrder ≈ ∼ → IsStrictTotalOrder ≈ (flip ∼)
    isStrictTotalOrderᵘ sto = record
      { isEquivalence = Sto.isEquivalence
      ; trans         = transitive ∼ Sto.trans
      ; compare       = trichotomousᵘ ≈ ∼ Sto.compare
      }
      where module Sto = IsStrictTotalOrder sto


  module _ {ℓ₁ ℓ₂ ℓ₃} where
  
    preorderᵘ : Preorder ℓ₁ ℓ₂ ℓ₃ → Preorder ℓ₁ ℓ₂ ℓ₃
    preorderᵘ P = record
      { isPreorder = isPreorderᵘ (Preorder.isPreorder P)
      }

    totalPreorderᵘ : TotalPreorder ℓ₁ ℓ₂ ℓ₃ → TotalPreorder ℓ₁ ℓ₂ ℓ₃
    totalPreorderᵘ P = record
      { isTotalPreorder = isTotalPreorderᵘ (TotalPreorder.isTotalPreorder P)
      }
      
    posetᵘ : Poset ℓ₁ ℓ₂ ℓ₃ → Poset ℓ₁ ℓ₂ ℓ₃
    posetᵘ O = record
      { isPartialOrder = isPartialOrderᵘ (Poset.isPartialOrder O)
      }

    strictPartialOrderᵘ : StrictPartialOrder ℓ₁ ℓ₂ ℓ₃ → StrictPartialOrder ℓ₁ ℓ₂ ℓ₃
    strictPartialOrderᵘ O = record
      { isStrictPartialOrder = isStrictPartialOrderᵘ O.isStrictPartialOrder
      } where module O = StrictPartialOrder O

    totalOrderᵘ : TotalOrder ℓ₁ ℓ₂ ℓ₃ → TotalOrder ℓ₁ ℓ₂ ℓ₃
    totalOrderᵘ O = record
      { isTotalOrder = isTotalOrderᵘ O.isTotalOrder
      } where module O = TotalOrder O

    decTotalOrderᵘ : DecTotalOrder ℓ₁ ℓ₂ ℓ₃ → DecTotalOrder ℓ₁ ℓ₂ ℓ₃
    decTotalOrderᵘ O = record
      { isDecTotalOrder = isDecTotalOrderᵘ O.isDecTotalOrder
      } where module O = DecTotalOrder O

    strictTotalOrderᵘ : StrictTotalOrder ℓ₁ ℓ₂ ℓ₃ → StrictTotalOrder ℓ₁ ℓ₂ ℓ₃
    strictTotalOrderᵘ O = record
      { isStrictTotalOrder = isStrictTotalOrderᵘ O.isStrictTotalOrder
      } where module O = StrictTotalOrder O

