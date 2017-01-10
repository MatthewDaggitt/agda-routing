
open import Data.Nat using (suc)
open import Data.Fin using (Fin)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Data.Product using (_,_)
open import Function using (_∘_)

open import RoutingLib.Data.Fin using (punchup; punchdown)
open import RoutingLib.Data.Fin.Properties using (punchdown-punchup; punchdown-injective; punchup-injective; punchupₖ≢k)
open import RoutingLib.Data.Graph
open import RoutingLib.Data.Graph.EGPath

module RoutingLib.Data.Graph.Subgraph {a n} {A : Set a}  where

  _/_ : Graph A (suc n) → Fin (suc n) → Graph A n
  (G / k) i j = G (punchup k i) (punchup k j)

  data ⟦_/_⟧_≃_ : ∀ G k → EGPath G → EGPath (G / k) → Set a where
    [_] : ∀ {G k i j} → i ≡ punchup k j → ⟦ G / k ⟧ [ i ] ≃ [ j ]
    _∷_ : ∀ {G k i j} {p : EGPath G} {q i∉p j∉q ip₀∈G iq₀∉G/k} → i ≡ punchup k j → ⟦ G / k ⟧ p ≃ q → ⟦ G / k ⟧ (i ∷ p ∣ i∉p ∣ ip₀∈G) ≃ (j ∷ q ∣ j∉q ∣ iq₀∉G/k)


  -- ↓ conversion

  ↓convert : ∀ {G k} (p : EGPath G) → k ∉ p → EGPath (G / k)
  ↓convert∉ : ∀ {G k i} (p : EGPath G) → (k∉p : k ∉ p) → (i∉p : i ∉ p) → (k≢i : k ≢ i) → punchdown k≢i ∉ ↓convert p k∉p
  ↓convertSource : ∀ {G} k (p : EGPath G) k∉p → punchup k (source (↓convert p k∉p)) ≡ source p

  ↓convert {_} [ i ]                     (notThere k≢i)    = [ punchdown k≢i ]
  ↓convert {G} {k} (i ∷ p ∣ i∉p ∣ (v , e≈v)) (notHere k≢i k∉p) = punchdown k≢i ∷ ↓convert p k∉p ∣ ↓convert∉ p k∉p i∉p k≢i ∣ (v , trans (cong₂ G (punchdown-punchup k≢i) (↓convertSource k p k∉p)) e≈v)

  ↓convert∉ [ j ]           (notThere k≢j)     (notThere i≢j)   k≢i = notThere (i≢j ∘ punchdown-injective k≢i k≢j)
  ↓convert∉ (j ∷ p ∣ _ ∣ _) (notHere k≢j k∉p) (notHere i≢j i∉p) k≢i = notHere (i≢j ∘ punchdown-injective k≢i k≢j) (↓convert∉ p k∉p i∉p k≢i)

  ↓convertSource _ [ i ]            (notThere k≢i) = punchdown-punchup k≢i
  ↓convertSource _ (_ ∷ _ ∣ _ ∣ _) (notHere k≢i _) = punchdown-punchup k≢i

  ↓convertPath-≃ : ∀ {G : Graph A (suc n)} {k p} (k∉p : k ∉ p) → ⟦ G / k ⟧ p ≃ ↓convert p k∉p
  ↓convertPath-≃ (notThere k≢i)    = [ sym (punchdown-punchup k≢i) ]
  ↓convertPath-≃ (notHere k≢i k∉p) = sym (punchdown-punchup k≢i) ∷ ↓convertPath-≃ k∉p



  -- ↑ conversion
  
  ↑convert : ∀ (G : Graph A (suc n)) k (p : EGPath (G / k)) → EGPath G
  ↑convert∉ : ∀ {G : Graph A (suc n)} k (p : EGPath (G / k)) → ∀ {i} → i ∉ p → punchup k i ∉ ↑convert G k p
  ↑convertSource : ∀ (G : Graph A (suc n)) k (p : EGPath (G / k)) → source (↑convert G k p) ≡ punchup k (source p)

  ↑convert _ k [ i ]                     = [ punchup k i ]
  ↑convert G k (i ∷ p ∣ i∉p ∣ (v , e≈v)) = punchup k i ∷ ↑convert G k p ∣ ↑convert∉ k p i∉p ∣ (v , trans (cong₂ G refl (↑convertSource G k p)) e≈v)

  ↑convert∉ k [ j ] (notThere i≢j) = notThere (i≢j ∘ punchup-injective k)
  ↑convert∉ k (j ∷ p ∣ _ ∣ _) (notHere i≢j i∉p) = notHere (i≢j ∘ punchup-injective k) (↑convert∉ k p i∉p)

  ↑convertSource _ _ [ _ ] = refl
  ↑convertSource _ _ (_ ∷ _ ∣ _ ∣ _) = refl

  k∉↑convertₖ : ∀ {G : Graph A (suc n)} k p → k ∉ ↑convert G k p 
  k∉↑convertₖ k [ i ] = notThere (punchupₖ≢k k ∘ sym) 
  k∉↑convertₖ k (_ ∷ p ∣ _ ∣ _) = notHere (punchupₖ≢k k ∘ sym) (k∉↑convertₖ k p)

  ↑convert-length : ∀ {G : Graph A (suc n)} k p → length (↑convert G k p) ≡ length p
  ↑convert-length k [ _ ] = refl
  ↑convert-length k (_ ∷ p ∣ _ ∣ _) = cong suc (↑convert-length k p)

  ↑convert-destination : ∀ (G : Graph A (suc n)) k p → destination (↑convert G k p) ≡ punchup k (destination p)
  ↑convert-destination _ _ [ _ ] = refl
  ↑convert-destination G k (_ ∷ p ∣ _ ∣ _) = ↑convert-destination G k p

  ↑convert-weight : ∀ {b} {B : Set b} (_▷_ : A → B → B) (one : B) (G : Graph A (suc n)) k p  → weight _▷_ one p ≡ weight _▷_ one (↑convert G k p)
  ↑convert-weight _▷_ one G k [ _ ]                 = refl
  ↑convert-weight _▷_ one G k (_ ∷ p ∣ _ ∣ (v , _)) = cong (v ▷_) (↑convert-weight _▷_ one G k p)

  ↑convert-cong : ∀ (G : Graph A (suc n)) k {p q} → p ≈ₚ q → ↑convert G k p ≈ₚ ↑convert G k q
  ↑convert-cong _ _ {[ _ ]}         {[ _ ]}         [ refl ] = [ refl ]
  ↑convert-cong _ _ {[ _ ]}         {_ ∷ _ ∣ _ ∣ _} ()
  ↑convert-cong _ _ {_ ∷ _ ∣ _ ∣ _} {[ _ ]}         ()
  ↑convert-cong G k {_ ∷ _ ∣ _ ∣ _} {_ ∷ _ ∣ _ ∣ _} (refl ∷ p≈q) = refl ∷ ↑convert-cong G k p≈q
