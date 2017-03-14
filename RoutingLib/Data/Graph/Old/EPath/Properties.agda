
open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; decTotalOrder) renaming (_<_ to _<ℕ_; _≤_ to _≤ℕ_; _≤?_ to _≤ℕ?_)
open import Data.Nat.Properties using (1+n≰n; n≤1+n)
open import Data.Fin using (Fin; toℕ; fromℕ≤) renaming (suc to fsuc ; zero to fzero)
open import Data.Fin.Properties using (_≟_; toℕ-fromℕ≤; toℕ-injective)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Any as Any using (here; there)
open import Data.List.All using (All; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (∃₂; _,_; _×_)
open import Data.Vec using (allFin) renaming (lookup to lookupᵥ; toList to toListᵥ)
open import Data.Vec.Properties using (∈-allFin)
open import Relation.Nullary using (yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; subst; subst₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; setoid to ≡-setoid)
open import Relation.Binary.On using () renaming (isDecEquivalence to on-isDecEquivalence; isDecTotalOrder to on-isDecTotalOrder; respects₂ to on-respects₂)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Consequences using (Total)
open import Relation.Binary.List.Pointwise using () renaming (setoid to list-setoid)
open import Function using (_∘_)

open import RoutingLib.Data.Graph using (Graph; _ᵉ∈ᵍ_)
open import RoutingLib.Data.Fin.Pigeonhole using (pigeonhole)
open import RoutingLib.Data.Graph.EPath
open import RoutingLib.Data.Fin.Properties using (≤-isDecTotalOrder; ≤-refl; ≤-total; ≤-antisym; ≤-trans; _≤?_)
open import RoutingLib.Data.Nat.Properties using (m≰n⇨n<m)
open import RoutingLib.Relation.Binary
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_; RespectedBy⇨Respects₂)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.All.Uniqueness.Properties using (concat!; allFin!; map!)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties using (forced-map; map-pairs; concat-all; ∈-All; ¬Any→All¬)
open import RoutingLib.Data.List.Any.GenericMembership using (Disjoint; disjoint-[]; ∈-resp-≈; toList-preserves-∈; concat-∈; ∈-map)
open import RoutingLib.Data.List.Enumeration

module RoutingLib.Data.Graph.EPath.Properties {n : ℕ} where

  --------------
  -- Equality --
  --------------

  ≈ₚ-refl : Reflexive (_≈ₚ_ {n})
  ≈ₚ-refl {x = [ _ ]}     = [ ≡-refl ]
  ≈ₚ-refl {x = _ ∷ _ ∣ _} = ≡-refl ∷ ≈ₚ-refl

  ≈ₚ-reflexive : _≡_ ⇒ (_≈ₚ_ {n})
  ≈ₚ-reflexive ≡-refl = ≈ₚ-refl

  ≈ₚ-sym : Symmetric (_≈ₚ_ {n})
  ≈ₚ-sym  [ ≡-refl ]    = [ ≡-refl ]
  ≈ₚ-sym (≡-refl ∷ p≈q) = ≡-refl ∷ (≈ₚ-sym p≈q)

  ≈ₚ-trans : Transitive (_≈ₚ_ {n})
  ≈ₚ-trans [ ≡-refl ]    [ ≡-refl ]    = [ ≡-refl ]
  ≈ₚ-trans (x≈y ∷ xs≈ys) (y≈z ∷ ys≈zs) = (≡-trans x≈y y≈z) ∷ (≈ₚ-trans xs≈ys ys≈zs)

  _≟ₚ_ : Decidable (_≈ₚ_ {n})
  [ i ]        ≟ₚ [ j ] with i ≟ j
  ... | no  i≢j = no (λ {([ i≡j ]) → i≢j i≡j})
  ... | yes i≡j = yes ([ i≡j ])
  [ _ ]        ≟ₚ (_ ∷ _ ∣ _)  = no λ()
  (_ ∷ _  ∣ _) ≟ₚ [ _ ]        = no λ()
  (x ∷ xs ∣ _) ≟ₚ (y ∷ ys ∣ _) with x ≟ y | xs ≟ₚ ys
  ... | no  x≉y | _         = no λ{(x≈y ∷ _) → x≉y x≈y}
  ... | _       | no  xs≉ys = no λ{(_ ∷ xs≈ys) → xs≉ys xs≈ys}
  ... | yes x≈y | yes xs≈ys = yes (x≈y ∷ xs≈ys)

  ≈ₚ-isEquivalence : IsEquivalence (_≈ₚ_ {n})
  ≈ₚ-isEquivalence = record {
      refl = ≈ₚ-refl;
      sym = ≈ₚ-sym;
      trans = ≈ₚ-trans
    }

  ≈ₚ-setoid : Setoid _ _
  ≈ₚ-setoid = record {
      Carrier = EPath n;
      _≈_ = _≈ₚ_;
      isEquivalence = ≈ₚ-isEquivalence
    }

  ≈ₚ-isDecEquivalence : IsDecEquivalence (_≈ₚ_ {n})
  ≈ₚ-isDecEquivalence = record {
      isEquivalence = ≈ₚ-isEquivalence;
      _≟_ = _≟ₚ_
    }

  ≈ₚ-decSetoid : DecSetoid _ _
  ≈ₚ-decSetoid = record {
      Carrier = EPath n ;
      _≈_ = _≈ₚ_ ;
      isDecEquivalence = ≈ₚ-isDecEquivalence
    }

  -- Other properties

  p≉i∷p : ∀ {i} {p : EPath n} {i∉p} → p ≉ₚ i ∷ p ∣ i∉p
  p≉i∷p (_ ∷ rec) = p≉i∷p rec

  p≈q⇨p₀≡q₀ : ∀ {p q : EPath n} → p ≈ₚ q → source p ≡ source q
  p≈q⇨p₀≡q₀ [ ≡-refl ]   = ≡-refl
  p≈q⇨p₀≡q₀ (≡-refl ∷ _) = ≡-refl

  p₀≢q₀⇨p≉q : ∀ {p q : EPath n} → source p ≢ source q → p ≉ₚ q
  p₀≢q₀⇨p≉q p₀≢q₀ p≈q = p₀≢q₀ (p≈q⇨p₀≡q₀ p≈q)

  pₜ≉qₜ⇨p≉q : ∀ {i j : Fin n} {p q i∉p j∉q} → p ≉ₚ q → (i ∷ p ∣ i∉p) ≉ₚ (j ∷ q ∣ j∉q)
  pₜ≉qₜ⇨p≉q p≉q (_ ∷ p≈q) = p≉q p≈q

  i≢j⇨[i]≉[j] : ∀ {i j : Fin n} → i ≢ j → [ i ] ≉ₚ [ j ]
  i≢j⇨[i]≉[j] i≢j = p₀≢q₀⇨p≉q i≢j


  p≈q∧ip₀∈G⇨iq₀∈G : ∀ {a} {A : Set a} (G : Graph A n) {p q : EPath n} → p ≈ₚ q → ∀ {i} → (i , source p) ᵉ∈ᵍ G → (i , source q) ᵉ∈ᵍ G
  p≈q∧ip₀∈G⇨iq₀∈G G p≈q {i} ip₀∈G = subst (λ v → (i , v) ᵉ∈ᵍ G) (p≈q⇨p₀≡q₀ p≈q) ip₀∈G




  ----------------------------
  -- Lexicographic ordering --
  ----------------------------

  ≤ₚ-resp-≈ₚ : (_≤ₚ_ {n}) RespectedBy _≈ₚ_
  ≤ₚ-resp-≈ₚ [ ≡-refl ]     [ ≡-refl ]     p≤r                    = p≤r
  ≤ₚ-resp-≈ₚ [ ≡-refl ]     (_ ∷ r≈s)      (stopLeft [i]≤r)        = stopLeft (≤ₚ-resp-≈ₚ [ ≡-refl ] r≈s [i]≤r)
  ≤ₚ-resp-≈ₚ (_      ∷ p≈q) [ ≡-refl ]     (stopRight p≉[k] [k]≤p) = stopRight (λ q≈[l] → p≉[k] (≈ₚ-trans p≈q (≈ₚ-trans q≈[l] [ ≡-refl ]))) (≤ₚ-resp-≈ₚ p≈q [ ≡-refl ] [k]≤p)
  ≤ₚ-resp-≈ₚ (≡-refl ∷ p≈q) (≡-refl ∷ r≈s) (stepEqual p≈r i≤k)     = stepEqual (≈ₚ-trans (≈ₚ-trans (≈ₚ-sym p≈q) p≈r) r≈s) i≤k
  ≤ₚ-resp-≈ₚ (≡-refl ∷ p≈q) (≡-refl ∷ r≈s) (stepUnequal p≉r p≤r)   = stepUnequal (λ q≈s → p≉r (≈ₚ-trans p≈q (≈ₚ-trans q≈s (≈ₚ-sym r≈s)))) (≤ₚ-resp-≈ₚ p≈q r≈s p≤r)

  ≤ₚ-resp₂-≈ₚ : (_≤ₚ_ {n}) Respects₂ _≈ₚ_
  ≤ₚ-resp₂-≈ₚ = RespectedBy⇨Respects₂ ≈ₚ-refl ≤ₚ-resp-≈ₚ

  ≤ₚ-total : Total (_≤ₚ_ {n})
  ≤ₚ-total [ i ]         [ j ]         with ≤-total i j
  ... | inj₁ i≤j = inj₁ (stop i≤j)
  ... | inj₂ j≤i = inj₂ (stop j≤i)
  ≤ₚ-total [ i ]       (j ∷ q ∣ _) with q ≟ₚ [ i ] | ≤ₚ-total [ i ] q
  ... | _         | inj₁ [i]≤q = inj₁ (stopLeft [i]≤q)
  ... | no  q≉[i] | inj₂ q≤[i] = inj₂ (stopRight q≉[i] q≤[i])
  ≤ₚ-total [ i ] (j ∷ [ .i ] ∣ _) | yes [ ≡-refl ] | inj₂ q≤[i] = inj₁ (stopLeft q≤[i])
  ≤ₚ-total (i ∷ p ∣ _) [ j ]         with p ≟ₚ [ j ] | ≤ₚ-total p [ j ]
  ... | _         | inj₂ [j]≤p = inj₂ (stopLeft [j]≤p)
  ... | no  p≉[j] | inj₁ p≤[j] = inj₁ (stopRight p≉[j] p≤[j])
  ≤ₚ-total (i ∷ [ j ] ∣ _) [ .j ] | yes [ ≡-refl ] | inj₁ p≤[j] = inj₂ (stopLeft p≤[j])
  ≤ₚ-total (i ∷ p ∣ _) (j ∷ q ∣ _ ) with p ≟ₚ q | ≤-total i j | ≤ₚ-total p q
  ... | yes p≈q | inj₁ i≤j | _        = inj₁ (stepEqual p≈q i≤j)
  ... | yes p≈q | inj₂ j≤i | _        = inj₂ (stepEqual (≈ₚ-sym p≈q) j≤i)
  ... | no  p≉q | _        | inj₁ p≤q = inj₁ (stepUnequal p≉q p≤q)
  ... | no  p≉q | _        | inj₂ q≤p = inj₂ (stepUnequal (p≉q ∘ ≈ₚ-sym) q≤p)

  ≤ₚ-refl : Reflexive (_≤ₚ_ {n})
  ≤ₚ-refl {[ _ ]}     = stop ≤-refl
  ≤ₚ-refl {_ ∷ _ ∣ _} = stepEqual ≈ₚ-refl ≤-refl

  ≤ₚ-reflexive : (_≈ₚ_ {n}) Relation.Binary.⇒ _≤ₚ_
  ≤ₚ-reflexive [ ≡-refl ]     = ≤ₚ-refl
  ≤ₚ-reflexive (≡-refl ∷ p≈q) = stepEqual p≈q ≤-refl

  ≤ₚ-antisym : Antisymmetric (_≈ₚ_ {n}) _≤ₚ_
  ≤ₚ-antisym (stop i≤j)              (stop j≤i)              = [ ≤-antisym i≤j j≤i ]
  ≤ₚ-antisym (stopRight p≉[j] p≤[j]) (stopLeft [j]≤p)        = contradiction (≤ₚ-antisym p≤[j] [j]≤p) p≉[j]
  ≤ₚ-antisym (stopLeft [i]≤q)        (stopRight q≉[i] q≤[i]) = contradiction (≤ₚ-antisym q≤[i] [i]≤q) q≉[i]
  ≤ₚ-antisym (stepEqual p≈q i≤j)     (stepEqual q≈p j≤i)     = (≤-antisym i≤j j≤i) ∷ p≈q
  ≤ₚ-antisym (stepEqual p≈q i≤j)     (stepUnequal q≉p q≤p)   = contradiction (≈ₚ-sym p≈q) q≉p
  ≤ₚ-antisym (stepUnequal p≉q p≤q)   (stepEqual q≈p j≤i)     = contradiction (≈ₚ-sym q≈p) p≉q
  ≤ₚ-antisym (stepUnequal p≉q p≤q)   (stepUnequal q≉p q≤p)   = contradiction (≤ₚ-antisym p≤q q≤p) p≉q

  ≤ₚ-trans : Transitive (_≤ₚ_ {n})
  ≤ₚ-trans (stop i≤j)              (stop j≤k)              = stop (≤-trans i≤j j≤k)
  ≤ₚ-trans (stop i≤j)              (stopLeft [j]≤r)        = stopLeft (≤ₚ-trans (stop i≤j) [j]≤r)
  ≤ₚ-trans (stopLeft [i]≤q)        (stopRight q≉[k] q≤[k]) = ≤ₚ-trans [i]≤q q≤[k]
  ≤ₚ-trans (stopLeft [i]≤q)        (stepEqual q≈r j≤k)     = stopLeft (≤ₚ-resp-≈ₚ ≈ₚ-refl q≈r [i]≤q)
  ≤ₚ-trans (stopLeft [i]≤q)        (stepUnequal q≉r q≤r)   = stopLeft (≤ₚ-trans [i]≤q q≤r)
  ≤ₚ-trans (stopRight p≉[j] p≤[j]) (stop j≤k)              = stopRight (λ p≈[k] → p≉[j] (≤ₚ-antisym p≤[j] (≤ₚ-resp-≈ₚ ≈ₚ-refl (≈ₚ-sym p≈[k]) (stop j≤k)))) (≤ₚ-trans p≤[j] (stop j≤k))
  ≤ₚ-trans (stopRight p≉[j] p≤[j]) (stopLeft [j]≤r)        = stepUnequal (λ p≈r → p≉[j] (≤ₚ-antisym p≤[j] (≤ₚ-resp-≈ₚ ≈ₚ-refl (≈ₚ-sym p≈r) [j]≤r))) (≤ₚ-trans p≤[j] [j]≤r)
  ≤ₚ-trans (stepEqual p≈q i≤j)     (stopRight q≉[k] q≤[k]) = stopRight (λ p≈[k] → q≉[k] (≈ₚ-trans (≈ₚ-sym p≈q) p≈[k])) (≤ₚ-resp-≈ₚ (≈ₚ-sym p≈q) ≈ₚ-refl q≤[k])
  ≤ₚ-trans (stepEqual p≈q i≤j)     (stepEqual q≈r j≤k)     = stepEqual (≈ₚ-trans p≈q q≈r) (≤-trans i≤j j≤k)
  ≤ₚ-trans (stepEqual p≈q i≤j)     (stepUnequal q≉r q≤r)   = stepUnequal (λ p≈r → q≉r (≈ₚ-trans (≈ₚ-sym p≈q) p≈r)) (≤ₚ-resp-≈ₚ (≈ₚ-sym p≈q) ≈ₚ-refl q≤r)
  ≤ₚ-trans (stepUnequal p≉q p≤q)   (stopRight q≉[k] q≤[k]) = stopRight (λ p≈[k] → q≉[k] (≤ₚ-antisym q≤[k] (≤ₚ-resp-≈ₚ p≈[k] ≈ₚ-refl p≤q))) (≤ₚ-trans p≤q q≤[k])
  ≤ₚ-trans (stepUnequal p≉q p≤q)   (stepEqual q≈r j≤k)     = stepUnequal (λ p≈r → p≉q (≈ₚ-trans p≈r (≈ₚ-sym q≈r))) (≤ₚ-resp-≈ₚ ≈ₚ-refl q≈r p≤q)
  ≤ₚ-trans (stepUnequal p≉q p≤q)   (stepUnequal q≉r q≤r)   = stepUnequal (λ p≈r → q≉r (≤ₚ-antisym q≤r (≤ₚ-resp-≈ₚ p≈r ≈ₚ-refl p≤q))) (≤ₚ-trans p≤q q≤r)

  _≤ₚ?_ : Decidable (_≤ₚ_ {n})
  [ i ] ≤ₚ? [ j ] with i ≤? j
  ... | yes i≤j = yes (stop i≤j)
  ... | no  i≰j = no (λ {(stop i≤j) → i≰j i≤j})
  [ i ] ≤ₚ? (j ∷ q ∣ _ ) with [ i ] ≤ₚ? q
  ... | yes [i]≤q = yes (stopLeft [i]≤q)
  ... | no  [i]≰q = no (λ {(stopLeft [i]≤q) → [i]≰q [i]≤q})
  (i ∷ p ∣ _ ) ≤ₚ? [ j ] with p ≟ₚ [ j ] | p ≤ₚ? [ j ]
  ... | _ | no p≰[j] = no (λ {(stopRight _ p≤[j]) → p≰[j] p≤[j]})
  ... | yes p≈[j] | _ = no (λ {(stopRight p≉[j] _) → p≉[j] p≈[j]})
  ... | no p≉[j] | yes p≤[j] = yes (stopRight p≉[j] p≤[j])
  (i ∷ p ∣ _ ) ≤ₚ? (j ∷ q ∣ _ ) with p ≟ₚ q | i ≤? j | p ≤ₚ? q
  ... | yes p≈q | yes i≤j | _       = yes (stepEqual p≈q i≤j)
  ... | yes p≈q | no  i≰j | _       = no (λ {(stepEqual _ i≤j) → i≰j i≤j ; (stepUnequal p≉q _) → p≉q p≈q })
  ... | no  p≉q | _       | yes p≤q = yes (stepUnequal p≉q p≤q)
  ... | no  p≉q | _       | no  p≰q = no (λ {(stepEqual p≈q _) → p≉q p≈q ; (stepUnequal _ p≤q) → p≰q p≤q})


  ≤ₚ-isPreorder : IsPreorder (_≈ₚ_ {n}) _≤ₚ_
  ≤ₚ-isPreorder = record {
      isEquivalence = ≈ₚ-isEquivalence ;
      reflexive = ≤ₚ-reflexive ;
      trans = ≤ₚ-trans
    }

  ≤ₚ-isPartialOrder : IsPartialOrder (_≈ₚ_ {n}) _≤ₚ_
  ≤ₚ-isPartialOrder = record {
      isPreorder = ≤ₚ-isPreorder ;
      antisym = ≤ₚ-antisym
    }

  ≤ₚ-isTotalOrder : IsTotalOrder (_≈ₚ_ {n}) _≤ₚ_
  ≤ₚ-isTotalOrder = record {
      isPartialOrder = ≤ₚ-isPartialOrder ;
      total = ≤ₚ-total
    }

  ≤ₚ-isDecTotalOrder : IsDecTotalOrder (_≈ₚ_ {n}) _≤ₚ_
  ≤ₚ-isDecTotalOrder = record {
      isTotalOrder = ≤ₚ-isTotalOrder ;
      _≟_ = _≟ₚ_ ;
      _≤?_ = _≤ₚ?_
    }


  -- Other

  p≤ₚi∷p : ∀ {i} {p : EPath n} {i∉p} → p ≤ₚ i ∷ p ∣ i∉p
  p≤ₚi∷p {p = [ j ]}    = stopLeft (stop ≤-refl)
  p≤ₚi∷p {p = j ∷ q ∣ _} = stepUnequal p≉i∷p p≤ₚi∷p

  i∷p≰ₚp : ∀ {i} {p : EPath n} {i∉p} → i ∷ p ∣ i∉p ≰ₚ p
  i∷p≰ₚp (stopRight [j]≉[j] _)   = contradiction ([ ≡-refl ]) [j]≉[j]
  i∷p≰ₚp (stepEqual i∷p≈p _)     = p≉i∷p (≈ₚ-sym i∷p≈p)
  i∷p≰ₚp (stepUnequal i∷p≉p rec) = i∷p≰ₚp rec


  ---------------------
  -- Length ordering --
  ---------------------

  ≤ₗ-reflexive : (_≈ₚ_ {n}) ⇒ _≤ₗ_
  ≤ₗ-reflexive [ ≡-refl ]     = z≤n
  ≤ₗ-reflexive (≡-refl ∷ p≈q) = s≤s (≤ₗ-reflexive p≈q)

  ≤ₗ-refl : Reflexive (_≤ₗ_ {n})
  ≤ₗ-refl {[ _ ]}     = z≤n
  ≤ₗ-refl {_ ∷ _ ∣ _} = s≤s ≤ₗ-refl

  ≤ₗ-trans : Transitive (_≤ₗ_ {n})
  ≤ₗ-trans {[ _ ]}     {_}          {_}         _          _        = z≤n
  ≤ₗ-trans {_ ∷ _ ∣ _} {[ _ ]}      {_}         ()
  ≤ₗ-trans {_ ∷ _ ∣ _} {_ ∷ _ ∣ _}  {[ _ ]}     _         ()
  ≤ₗ-trans {_ ∷ _ ∣ _} {_ ∷ _ ∣ _}  {_ ∷ _ ∣ _} (s≤s p≤q) (s≤s q≤r) = s≤s (≤ₗ-trans p≤q q≤r)

  ≤ₗ-total : Total (_≤ₗ_ {n})
  ≤ₗ-total [ _ ]       [ _ ]        = inj₁ z≤n
  ≤ₗ-total [ _ ]       (_ ∷ _ ∣ _)  = inj₁ z≤n
  ≤ₗ-total (_ ∷ _ ∣ _) [ _ ]        = inj₂ z≤n
  ≤ₗ-total (_ ∷ p ∣ _) (_ ∷ q ∣ _ ) with ≤ₗ-total p q
  ... | inj₁ p≤q = inj₁ (s≤s p≤q)
  ... | inj₂ q≤p = inj₂ (s≤s q≤p)

  _≤ₗ?_ : Decidable (_≤ₗ_ {n})
  [ _ ]        ≤ₗ? [ _ ]        = yes z≤n
  [ _ ]        ≤ₗ? (_ ∷ _ ∣ _ ) = yes z≤n
  (_ ∷ _ ∣ _ ) ≤ₗ? [ _ ]        = no λ()
  (_ ∷ p ∣ _ ) ≤ₗ? (_ ∷ q ∣ _ ) with p ≤ₗ? q
  ... | yes p≤q = yes (s≤s p≤q)
  ... | no  p≰q = no (λ {(s≤s p≤q) → p≰q p≤q})

  ≤ₗ-resp-≈ₚ : (_≤ₗ_ {n}) RespectedBy _≈ₚ_
  ≤ₗ-resp-≈ₚ [ ≡-refl ]     [ ≡-refl ]     _         = z≤n
  ≤ₗ-resp-≈ₚ [ ≡-refl ]     (_ ∷ _)        _         = z≤n
  ≤ₗ-resp-≈ₚ (_ ∷ _)        [ ≡-refl ]     ()
  ≤ₗ-resp-≈ₚ (≡-refl ∷ p≈q) (≡-refl ∷ r≈s) (s≤s p≤r) = s≤s (≤ₗ-resp-≈ₚ p≈q r≈s p≤r)

  ≤ₗ-resp₂-≈ₚ : (_≤ₗ_ {n}) Respects₂ _≈ₚ_
  ≤ₗ-resp₂-≈ₚ = RespectedBy⇨Respects₂ ≈ₚ-refl ≤ₗ-resp-≈ₚ

  ≤ₗ-isPreorder : IsPreorder (_≈ₚ_ {n}) _≤ₗ_
  ≤ₗ-isPreorder = record {
      isEquivalence = ≈ₚ-isEquivalence ;
      reflexive = ≤ₗ-reflexive ;
      trans = ≤ₗ-trans
    }

  ≤ₗ-isTotalPreorder : IsTotalPreorder (_≈ₚ_ {n}) _≤ₗ_
  ≤ₗ-isTotalPreorder = record {
      isPreorder = ≤ₗ-isPreorder ;
      total = ≤ₗ-total
    }

  ≤ₗ-isDecTotalPreorder : IsDecTotalPreorder (_≈ₚ_ {n}) _≤ₗ_
  ≤ₗ-isDecTotalPreorder = record {
      isTotalPreorder = ≤ₗ-isTotalPreorder ;
      _≟_ = _≟ₚ_ ;
      _≤?_ = _≤ₗ?_
    }

  -- Other

  p≤ₗi∷p : ∀ {i} {p : EPath n} {i∉p} → p ≤ₗ i ∷ p ∣ i∉p
  p≤ₗi∷p {p = p} = n≤1+n (length p)

  i∷p≰ₗp : ∀ {i} {p : EPath n} {i∉p} → i ∷ p ∣ i∉p ≰ₗ p
  i∷p≰ₗp = 1+n≰n

  ------------
  -- Lookup --
  ------------

  lookup-toVec : ∀ (p : EPath n) i → lookupᵥ i (toVec p) ≡ lookup p i
  lookup-toVec [ _ ] fzero = ≡-refl
  lookup-toVec [ _ ] (fsuc ())
  lookup-toVec (i ∷ p ∣ _) fzero = ≡-refl
  lookup-toVec (i ∷ p ∣ _) (fsuc j) = lookup-toVec p j

  lookup-∉ : ∀ {v} {p : EPath n} i → v ∉ p → lookup p i ≢ v
  lookup-∉ {p = [ _ ]}     fzero     (notThere i≢v)      = i≢v ∘ ≡-sym
  lookup-∉ {p = _ ∷ _ ∣ _} fzero     (notHere  i≢v _)    = i≢v ∘ ≡-sym
  lookup-∉ {p = [ _ ]}     (fsuc ())
  lookup-∉ {p = _ ∷ _ ∣ _} (fsuc l)  (notHere  i≢v v∉ps) = lookup-∉ l v∉ps

  lookup! : ∀ (p : EPath n) {i j} → i ≢ j → lookup p i ≢ lookup p j
  lookup!  _            {i = fzero}   {j = fzero}   i≢j = contradiction ≡-refl i≢j
  lookup! [ _ ]         {i = fsuc ()}
  lookup! [ _ ]                       {j = fsuc ()}
  lookup! (k ∷ p ∣ k∉p) {i = fzero}   {j = fsuc j}  i≢j = (lookup-∉ j k∉p) ∘ ≡-sym
  lookup! (k ∷ p ∣ k∉p) {i = fsuc i}  {j = fzero}   i≢j = lookup-∉ i k∉p
  lookup! (k ∷ p ∣ _ )  {i = fsuc i}  {j = fsuc j}  i≢j = lookup! p (i≢j ∘ cong fsuc)


  -- Length

  |i∷p|≡l+1⇨|p|≡l : ∀ {p : EPath n} {l i i∉p} → length (i ∷ p ∣ i∉p) ≡ suc l → length p ≡ l
  |i∷p|≡l+1⇨|p|≡l ≡-refl = ≡-refl

  |p|<n : (p : EPath n) → length p <ℕ n
  |p|<n p with suc (length p) ≤ℕ? n
  ... | yes |p|<n = |p|<n
  ... | no  |p|≮n with pigeonhole (m≰n⇨n<m |p|≮n) (λ z → lookupᵥ z (toVec p))
  ...   | i , j , i≢j , pᵢ≡pⱼ =
    contradiction
      (subst₂ _≡_ (lookup-toVec p i) (lookup-toVec p j) pᵢ≡pⱼ)
      (lookup! p i≢j)

  length-resp-≈ₚ : ∀ {p q : EPath n} → p ≈ₚ q → length p ≡ length q
  length-resp-≈ₚ [ _ ]     = ≡-refl
  length-resp-≈ₚ (_ ∷ p≈q) = cong suc (length-resp-≈ₚ p≈q)


  ∉-resp-≈ₚ : ∀ {k} {p q : EPath n} → p ≈ₚ q → k ∉ p → k ∉ q
  ∉-resp-≈ₚ [ ≡-refl ]     (notThere i≢j)    = notThere i≢j
  ∉-resp-≈ₚ (≡-refl ∷ p≈q) (notHere k≉x k∉p) = notHere k≉x (∉-resp-≈ₚ p≈q k∉p)



  -----------------
  -- Enumeration --
  -----------------

  Fₛ : Setoid _ _
  Fₛ = ≡-setoid (Fin n)

  ℕₛ : Setoid _ _
  ℕₛ = ≡-setoid ℕ

  Pₛ : Setoid _ _
  Pₛ = ≈ₚ-setoid

  LPₛ : Setoid _ _
  LPₛ = list-setoid Pₛ

  open Any.Membership ℕₛ using () renaming (_∈_ to _∈ℕ_)
  open Any.Membership Pₛ using () renaming (_∈_ to _∈ₚ_; _∉_ to _∉ₚ_; ∈-resp-≈ to ∈ₚ-resp-≈ₚ)
  open Setoid LPₛ using () renaming (reflexive to ≈ₗₚ-reflexive)




  -- extensions

  extendAll-completeness : ∀ {i q i∉q ps} → q ∈ₚ ps → i ∷ q ∣ i∉q ∈ₚ extendAll ps i
  extendAll-completeness {i} {_} {i∉q} {p ∷ _} (here q≈p) with i ∉? p
  ... | no i∈p = contradiction (∉-resp-≈ₚ q≈p i∉q) i∈p
  ... | yes _  = here (≡-refl ∷ q≈p)
  extendAll-completeness {i} {ps = p ∷ _} (there q∈ps) with i ∉? p
  ... | no  _ = extendAll-completeness q∈ps
  ... | yes _ = there (extendAll-completeness q∈ps)

  extendAll-∈ : ∀ {i v} ps → v ∈ₚ extendAll ps i → ∃₂ λ q i∉q → v ≈ₚ i ∷ q ∣ i∉q
  extendAll-∈ []  ()
  extendAll-∈ {i} (p ∷ ps) v∈e[p∷ps] with i ∉? p
  ... | no  _   = extendAll-∈ ps v∈e[p∷ps]
  ... | yes i∉p with v∈e[p∷ps]
  ...   | here  v≈i∷p = p , i∉p , v≈i∷p
  ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]

  extendAll-∉ : ∀ {i} {q : EPath n} {i∉q ps} → All (q ≉ₚ_) ps → All (i ∷ q ∣ i∉q ≉ₚ_) (extendAll ps i)
  extendAll-∉ {_} [] = []
  extendAll-∉ {i} {ps = p ∷ ps} (q≉p ∷ q≉ps) with i ∉? p
  ... | no  i∈p = extendAll-∉ q≉ps
  ... | yes i∉p = (λ {(_ ∷ p≈q) → q≉p p≈q}) ∷ (extendAll-∉ q≉ps)

  extendAll! : ∀ {ps} → Unique Pₛ ps → ∀ i → Unique Pₛ (extendAll ps i)
  extendAll!       [] _ = []
  extendAll! {ps = p ∷ ps} (p∉ps ∷ ps!) i with i ∉? p
  ... | no  _ = extendAll! ps! i
  ... | yes _ = extendAll-∉ p∉ps ∷ extendAll! ps! i

  extendAll-length : ∀ {l ps} → All (λ p → length p ≡ l) ps → (i : Fin n) → All (λ p → length p ≡ suc l) (extendAll ps i)
  extendAll-length [] _ = []
  extendAll-length {ps = p ∷ ps} (|p|≡l ∷ |ps|≡l) i with i ∉? p
  ... | no i∈p = extendAll-length |ps|≡l i
  ... | yes _  = cong suc |p|≡l ∷ extendAll-length |ps|≡l i

  extendAll-disjoint : ∀ ps qs {i j} → i ≢ j → Disjoint Pₛ (extendAll ps i) (extendAll qs j)
  extendAll-disjoint ps qs i≢j (v∈extᵢps , v∈extⱼqs) with extendAll-∈ ps v∈extᵢps | extendAll-∈ qs v∈extⱼqs
  ... | _ , _ , v≈i∷p | _ , _ , v≈j∷q = (p₀≢q₀⇨p≉q i≢j) (≈ₚ-trans (≈ₚ-sym v≈i∷p) v≈j∷q)



  -- All paths of length l

  allPathsOfLength-completeness : ∀ p → p ∈ₚ (allPathsOfLength (length p))
  allPathsOfLength-completeness [ i ]       = ∈-map Fₛ Pₛ [_] (toList-preserves-∈ Fₛ (∈-allFin i))
  allPathsOfLength-completeness (i ∷ p ∣ _) = concat-∈ Pₛ (extendAll-completeness (allPathsOfLength-completeness p)) (∈-map Fₛ LPₛ (≈ₗₚ-reflexive ∘ (cong (extendAll (allPathsOfLength (length p))))) (toList-preserves-∈ Fₛ (∈-allFin i)))

  allPathsOfLength! : ∀ l → Unique Pₛ (allPathsOfLength l)
  allPathsOfLength! zero    = map! Fₛ Pₛ p₀≢q₀⇨p≉q (allFin! n)
  allPathsOfLength! (suc l) = concat! Pₛ (forced-map (extendAll! (allPathsOfLength! l)) (toListᵥ (allFin n))) (map-pairs (extendAll-disjoint (allPathsOfLength l) (allPathsOfLength l)) (allFin! n))

  allPathsOfLength-length : ∀ l → All (λ p → length p ≡ l) (allPathsOfLength l)
  allPathsOfLength-length zero    = forced-map (λ _ → ≡-refl) (toListᵥ (allFin n))
  allPathsOfLength-length (suc l) = concat-all (forced-map (extendAll-length (allPathsOfLength-length l)) (toListᵥ (allFin n)))

  l-resp-≈ₚ : ∀ l → ((_≡ l) ∘ length {n}) Respects _≈ₚ_
  l-resp-≈ₚ _ x≈y |x|≡l  = ≡-trans (length-resp-≈ₚ (≈ₚ-sym x≈y)) |x|≡l

  allPathsOfLength-disjoint : ∀ {l k} → l ≢ k → Disjoint Pₛ (allPathsOfLength l) (allPathsOfLength k)
  allPathsOfLength-disjoint {l} {k} l≢k (v∈pₗ , v∈pₖ) = l≢k (≡-trans (≡-sym (∈-All Pₛ (l-resp-≈ₚ l) (allPathsOfLength-length l) v∈pₗ)) (∈-All Pₛ (l-resp-≈ₚ k) (allPathsOfLength-length k) v∈pₖ))


  -- All paths

  allPaths-completeness : ∀ p → p ∈ₚ allPaths
  allPaths-completeness p = concat-∈ Pₛ (allPathsOfLength-completeness p) (∈-map ℕₛ LPₛ (≈ₗₚ-reflexive ∘ (cong allPathsOfLength)) (subst (_∈ℕ map toℕ (toListᵥ (allFin n))) (toℕ-fromℕ≤ (|p|<n p)) (∈-map Fₛ ℕₛ (cong toℕ) (toList-preserves-∈ Fₛ (∈-allFin (fromℕ≤ (|p|<n p)))))))

  allPaths! : Unique Pₛ allPaths
  allPaths! = concat! Pₛ (forced-map allPathsOfLength! (map toℕ (toListᵥ (allFin n)))) (map-pairs allPathsOfLength-disjoint (map! Fₛ ℕₛ (λ x≢y → x≢y ∘ toℕ-injective) (allFin! n)))


  isEnumeration : IsEnumeration Pₛ allPaths
  isEnumeration = record {
      unique = allPaths!;
      complete = allPaths-completeness
    }

  enumeration : Enumeration Pₛ
  enumeration = record {
      list = allPaths;
      isEnumeration = isEnumeration
    }
