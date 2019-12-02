
open import RoutingLib.Routing using (AdjacencyMatrix)
open import RoutingLib.Routing.Algebra

module RoutingLib.Routing.VectorBased.Asynchronous.Convergence.ExtensionRespectingOrder
  {a b ℓ}
  (alg : RawRoutingAlgebra a b ℓ)
  {n} (A : AdjacencyMatrix alg n) where

open RawRoutingAlgebra alg

open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin; suc; inject₁)
open import Data.Fin.Patterns
open import Data.List hiding ([_])
open import Data.List.Membership.Setoid S
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Product as Product using (∃; ∃₂; _,_; proj₁; proj₂; _×_)
open import Data.Maybe
open import Data.Maybe.Relation.Unary.Any
open import Data.Maybe.Relation.Unary.All as All
open import Data.List.Relation.Binary.Sublist.Setoid S
open import Data.List.Relation.Binary.Sublist.Setoid.Properties S
open import Data.Unit using (tt)
open import Function
open import Induction.WellFounded using (WellFounded; Acc; acc)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.Construct.Union as Union using (_∪_)
open import Relation.Binary.Construct.Closure.Transitive as TransClosure
  renaming (Plus′ to TransitiveClosure) hiding ([_]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

open import RoutingLib.Routing alg n
open import RoutingLib.Routing.Extensions alg A

open import RoutingLib.Data.Fin using (_+ₘ_; _-ₘ_)
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid S
open import RoutingLib.Data.List.Relation.Binary.Sublist.Setoid.Properties S
open import RoutingLib.Data.FiniteSet renaming (FiniteSet to FiniteSet⁺)
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid using (Finite)
open import RoutingLib.Data.Maybe.Properties
open import RoutingLib.Relation.Binary using (StrictMinimum)
import RoutingLib.Relation.Binary.Construct.Union as Union
import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Finite as TransClosure
import RoutingLib.Relation.Binary.Construct.Closure.Transitive as TransClosure

--------------------------------------------------------------------------------
-- Introduction
--------------------------------------------------------------------------------

-- It occured to me (whilst programming dropdown boxes in Java) that what
-- determines whether or not we have a suitable height function on which our
-- entire proof in the SIGCOMM paper is based, is whether or not we have a
-- strict partial order over the routes which respects the extension,
-- i.e. x < Aᵢⱼ(x).

-- Obviously when the algebra is strictly contracting this is trivial and we
-- use _<₊_. However for free networks over non-strictly increasing algebras
-- we still get the strictly contracting part for free from _<₊_ and all we
-- have to do is tweak it to recover the `respect extensions` part. After
-- checking in Sobrinho's 2005 paper, the dispute digraph bit in the appendix
-- can easily be taken, generalised and then repurposed almost trivially.
-- I say trivial as it's only 8 small lemmas in Agda, which if that's not
-- trivial I'm not sure what is!

record IsExtensionRespectingOrder {ℓ₂} (_<_ : Rel Route ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_
    ↝⇒<                     : _↝_  ⇒ _<_
    <₊⇒<                    : _<₊_ ⇒ _<_
    <-min                   : StrictMinimum _≈_ _<_ 0#

  open IsDecStrictPartialOrder isDecStrictPartialOrder public
  
record ExtensionRespectingOrder ℓ₂ : Set (a ⊔ ℓ ⊔ lsuc ℓ₂) where
  field
    _<_                        : Rel Route ℓ₂
    isExtensionRespectingOrder : IsExtensionRespectingOrder _<_

  open IsExtensionRespectingOrder isExtensionRespectingOrder public

--------------------------------------------------------------------------------
-- Cycle-free networks implies ExtensionRespectingOrder
--------------------------------------------------------------------------------

module _ (isRoutingAlgebra : IsRoutingAlgebra alg) where

  open IsRoutingAlgebra isRoutingAlgebra
  open import RoutingLib.Routing.Algebra.Properties.RoutingAlgebra isRoutingAlgebra
  open import Relation.Binary.Reasoning.PartialOrder ≤₊-poset

  -- In order to define a free network, we first define the dominates relation.
  -- Route x is dominated by y if there exists some extension of x that is
  -- preferred over y.
  _⊴_ : Rel Route ℓ
  x ⊴ y = ∃₂ λ k j → A k j ▷ x ≤₊ y

  -- The definition of cyclic from `RoutingLib.Routing` is then:
  -- A non-empty set of routes X is cyclic if every route in it dominates the
  -- previous one (modulo the size of the set).

  -- If x is dominated by y and y is preferred to z then x is dominated by z.
  ⊴-≤₊-trans : Trans _⊴_ _≤₊_ _⊴_
  ⊴-≤₊-trans (k , j , Aₖⱼ▷x≤y) y≤z = k , j , ≤₊-trans Aₖⱼ▷x≤y y≤z

  -- Extended by trivially implies domination.
  ↝⇒⊴ : _↝_ ⇒ _⊴_
  ↝⇒⊴ (i , j , Aᵢⱼ▷x≈y) = i , j , ≤₊-reflexive Aᵢⱼ▷x≈y

  --------------------------------------------------------------------------------
  -- An ordering over routes
  --------------------------------------------------------------------------------
  -- In order to build a height function all we need to have is a
  -- strict partial order over routes with the property `x < Aᵢⱼ(x)`. When
  -- the algebra is strictly increasing this is simply `_<₊_`. However when the
  -- network is cycle free we must come up with something more complicated. The
  -- hard part is proving that any such order is irreflexive, i.e. it has no
  -- cycles in it.

  -- The relation below is a generalisation of the dispute digraph. It says that
  -- route `x` is less than route `y` if there exists some path of either
  -- `<₊ = is preferred to` or `↝ = can be extended to` relations between them.
  -- It is more general than the dispute digraph as used by both Griffin and
  -- Sobrinho, as a) it doesn't require all the routes to have the same source
  -- (something not easily expressible in an algebra) and b) it weakens
  -- distributivity violation links to merely `can be extended to` links.

  infix 4 _<ᶠ_

  _<ᶠ_ : Rel Route (a ⊔ ℓ)
  _<ᶠ_ = TransitiveClosure (_<₊_ ∪ _↝_)

  -- Given two related routes, i.e. path through this graph, we identify the set
  -- of routes that are extended. If extensions exist in the path we return
  -- nothing, otherwise we return a non-empty set of routes.
  ⟦_⟧↝ : ∀ {x y} → x <ᶠ y → Maybe (FiniteSet⁺ Route)
  ⟦_⟧↝ {x} [ inj₁ x<y ]     = nothing
  ⟦_⟧↝ {x} [ inj₂ x↝y ]     = just ⟦ x ⟧
  ⟦_⟧↝ {x} (inj₁ x<z ∷ z<y) = ⟦ z<y ⟧↝
  ⟦_⟧↝ {x} (inj₂ x↝z ∷ z<y) with ⟦ z<y ⟧↝
  ... | nothing = just ⟦ x ⟧
  ... | just t  = just (⟦ x ⟧∪ t)

  -- If the set of extended routes are empty then the first route in the
  -- path must be strictly preferred to the last route in the path.
  ¬⟦x<ᶠy⟧↝⇒x<y : ∀ {x y} (x<y : x <ᶠ y) → ¬ Is-just ⟦ x<y ⟧↝ → x <₊ y
  ¬⟦x<ᶠy⟧↝⇒x<y [ inj₁ x<y ]     _  = x<y
  ¬⟦x<ᶠy⟧↝⇒x<y [ inj₂ x<y ]     v  = contradiction (just tt) v
  ¬⟦x<ᶠy⟧↝⇒x<y (inj₁ x<y ∷ y<z) eq = <₊-trans x<y (¬⟦x<ᶠy⟧↝⇒x<y y<z eq)
  ¬⟦x<ᶠy⟧↝⇒x<y (inj₂ x<y ∷ y<z) eq with ⟦ y<z ⟧↝
  ... | nothing = contradiction (just tt) eq
  ... | just _  = contradiction (just tt) eq

  -- If some route `v` is preferred to the start point of the path then `v` must also
  -- be preferred to the first extended route in the path (if it exists).
  v≤x⇒v≤⟦x<ᶠy⟧↝₀ : ∀ {v x y} → v ≤₊ x → (x<ᶠy : x <ᶠ y) → All (λ w → v ≤₊ first w) ⟦ x<ᶠy ⟧↝
  v≤x⇒v≤⟦x<ᶠy⟧↝₀ v≤x [ inj₁ _ ]        = nothing
  v≤x⇒v≤⟦x<ᶠy⟧↝₀ v≤x [ inj₂ _ ]        = just v≤x
  v≤x⇒v≤⟦x<ᶠy⟧↝₀ v≤x (inj₁ x<z ∷ z<ᶠy) = v≤x⇒v≤⟦x<ᶠy⟧↝₀ (≤₊-trans v≤x (proj₁ x<z)) z<ᶠy
  v≤x⇒v≤⟦x<ᶠy⟧↝₀ v≤x (inj₂ x↝z ∷ z<ᶠy) with ⟦ z<ᶠy ⟧↝
  ... | nothing = just v≤x
  ... | just _  = just v≤x

  -- If the end point of the path is preferred to some route `v` then last extended route
  -- in the path (if it exists) must be dominated by `v`.
  y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v : ∀ {v x y} → y ≤₊ v → (x<ᶠy : x <ᶠ y) → All (λ w → last w ⊴ v) ⟦ x<ᶠy ⟧↝
  y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v y≤v [ inj₁ x<y ]      = nothing
  y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v y≤v [ inj₂ x↝y ]      = just (⊴-≤₊-trans (↝⇒⊴ x↝y) y≤v)
  y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v y≤v (inj₁ x<z ∷ z<ᶠy) = y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v y≤v z<ᶠy
  y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v {v} y≤v (inj₂ x↝w ∷ w<ᶠy) with ⟦ w<ᶠy ⟧↝ | inspect ⟦_⟧↝ w<ᶠy
  ... | nothing | [ eq ] = just (⊴-≤₊-trans (↝⇒⊴ x↝w) (≤₊-trans (proj₁ (¬⟦x<ᶠy⟧↝⇒x<y w<ᶠy (subst (λ v → ¬ Is-just v) (sym eq) λ()))) y≤v)) 
  ... | just q  | [ eq ] = just (subst (λ v → last v ⊴ _) (to-witness-subst eq) (All-witness test (y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v y≤v w<ᶠy)))
    where
    test : Is-just ⟦ w<ᶠy ⟧↝
    test = subst Is-just (sym eq) (just {x = q} tt)

  -- The iᵗʰ extended route in the path is dominated by i+1ᵗʰ extended route in the path
  ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ : ∀ {x y} (x<ᶠy : x <ᶠ y) → All (λ v → (∀ i → iᵗʰ v (inject₁ i) ⊴ iᵗʰ v (suc i))) ⟦ x<ᶠy ⟧↝
  ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₁ _ ]         = nothing
  ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ [ inj₂ _ ]         = just λ()
  ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ (inj₁ x<z ∷ z<ᶠy)  = ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy
  ⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ {x} {y} (_∷_ {y = z} (inj₂ x↝z) z<ᶠy)  with ⟦ z<ᶠy ⟧↝ | inspect ⟦_⟧↝ z<ᶠy 
  ... | nothing | _      = just λ()
  ... | just v  | [ eq ] = just λ
    -- Please don't ask about this monstrosity. Horrible hacks around definitional equality of `to-witness`
    { 0F      → ⊴-≤₊-trans (↝⇒⊴ x↝z) (subst (λ q → z ≤₊ FiniteSet⁺.x q 0F) (to-witness-subst eq) (All-witness test (v≤x⇒v≤⟦x<ᶠy⟧↝₀ ≤₊-refl z<ᶠy)))
    ; (suc i) → subst (λ v → ∀ i → iᵗʰ v (inject₁ i) ⊴ iᵗʰ v (suc i)) (to-witness-subst eq) (All-witness test (⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ z<ᶠy)) i
    }
    where
    test : Is-just ⟦ z<ᶠy ⟧↝
    test = subst Is-just (sym eq) (just {x = v} tt)

  -- When the network is cycle free then irreflexivity can now be proved. This follows
  -- as if the start point of the path is equal to the end point then:
  --   ∙ if the path contains no extensions then x ≈ y and x <₊ y which is contradiction
  --     by the irreflexivity of _<₊_
  --   ∙ if the path does contain extensions then the set of extended routes must form
  --     a cycle thanks to x ≈ y and the previous lemmas.
  <ᶠ-irrefl : CycleFree A → Irreflexive _≈_ _<ᶠ_
  <ᶠ-irrefl cf x≈y x<ᶠy with IsJust? ⟦ x<ᶠy ⟧↝
  ... | no  ¬∣x<ᶠy∣↝ = <₊-irrefl x≈y (¬⟦x<ᶠy⟧↝⇒x<y x<ᶠy ¬∣x<ᶠy∣↝)
  ... | yes ∣x<ᶠy∣↝  = cf (to-witness ∣x<ᶠy∣↝) ∣x<ᶠy∣↝-cyclic
    where
    ⟦x<ᶠy⟧₋₁⊴x        = All-witness ∣x<ᶠy∣↝ (y≤v⇒⟦x<ᶠy⟧↝₋₁⊴v ≤₊-refl x<ᶠy)
    x≤⟦x<ᶠy⟧₀         = All-witness ∣x<ᶠy∣↝ (v≤x⇒v≤⟦x<ᶠy⟧↝₀ (≤₊-reflexive (≈-sym x≈y)) x<ᶠy)
    ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁ = All-witness ∣x<ᶠy∣↝ (⟦y<ᶠz⟧↝ᵢ⊴⟦y<ᶠz⟧↝ᵢ₊₁ x<ᶠy)

    ∣x<ᶠy∣↝-cyclic : Cyclic A (to-witness ∣x<ᶠy∣↝)
    ∣x<ᶠy∣↝-cyclic 0F      = ⊴-≤₊-trans ⟦x<ᶠy⟧₋₁⊴x x≤⟦x<ᶠy⟧₀
    ∣x<ᶠy∣↝-cyclic (suc i) = ⟦x<ᶠy⟧ᵢ⊴⟦x<ᶠy⟧ᵢ₊₁ i

  <ᶠ-trans : Transitive _<ᶠ_
  <ᶠ-trans = TransClosure.trans

  <ᶠ-respʳ-≈ : _<ᶠ_ Respectsʳ _≈_
  <ᶠ-respʳ-≈ = TransClosure.R⁺-respʳ-≈ (Union.respʳ _<₊_ _↝_ <₊-respʳ-≈ ↝-respʳ-≈)

  <ᶠ-respˡ-≈ : _<ᶠ_ Respectsˡ _≈_
  <ᶠ-respˡ-≈ = TransClosure.R⁺-respˡ-≈ (Union.respˡ _<₊_ _↝_ <₊-respˡ-≈ ↝-respˡ-≈)

  <ᶠ-resp-≈ : _<ᶠ_ Respects₂ _≈_
  <ᶠ-resp-≈ = <ᶠ-respʳ-≈ , <ᶠ-respˡ-≈

  <ᶠ-dec : Finite S → Decidable _<ᶠ_
  <ᶠ-dec fin = TransClosure.R⁺? {S = S} fin (Union.resp₂ <₊-resp-≈ ↝-resp-≈) (Union.decidable _<₊?_ _↝?_)

  <ᶠ-min : StrictMinimum _≈_ _<ᶠ_ 0#
  <ᶠ-min {x} 0≉x = [ inj₁ (≤₊-minimum x , 0≉x) ]

  <₊⇒<ᶠ : _<₊_ ⇒ _<ᶠ_
  <₊⇒<ᶠ x<y = [ inj₁ x<y ]

  -- And importantly `x` is strictly less than `Aᵢⱼ(x)` even though the algebra
  -- is not necessarily strictly increasing.
  ↝⇒<ᶠ : _↝_ ⇒ _<ᶠ_
  ↝⇒<ᶠ x↝y = [ inj₂ x↝y ]


  <ᶠ-isStrictPartialOrder : CycleFree A → IsStrictPartialOrder _≈_ _<ᶠ_
  <ᶠ-isStrictPartialOrder cf = record
    { isEquivalence = ≈-isEquivalence
    ; irrefl        = <ᶠ-irrefl cf
    ; trans         = <ᶠ-trans
    ; <-resp-≈      = <ᶠ-resp-≈
    }

  <ᶠ-isDecStrictPartialOrder : IsFinite alg → CycleFree A → IsDecStrictPartialOrder _≈_ _<ᶠ_
  <ᶠ-isDecStrictPartialOrder fin cf = record
    { isStrictPartialOrder = <ᶠ-isStrictPartialOrder cf
    ; _≟_                  = _≟_
    ; _<?_                 = <ᶠ-dec fin
    }

  <ᶠ-isExtensionRespectingOrder : IsFinite alg → CycleFree A → IsExtensionRespectingOrder _<ᶠ_
  <ᶠ-isExtensionRespectingOrder fin cf = record
    { isDecStrictPartialOrder = <ᶠ-isDecStrictPartialOrder fin cf
    ; ↝⇒<                     = ↝⇒<ᶠ
    ; <₊⇒<                    = <₊⇒<ᶠ
    ; <-min                   = <ᶠ-min
    }

  <ᶠ-extensionRespectingOrder : IsFinite alg → CycleFree A → ExtensionRespectingOrder _
  <ᶠ-extensionRespectingOrder fin cf = record
    { _<_                        = _<ᶠ_
    ; isExtensionRespectingOrder = <ᶠ-isExtensionRespectingOrder fin cf
    }

  --------------------------------------------------------------------------------
  -- Height function
  --------------------------------------------------------------------------------
  -- Using the above ordering the height function is now trivial to define for
  -- cycle free networks over finite algebra.

  -- The rest of the proof of convergence
  --   ∙ construction of height + distance functions
  --   ∙ proof that they're strictly contracting
  --   ∙ extension to infinite path algebras
  --   ∙ lifting to our dynamic asynchronous model
  -- we get for free as it's identical to that in our SIGCOMM paper, **YAY!**
