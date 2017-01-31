open import Data.Nat using (ℕ; suc; zero; _⊓_; _⊔_)
open import Data.List using (List; []; _∷_; gfilter; map; foldr)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; inspect; [_]; refl; sym)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_on_; _∘_)

open import RoutingLib.Data.Graph.EPath using (EPath; [_]; _∷_∣_; notHere; notThere) renaming (_∉_ to _∉′_; _≈ₚ_ to _≈ₚ′_; _≤ₚ_ to _≤ₚ′_; length to length′; toList to toList′; toVec to toVec′; _≤ₗ_ to _≤ₗ′_; allPaths to allPaths′)
open import RoutingLib.Data.Graph using (Graph)
open import RoutingLib.Data.Graph
open import RoutingLib.Data.List.All using (Chain; _∷_; [])
open import RoutingLib.Data.Maybe.Properties using (just-injective)

module RoutingLib.Data.Graph.EGPath {a n} {A : Set a} where

  --------------------
  -- Path structure --
  --------------------

  data EGPath (G : Graph A n) : Set a
  data _∉_ {G : Graph A n} : Fin n → EGPath G → Set lzero
  source : ∀ {G} → EGPath G → Fin n

  data EGPath G where
    [_]   : Fin n → EGPath G
    _∷_∣_∣_ : ∀ i (p : EGPath G) → i ∉ p → (i , (source p)) ᵉ∈ᵍ G → EGPath G

  data _∉_ {G} where
    notThere : ∀ {i j}         → i ≢ j → i ∉ [ j ]
    notHere  : ∀ {i j p j∉p t} → i ≢ j → i ∉ p → i ∉ (j ∷ p ∣ j∉p ∣ t)

  source [ i ] = i
  source (i ∷ _ ∣ _ ∣ _) = i

  destination : ∀ {G} → EGPath G → Fin n
  destination [ i ] = i
  destination (_ ∷ p ∣ _ ∣ _) = destination p

  _∈_ : Fin n → ∀ {G} → EGPath G → Set _
  i ∈ G = ¬ (i ∉ G)


  -- Conversion

  toEPath : ∀ {G} → EGPath G → EPath n
  to∉′ : ∀ {G i} {p : EGPath G} → i ∉ p → i ∉′ (toEPath p)

  toEPath [ i ] = [ i ]
  toEPath (i ∷ p ∣ i∉p ∣ _) = i ∷ toEPath p ∣ to∉′ i∉p

  to∉′ (notThere i≢j) = notThere i≢j
  to∉′ (notHere i≢j i∉p) = notHere i≢j (to∉′ i∉p)


  to∉′′ : ∀ {G i} {p : EGPath G} → i ∉′ (toEPath p) → i ∉ p
  to∉′′ {p = [ _ ]}         (notThere i≢j)    = notThere i≢j
  to∉′′ {p = _ ∷ _ ∣ _ ∣ _} (notHere i≢j i∉p) = notHere i≢j (to∉′′ i∉p)



  fromEPath : EPath n → ∀ G → Maybe (EGPath G)
  from∉′ : ∀ {G i q} {p : EPath n} → i ∉′ p → fromEPath p G ≡ just q → i ∉ q

  fromEPath [ i ] _ = just [ i ]
  fromEPath (i ∷ p ∣ i∉p) G with fromEPath p G | inspect (fromEPath p) G
  ... | nothing | _ = nothing
  ... | just p′ | [ from≡p ] with (i , source p′) ᵉ∈ᵍ? G
  ...   | no  _   = nothing
  ...   | yes e∈G = just (i ∷ p′ ∣ from∉′ i∉p from≡p ∣ e∈G)

  from∉′ {_} {_} {q} (notThere i≢j ) justᵢ≡justⱼ rewrite (sym (just-injective justᵢ≡justⱼ)) = notThere i≢j
  from∉′ {G} {_} {_} {j ∷ p ∣ j∉p} (notHere i≢j i∉p) x with fromEPath p G | inspect (fromEPath p) G
  ... | nothing | _ = contradiction x (λ())
  ... | just p′ | [ from≡p ] with (j , source p′) ᵉ∈ᵍ? G
  ...   | no _ = contradiction x (λ())
  ...   | yes e∈G rewrite (sym (just-injective x)) = notHere i≢j (from∉′ i∉p from≡p)



  -- Equality over paths

  infix 4 _≈ₚ_ _≉ₚ_

  open import RoutingLib.Data.Graph.EPath using ([_]; _∷_) public

  _≈ₚ_ : ∀ {G} → Rel (EGPath G) lzero
  _≈ₚ_ = _≈ₚ′_ on toEPath

  _≉ₚ_ : ∀ {G} → Rel (EGPath G) lzero
  p ≉ₚ q = ¬ (p ≈ₚ q)



  -- Lexicographic omparison between paths

  infix 4 _≤ₚ_ _≰ₚ_

  open import RoutingLib.Data.Graph.EPath using (stop; stopLeft; stopRight; stepEqual; stepUnequal) public

  _≤ₚ_ : ∀ {G} → Rel (EGPath G) lzero
  _≤ₚ_ = _≤ₚ′_ on toEPath

  _≰ₚ_ : ∀ {G} → Rel (EGPath G) lzero
  p ≰ₚ q = ¬ (p ≤ₚ q)



  -- Length comparison between paths

  infix 4 _≤ₗ_ _≰ₗ_

  _≤ₗ_ : ∀ {G} → Rel (EGPath G) lzero
  _≤ₗ_ = _≤ₗ′_ on toEPath

  _≰ₗ_ : ∀ {G} → Rel (EGPath G) lzero
  p ≰ₗ q = ¬ (p ≤ₗ q)


  -- Other operations

  length : ∀ {G} → EGPath G → ℕ
  length = length′ ∘ toEPath

  toList : ∀ {G} → EGPath G → List (Fin n)
  toList = toList′ ∘ toEPath

  toVec : ∀ {G} → (p : EGPath G) → Vec (Fin n) (suc (length p))
  toVec = toVec′ ∘ toEPath

  weight : ∀ {b} {B : Set b} → (A → B → B) → B → ∀ {G} → EGPath G → B
  weight _▷_ 1# [ i ] = 1#
  weight _▷_ 1# (_ ∷ p ∣ _ ∣ (v , _)) = v ▷ weight _▷_ 1# p

  allPaths : ∀ G → List (EGPath G)
  allPaths G = gfilter (λ p → fromEPath p G) allPaths′


  truncateAt : ∀ {G} {p : EGPath G} {i} → i ∈ p → EGPath G
  truncateAt {p = [ j ]}         _      = [ j ]
  truncateAt {p = j ∷ p ∣ j∉p ∣ e∈G} {i} i∈j∷p with i ≟ j
  ... | yes i≡j = j ∷ p ∣ j∉p ∣ e∈G
  ... | no  i≢j = truncateAt (i∈j∷p ∘ notHere i≢j)


  isPathBetween : ∀ {G} → Fin n → Fin n → EGPath G → Maybe (EGPath G)
  isPathBetween src dst p with source p ≟ src | destination p ≟ dst
  ... | no _  | _     = nothing
  ... | _     | no _  = nothing
  ... | yes _ | yes _ = just p

  allPathsBetween : ∀ G → Fin n → Fin n → List (EGPath G)
  allPathsBetween G src dst = gfilter (isPathBetween src dst) (allPaths G)

  diameterBetween : ∀ G → Fin n → Fin n → ℕ
  diameterBetween G src dst = foldr _⊔_ zero (map length (allPathsBetween G src dst))
