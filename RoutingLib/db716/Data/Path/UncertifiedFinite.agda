open import Data.Nat using (ℕ; suc; _≤_; s≤s; _⊓_) renaming (_*_ to _×ₙ_)
open import Data.Nat.Properties using (≰⇒>; n≤1+n; ≤-reflexive; <-trans)
open import Data.Fin using (Fin; inject₁; _≟_; punchOut; punchIn; _<_; _<?_; reduce≥) renaming (suc to fsuc)
open import Data.Fin.Properties using (pigeonhole; ≤∧≢⇒<; inject₁-injective)
open import Data.List using (List; []; _∷_; _++_; foldl; foldr; map; concat; length; lookup; zip)
open import Data.List.Relation.Unary.Any using (Any; here; there; any; index) renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; tabulate)
open import Data.List.Properties
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-≡⇒≡) renaming (refl to ≈ₚ-refl)
open import Data.List.Membership.Propositional using (_∈_; find; mapWith∈; lose)
open import Data.List.Membership.Propositional.Properties using (∈-lookup; ∈-∃++)
open import Data.Product using (_×_; _,_; <_,_>; proj₁; proj₂; ∃; ∃₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡⇒≡×≡; ≡×≡⇒≡)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Algebra using (Semiring)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong₂) renaming (refl to ≡-refl; cong to ≡-cong; sym to ≡-sym)
open import RoutingLib.Data.Matrix.Relation.Binary.Equality using (_≈ₘ_)

module RoutingLib.db716.Data.Path.UncertifiedFinite where

Vertex : ℕ → Set 
Vertex n = Fin n

Edge : ℕ → Set
Edge n = Vertex n × Vertex n

Path : ℕ → Set
Path n = List (Edge n)


infix 4 _∈ₑ_ _∈ₚ_ _∉ₚ_

data _∈ₑ_ : ∀ {n} → Vertex n → Edge n → Set where
  left : ∀ {n} {i j : Fin n} → i ∈ₑ (i , j)
  right : ∀ {n} {i j : Fin n} → j ∈ₑ (i , j)

_∈ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∈ₚ p = Any (i ∈ₑ_) p

_∉ₚ_ : ∀ {n} → Vertex n → Path n → Set
i ∉ₚ p = ¬ (i ∈ₚ p)

infix 4 _⇿_

data _⇿_ : ∀ {n} → Edge n → Path n → Set where
  start : ∀ {n} {i j : Fin n} → (i , j) ⇿ []
  continue : ∀ {n} {i j k : Fin n} {p : Path n} → (i , j) ⇿ (j , k) ∷ p

data ValidPath {n} : Path n → Set where
  [] : ValidPath []
  _∷_ : {e : Edge n} {p : Path n} → e ⇿ p → ValidPath p → ValidPath (e ∷ p)

infix 4 _≈ₚ_ _≉ₚ_

_≈ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
_≈ₚ_ {n} = Pointwise _≡_

_≉ₚ_ : ∀ {n} → Rel (Path n) ℓ₀
p ≉ₚ q = ¬ (p ≈ₚ q)

-- Maybe I should add a proof of (e ⇿ p) as a parameter here
data HasLoop {n : ℕ} : (p : Path n) → Set where
  trivial : {p : Path n} {b : Vertex n} → HasLoop ((b , b) ∷ p)
  here : {p : Path n} {a b c : Vertex n} → (a , b) ∈ p → HasLoop ((b , c) ∷ p)
  there : {p : Path n} {e : Edge n} → HasLoop p → HasLoop (e ∷ p)

cutLoopAux : {n : ℕ} (e : Edge n) (p : Path n) → e ∈ p → Path n
cutLoopAux e (e' ∷ p) (here e≡e') = p
cutLoopAux e (e' ∷ p) (there e∈p) = cutLoopAux e p e∈p

cutLoop : {n : ℕ} (p : Path n) → HasLoop p → Path n
cutLoop p (trivial {p'}) = p'
cutLoop {n} ((b , c) ∷ e ∷ p) (here {_} {a} [a,b]∈e∷p) = cutLoopAux (a , b) (e ∷ p) [a,b]∈e∷p
cutLoop (e ∷ p) (there pHasLoop) = e ∷ (cutLoop p pHasLoop)


allFins : ∀ n → List (Fin n)
allFins ℕ.zero = []
allFins (suc n) = Fin.zero ∷ (Data.List.map Fin.suc (allFins n))

addVertex : ∀ {n} → Fin n → Path n → Path n
addVertex {n} v [] = (v , v) ∷ []
addVertex {n} v ((w , t) ∷ p) = (v , w) ∷ (w , t) ∷ p

_▻_ = addVertex

_▻*_ : ∀ {n} → Fin n → List (Path n) → List (Path n)
i ▻* l = map (i ▻_) l

data PathFrom {n : ℕ} (i : Fin n) : Path n → Set where
--  empty : PathFrom i []
  here : {j : Fin n} {p : Path n} → PathFrom i ((i , j) ∷ p)

data PathTo {n : ℕ} (j : Fin n) : Path n → Set where
--  empty : PathTo j []
  here : {i : Fin n} → PathTo j ((i , j) ∷ [])
  there : {e : Edge n} {p : Path n} → PathTo j p → PathTo j (e ∷ p)

all-k-length-paths-from-to : ∀ n → ℕ → (Vertex n) → (Vertex n) → List (Path n)
all-k-length-paths-to : ∀ n → ℕ → (Vertex n) → List (Path n)

all-k-length-paths-from-to ℕ.zero k ()
all-k-length-paths-from-to (suc n) ℕ.zero u v with (u ≟ v)
... | (yes _) = [] ∷ []
... | (no _) = []
all-k-length-paths-from-to (suc n) (suc 0) u v = ((u , v) ∷ []) ∷ []
all-k-length-paths-from-to (suc n) (suc (suc k)) u v = Data.List.map (addVertex u) (all-k-length-paths-to (suc n) (suc k) v)

all-all-k-length-paths-from-to : ∀ n → ℕ → Fin n → List (List (Path n))
all-all-k-length-paths-from-to (suc n) k v = Data.List.map (λ u → all-k-length-paths-from-to (suc n) k u v) (allFins (suc n))

all-k-length-paths-to (suc n) k v = concat (all-all-k-length-paths-from-to (suc n) k v)

all-≤k-length-paths-from-to : ∀ n → ℕ → Vertex n → Vertex n → List (Path n)
all-≤k-length-paths-from-to n 0 i j with i ≟ j
... | yes i≡j = [] ∷ []
... | no i≢j = []
all-≤k-length-paths-from-to n (suc k) i j = all-≤k-length-paths-from-to n k i j ++ all-k-length-paths-from-to n (suc k) i j
