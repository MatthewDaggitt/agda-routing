open import Data.Nat using (ℕ; suc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<_ to _<ℕ_)
open import Data.Nat.Properties using (<-trans)
open import Data.Fin using (Fin; _<_; toℕ; fromℕ≤) renaming (suc to fsuc)
open import Data.Fin.Properties using (_≟_;  toℕ-injective; toℕ-fromℕ≤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map; concat)
open import Data.List.Any as Any using (here; there)
open import Data.List.All using (All; []; _∷_)
open import Data.Product using (∃; ∃₂; _×_; _,_)
open import Relation.Binary using (Decidable; Setoid; Total; Reflexive; Symmetric; Antisymmetric; Transitive; IsEquivalence; tri≈; tri<; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; setoid)
open import Relation.Binary.List.Pointwise using () renaming (setoid to list-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)

open import RoutingLib.Data.Graph
open import RoutingLib.Data.Graph.SGPath
open import RoutingLib.Data.Graph.SGPath.Properties
open import RoutingLib.Data.Nat.Properties using (<⇒≢; <⇒≯; ≤-refl; m+n≮n; m+1+n≢n; suc-injective) renaming (cmp to ≤ℕ-cmp)
open import RoutingLib.Data.Fin.Properties using (≤-trans; ≤-antisym; ≤-total; _≤?_; _<?_; cmp)
open import RoutingLib.Relation.Binary.RespectedBy using (_RespectedBy_)
open import RoutingLib.Data.List using (allFin; combine)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.All.Properties using (forced-map; concat-all; map-pairs; All-∈)
open import RoutingLib.Data.List.All.Uniqueness using (Unique)
open import RoutingLib.Data.List.All.Uniqueness.Properties using (map!; concat!; combine!; allFin!)
open import RoutingLib.Data.List.Any.GenericMembership using (Disjoint; disjoint-[]; ∈-resp-≈; toList-preserves-∈; ∈-concat; ∈-map)
open import RoutingLib.Data.List.Any.PropositionalMembership using (∈-allFin; ∈-combine)
open import RoutingLib.Data.List.Enumeration


module RoutingLib.Data.Graph.SGPath.Enumerate {a n} {A : Set a} (G : Graph A n) where


  -- Enumeration

  filterValidEdges : List (Fin n × Fin n) → List (NonEmptySGPath G)
  filterValidEdges [] = []
  filterValidEdges ((i , j) ∷ xs) with i ≟ j | (i , j) ᵉ∈ᵍ? G
  ... | yes _  | _        = filterValidEdges xs
  ... | _      | no  _    = filterValidEdges xs
  ... | no i≢j | yes ij∈G = i ∺ j ∣ i≢j ∣ ij∈G ∷ filterValidEdges xs

  extendAll : List (NonEmptySGPath G) → Fin n → List (NonEmptySGPath G)
  extendAll []       _ = []
  extendAll (p ∷ ps) i with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
  ... | no  _   | _        = extendAll ps i
  ... | _       | no  _    = extendAll ps i
  ... | yes i∉p | yes ip∈G = i ∷ p ∣ i∉p ∣ ip∈G ∷ extendAll ps i

  allNEPathsOfLength : ℕ → List (NonEmptySGPath G)
  allNEPathsOfLength 0       = []
  allNEPathsOfLength 1       = filterValidEdges (combine _,_ (allFin n) (allFin n))
  allNEPathsOfLength (suc l) = concat (map (extendAll (allNEPathsOfLength l)) (allFin n))

  allNEPaths : List (NonEmptySGPath G)
  allNEPaths = concat (map (allNEPathsOfLength) (map toℕ (allFin n)))

  allPaths : List (SGPath G)
  allPaths = [] ∷ map [_] (allNEPaths)

  ------------
  -- Proofs --
  ------------

  private

    Fₛ : Setoid _ _
    Fₛ = setoid (Fin n)

    F×Fₛ : Setoid _ _
    F×Fₛ = setoid (Fin n × Fin n)

    ℕₛ : Setoid _ _
    ℕₛ = setoid ℕ

    Pₛ' : Setoid _ _
    Pₛ' = Pₛ G

    NEPₛ' : Setoid _ _
    NEPₛ' = NEPₛ G

    LNEPₛ : Setoid _ _
    LNEPₛ = list-setoid NEPₛ'

    open Any.Membership ℕₛ using () renaming (_∈_ to _∈ℕ_; ∈-resp-≈ to ∈ℕ-resp-≡)
    open Any.Membership Pₛ' using () renaming (_∈_ to _∈ₗₚ_)
    open Any.Membership F×Fₛ using () renaming (_∈_ to _∈ᶠ_)
    open Any.Membership NEPₛ' using () renaming (_∈_ to _∈ₗₙₑₚ_; _∉_ to _∉ₗₙₑₚ_; ∈-resp-≈ to ∈ₗₚ-resp-≈ₗₙₑₚ)
    open Setoid LNEPₛ using () renaming (reflexive to ≈ₗₙₑₚ-reflexive)

    w≢y⊎x≢z⇒wx≢yz : ∀ {w x y z : Fin n} → w ≢ y ⊎ x ≢ z → (w , x) ≢ (y , z)
    w≢y⊎x≢z⇒wx≢yz (inj₁ w≢w) refl = w≢w refl
    w≢y⊎x≢z⇒wx≢yz (inj₂ w≢w) refl = w≢w refl




  abstract

    |p|∈allFin : ∀ (p : NonEmptySGPath G) → length p ∈ℕ map toℕ (allFin n)
    |p|∈allFin p = ∈-resp-≈ ℕₛ (∈-map ℕₛ Fₛ (cong toℕ) (∈-allFin (fromℕ≤ (|p|<n p)))) (toℕ-fromℕ≤ (|p|<n p))

    -- filterValidEdges

    ∈-filterValidEdges : ∀ {i j} i≢j ij∈G {xs} → (i , j) ∈ᶠ xs → i ∺ j ∣ i≢j ∣ ij∈G ∈ₗₙₑₚ filterValidEdges xs
    ∈-filterValidEdges {i} {j} i≢j ij∈G (here refl) with i ≟ j | (i , j) ᵉ∈ᵍ? G
    ... | yes i≡j | _       = contradiction i≡j i≢j
    ... | no  _   | no ij∉G = contradiction ij∈G ij∉G
    ... | no  _   | yes _   = here (refl ∺ refl)
    ∈-filterValidEdges i≢j ij∈G {(k , l) ∷ _} (there ij∈xs) with k ≟ l | (k , l) ᵉ∈ᵍ? G
    ... | yes _ | _     = ∈-filterValidEdges i≢j ij∈G ij∈xs
    ... | no  _ | no  _ = ∈-filterValidEdges i≢j ij∈G ij∈xs
    ... | no  _ | yes _ = there (∈-filterValidEdges i≢j ij∈G ij∈xs)

    filterValidEdges-≉ : ∀ {i j} i≢j ij∈G {xs} → All ((i , j) ≢_) xs → All (i ∺ j ∣ i≢j ∣ ij∈G ≉ₙₑₚ_) (filterValidEdges xs)
    filterValidEdges-≉ {i} {j} i≢j ij∈G [] = []
    filterValidEdges-≉ {i} {j} i≢j ij∈G {(k , l) ∷ xs} (ij≢kl ∷ pxs) with k ≟ l | (k , l) ᵉ∈ᵍ? G
    ... | yes i≡j | _       = filterValidEdges-≉ i≢j ij∈G pxs
    ... | no  _   | no ij∉G = filterValidEdges-≉ i≢j ij∈G pxs
    ... | no  _   | yes _   = (λ {(i≡k ∺ j≡l) → ij≢kl (cong₂ _,_ i≡k j≡l)}) ∷ filterValidEdges-≉ i≢j ij∈G pxs

    filterValidEdges! : ∀ {xs} → Unique F×Fₛ xs → Unique NEPₛ' (filterValidEdges xs)
    filterValidEdges! {[]} [] = []
    filterValidEdges! {(i , j) ∷ xs} (ij∉xs ∷ xs!) with i ≟ j | (i , j) ᵉ∈ᵍ? G
    ... | yes _   | _        = filterValidEdges! xs!
    ... | no  _   | no  _    = filterValidEdges! xs!
    ... | no  i≢j | yes ij∈G = filterValidEdges-≉ i≢j ij∈G ij∉xs ∷ filterValidEdges! xs!

    filterValidEdges-length : ∀ xs → All (λ p → length p ≡ 1) (filterValidEdges xs)
    filterValidEdges-length [] = []
    filterValidEdges-length ((i , j) ∷ xs) with i ≟ j | (i , j) ᵉ∈ᵍ? G
    ... | yes _ | _      = filterValidEdges-length xs
    ... | no  _ | no   _ = filterValidEdges-length xs
    ... | no  _ | yes  _ = refl ∷ filterValidEdges-length xs

    -- extendAll

    ∈-extendAll : ∀ {i q i∉q iq∈G ps} → q ∈ₗₙₑₚ ps → i ∷ q ∣ i∉q ∣ iq∈G ∈ₗₙₑₚ extendAll ps i
    ∈-extendAll {i} {q} {i∉q} {(v , e≡v)} {p ∷ _} (here q≈p) with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no i∈p | _       = contradiction (i∉p∧p≈q⇒i∉q i∉q q≈p) i∈p
    ... | yes _  | no ip∉G = contradiction (v , subst (λ j → G i j ≡ _) (p≈q⇒p₀≡q₀ q≈p) e≡v) ip∉G
    ... | yes _  | yes _   = here (refl ∷ q≈p)
    ∈-extendAll {i} {ps = p ∷ _} (there q∈ps) with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no  _  | _     = ∈-extendAll q∈ps
    ... | yes _  | no  _ = ∈-extendAll q∈ps
    ... | yes _  | yes _ = there (∈-extendAll q∈ps)

    extendAll-∈ : ∀ {i v} ps → v ∈ₗₙₑₚ extendAll ps i → ∃₂ λ q i∉q → ∃ λ iq∈G → v ≈ₙₑₚ i ∷ q ∣ i∉q ∣ iq∈G
    extendAll-∈ []  ()
    extendAll-∈ {i} (p ∷ ps) v∈e[p∷ps] with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no  _   | _    = extendAll-∈ ps v∈e[p∷ps]
    ... | yes _   | no _ = extendAll-∈ ps v∈e[p∷ps]
    ... | yes i∉p | yes ip∈G with v∈e[p∷ps]
    ...   | here  v≈i∷p   = p , i∉p , ip∈G , v≈i∷p
    ...   | there v∈e[ps] = extendAll-∈ ps v∈e[ps]

    extendAll-∉ : ∀ {ps i} {q : NonEmptySGPath G} {i∉q iq∈G} → All (q ≉ₙₑₚ_) ps → All (i ∷ q ∣ i∉q ∣ iq∈G ≉ₙₑₚ_) (extendAll ps i)
    extendAll-∉ {_} [] = []
    extendAll-∉ {p ∷ ps} {i} (q≉p ∷ q≉ps) with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no  _ | _     = extendAll-∉ q≉ps
    ... | yes _ | no  _ = extendAll-∉ q≉ps
    ... | yes _ | yes _ = (λ {(_ ∷ p≈q) → q≉p p≈q}) ∷ (extendAll-∉ q≉ps)

    extendAll! : ∀ {ps} → Unique NEPₛ' ps → ∀ i → Unique NEPₛ' (extendAll ps i)
    extendAll! [] _ = []
    extendAll! {p ∷ ps} (p∉ps ∷ ps!) i with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no  _ | _     = extendAll! ps! i
    ... | yes _ | no  _ = extendAll! ps! i
    ... | yes _ | yes _ = extendAll-∉ p∉ps ∷ extendAll! ps! i

    extendAll-length : ∀ {l ps} → All (λ p → length p ≡ l) ps → (i : Fin n) → All (λ p → length p ≡ suc l) (extendAll ps i)
    extendAll-length [] _ = []
    extendAll-length {ps = p ∷ ps} (|p|≡l ∷ |ps|≡l) i with i ∉ₙₑₚ? p | (i , source p) ᵉ∈ᵍ? G
    ... | no i∈p | _      = extendAll-length |ps|≡l i
    ... | yes _  | no  _  = extendAll-length |ps|≡l i
    ... | yes _  | yes _  = cong suc |p|≡l ∷ extendAll-length |ps|≡l i

    extendAll-disjoint : ∀ ps qs {i j} → i ≢ j → Disjoint NEPₛ' (extendAll ps i) (extendAll qs j)
    extendAll-disjoint ps qs i≢j (v∈eᵢps , v∈eⱼqs) with extendAll-∈ ps v∈eᵢps | extendAll-∈ qs v∈eⱼqs
    ... | _ , _ , _ , refl ∷ _ | _ , _ , _ , refl ∷ _ = i≢j refl


    -- All paths of length l

    ∈-allNEPathsOfLength : ∀ p → p ∈ₗₙₑₚ allNEPathsOfLength (length p)
    ∈-allNEPathsOfLength (i ∺ j ∣ i≢j ∣ ij∈G)               = ∈-filterValidEdges i≢j ij∈G (∈-combine _,_ (∈-allFin i) (∈-allFin j))
    ∈-allNEPathsOfLength (i ∷ (j ∺ k ∣ j≢k ∣ jk∈G) ∣ _ ∣ _) = ∈-concat NEPₛ'
                                                                (∈-extendAll (∈-allNEPathsOfLength (j ∺ k ∣ j≢k ∣ jk∈G)))
                                                                (∈-map LNEPₛ Fₛ (≈ₗₙₑₚ-reflexive ∘ (cong (extendAll (allNEPathsOfLength 1)))) (∈-allFin i))
    ∈-allNEPathsOfLength (i ∷ (j ∷ p ∣ j∉p ∣ jp∈G) ∣ _ ∣ _) = ∈-concat NEPₛ'
                                                                (∈-extendAll (∈-allNEPathsOfLength (j ∷ p ∣ j∉p ∣ jp∈G)))
                                                                (∈-map LNEPₛ Fₛ (≈ₗₙₑₚ-reflexive ∘ (cong (extendAll (allNEPathsOfLength (suc (length p)))))) (∈-allFin i))

    allNEPathsOfLength! : ∀ l → Unique NEPₛ' (allNEPathsOfLength l)
    allNEPathsOfLength! 0             = []
    allNEPathsOfLength! 1             = filterValidEdges! (combine! F×Fₛ Fₛ _,_ w≢y⊎x≢z⇒wx≢yz (allFin! n) (allFin! n))
    allNEPathsOfLength! (suc (suc l)) = concat! NEPₛ'
                                          (forced-map (extendAll! (allNEPathsOfLength! (suc l))) (allFin n))
                                          (map-pairs (extendAll-disjoint (allNEPathsOfLength (suc l)) (allNEPathsOfLength (suc l))) (allFin! n))

    allNEPathsOfLength-length : ∀ l → All (λ p → length p ≡ l) (allNEPathsOfLength l)
    allNEPathsOfLength-length 0             = []
    allNEPathsOfLength-length 1             = filterValidEdges-length (combine _,_ (allFin n) (allFin n))
    allNEPathsOfLength-length (suc (suc l)) = concat-all (forced-map (extendAll-length (allNEPathsOfLength-length (suc l))) (allFin n))

    allNEPathsOfLength-∈ : ∀ {l p} → p ∈ₗₙₑₚ allNEPathsOfLength l → length p ≡ l
    allNEPathsOfLength-∈ {l} p∈all = All-∈ NEPₛ' (trans ∘ p≈q⇒|p|≡|q| ∘ ≈ₙₑₚ-sym) (allNEPathsOfLength-length l) p∈all

    allNEPathsOfLength-disjoint : ∀ {l k} → l ≢ k → Disjoint NEPₛ' (allNEPathsOfLength l) (allNEPathsOfLength k)
    allNEPathsOfLength-disjoint {l} {k} l≢k (v∈pₗ , v∈pₖ) = l≢k (trans (sym (allNEPathsOfLength-∈ v∈pₗ)) (allNEPathsOfLength-∈ v∈pₖ))




  -- All non-empty paths

    allNEPaths! : Unique NEPₛ' allNEPaths
    allNEPaths! = concat! NEPₛ'
                    (forced-map allNEPathsOfLength! (map toℕ (allFin n)))
                    (map-pairs (λ {l} {k} → allNEPathsOfLength-disjoint {l} {k}) (map-pairs (λ x≢y → x≢y ∘ toℕ-injective) (allFin! n)))

    ∈-allNEPaths : ∀ p → p ∈ₗₙₑₚ allNEPaths
    ∈-allNEPaths p = ∈-concat NEPₛ'
                       (∈-allNEPathsOfLength p)
                       (∈-map LNEPₛ ℕₛ (≈ₗₙₑₚ-reflexive ∘ (cong allNEPathsOfLength)) (|p|∈allFin p))


    -- All paths

    allPaths! : Unique Pₛ' allPaths
    allPaths! = forced-map (λ _ ()) allNEPaths  ∷ map! Pₛ' NEPₛ' p≉q⇒[p]≉[q] allNEPaths!

    ∈-allPaths : (p : SGPath G) → p ∈ₗₚ allPaths
    ∈-allPaths []    = here []
    ∈-allPaths [ p ] = there (∈-map Pₛ' NEPₛ' [_] (∈-allNEPaths p))

    isEnumeration : IsEnumeration Pₛ' allPaths
    isEnumeration = record {
        unique = allPaths!;
        complete = ∈-allPaths
      }

    enumeration : Enumeration Pₛ'
    enumeration = record {
        list = allPaths;
        isEnumeration = isEnumeration
      }

