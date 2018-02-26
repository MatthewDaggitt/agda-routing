open import Data.Bool using (Bool; true; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; reverse; filter; drop; take; concat; foldr; gfilter; map; zipWith; applyUpTo; tabulate)
open import Data.List.All using (All; []; _∷_) renaming (map to mapₐ)
open import Data.List.All.Properties
open import Data.List.Any using (Any; here; there; any)
open import Data.Maybe using (Maybe; just; nothing; Eq; drop-just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; suc; zero; z≤n; s≤s; _≤_; _<_)
open import Data.Nat.Properties using (⊔-sel; ≤-trans)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred; Universal; Decidable; _⊆_)
open import Relation.Binary using (Rel; REL; _Preserves_⟶_; _Respects_; DecSetoid; Setoid; Symmetric)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]; subst; subst₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_; id)
open import Algebra.FunctionProperties using (Op₂; Congruent₂)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.All
open import RoutingLib.Data.List.Properties
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.Permutation using (_⇿_; _◂_≡_; here; there; []; _∷_)

module RoutingLib.Data.List.All.Properties where

  All-swap : ∀ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL (List A) B ℓ} →
             ∀ {xss ys} → All (λ xs → All (xs ~_) ys) xss →
             All (λ y → All (_~ y) xss) ys
  All-swap {ys = []}      _  = []
  All-swap {ys = _ ∷ _}  []  = All-universal (λ _ → []) _
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxss) = (x~y ∷ (mapₐ (λ {(x~y ∷ _) → x~y}) pxss)) ∷ All-swap (x~ys ∷ (mapₐ (λ {(_ ∷ pys) → pys}) pxss))

  module _ {a p} {A : Set a} {P : A → Set p} where

    -- Permutations
    
    All-◂≡ : ∀ {x xs ys} → All P (x ∷ xs) → x ◂ xs ≡ ys → All P ys
    All-◂≡ pxs               here             = pxs
    All-◂≡ (px ∷ (py ∷ pxs)) (there x◂xs≡ys) = py ∷ All-◂≡ (px ∷ pxs) x◂xs≡ys
  
    All-⇿ : ∀ {xs ys} → All P xs → xs ⇿ ys → All P ys
    All-⇿ []         []                = []
    All-⇿ (px ∷ pxs) (x◂zs≡ys ∷ xs⇿zs) = All-◂≡ (px ∷ (All-⇿ pxs xs⇿zs)) x◂zs≡ys

    All-map⁺₂ : ∀ {b} {B : Set b} {f : B → A} → (∀ x → P (f x)) → ∀ xs → All P (map f xs)
    All-map⁺₂ Pf []       = []
    All-map⁺₂ Pf (x ∷ xs) = Pf x ∷ All-map⁺₂ Pf xs

    -----------
    -- Other --
    -----------

{-
    reverse⁺ : ∀ {xs} → All P xs → All P (reverse xs)
    reverse⁺ pxs = foldl-×pres {_•_ = λ rev x → x ∷ rev} {!!} {!!} []
    -- reverse xs ≡ foldl (λ rev x → x ∷ rev) [] xs
-}

    All-dfilter⁺₁ : ∀ (P? : Decidable P) xs → All P (dfilter P? xs)
    All-dfilter⁺₁ P? []       = []
    All-dfilter⁺₁ P? (x ∷ xs) with P? x
    ... | yes Px = Px ∷ All-dfilter⁺₁ P? xs
    ... | no  _  = All-dfilter⁺₁ P? xs

    All-dfilter⁺₂ : ∀ {q} {Q : A → Set q} (P? : Decidable P) 
                   {xs} → All Q xs → All Q (dfilter P? xs)
    All-dfilter⁺₂ P? {_} [] = []
    All-dfilter⁺₂ P? {x ∷ xs} (Qx ∷ Qxs) with P? x
    ... | no  _ = All-dfilter⁺₂ P? Qxs
    ... | yes _ = Qx ∷ All-dfilter⁺₂ P? Qxs

    All-applyBetween⁺₁ : ∀ f s e → (∀ {i} → s ≤ i → i < e → P (f i)) → All P (applyBetween f s e)
    All-applyBetween⁺₁ f zero    e       Pf = applyUpTo⁺₁ f e (Pf z≤n)
    All-applyBetween⁺₁ f (suc s) zero    Pf = []
    All-applyBetween⁺₁ f (suc s) (suc e) Pf = All-applyBetween⁺₁ (f ∘ suc) s e (λ s≤i i<e → Pf (s≤s s≤i) (s≤s i<e))

    All-applyBetween⁺₂ : ∀ f s e → (∀ {i} → P (f i)) → All P (applyBetween f s e)
    All-applyBetween⁺₂ f s e Pf = All-applyBetween⁺₁ f s e (λ _ _ → Pf)


  s≤betweenₛₑ : ∀ s e → All (s ≤_) (between s e)
  s≤betweenₛₑ s e = All-applyBetween⁺₁ id s e (λ s≤i _ → s≤i)

  betweenₛₑ<e : ∀ s e → All (_< e) (between s e)
  betweenₛₑ<e s e = All-applyBetween⁺₁ id s e (λ _ i<e → i<e)
  
  All-gfilter⁺₁ : ∀ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} {f : A → Maybe B} → (∀ {x} → P x → ∀ {y} → f x ≡ just y → Q y) → ∀ {xs} → All P xs → All Q (gfilter f xs)
  All-gfilter⁺₁ _ [] = []
  All-gfilter⁺₁ {f = f} f-inj {x ∷ xs} (px ∷ pxs) with f x | inspect f x
  ... | nothing | _            = All-gfilter⁺₁ f-inj pxs
  ... | just v  | [ fₓ≡justᵥ ] = f-inj px fₓ≡justᵥ ∷ All-gfilter⁺₁ f-inj pxs

  All-gfilter⁺₃ : ∀ {a b p} {A : Set a} {B : Set b} (P : B → Set p) {f : A → Maybe B} {xs} → All (λ x → f x ≡ nothing ⊎ (∀ {y} → f x ≡ just y → P y)) xs → All P (gfilter f xs)
  All-gfilter⁺₃ _ [] = []
  All-gfilter⁺₃ P {f = f} {x ∷ xs} (Px ∷ Pxs) with f x | inspect f x
  ... | nothing | _            = All-gfilter⁺₃ P Pxs
  ... | just v  | [ fₓ≡justᵥ ] with Px
  ...   | inj₁ fx≡nothing = contradiction fx≡nothing λ()
  ...   | inj₂ just⇒P     = just⇒P ≡-refl ∷ All-gfilter⁺₃ P Pxs
  
  All-gfilter⁺₂ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {f : A → Maybe B} → (∀ {x y} → f x ≡ just y → P y) → ∀ xs → All P (gfilter f xs)
  All-gfilter⁺₂ {P = P} f-inj xs = All-gfilter⁺₃ P (All-universal (λ x → inj₂ (λ {y} t → f-inj {x} {y} t)) xs)


  All-zipWith⁺ : ∀ {a b c p} {A : Set a} {B : Set b} {C : Set c} (P : C → Set p) (f : A → B → C) {xs ys} → All₂ (λ x y → P (f x y)) xs ys → All P (zipWith f xs ys)
  All-zipWith⁺ P f []              = []
  All-zipWith⁺ P f (Pfxy ∷ Pfxsys) = Pfxy ∷ All-zipWith⁺ P f Pfxsys


  ----------------------
  -- Pushed to stdlib --
  ----------------------


  module SetoidProperties {a ℓ} (S : Setoid a ℓ) where

    open Setoid S renaming (Carrier to A)
    open import Data.List.Any.Membership S using (_∈_)

    ∈-All : ∀ {p} {P : A → Set p} xs → (∀ {v} → v ∈ xs → P v) → All P xs
    ∈-All [] _ = []
    ∈-All (x ∷ xs) ∈⇨P = ∈⇨P (here refl) ∷ ∈-All xs (∈⇨P ∘ there)

    All-∈ : ∀ {p} {P : A → Set p} → P Respects _≈_ → ∀ {v xs} → All P xs → v ∈ xs → P v
    All-∈ resp (px ∷ pxs) (here v≈x)   = resp (sym v≈x) px
    All-∈ resp (px ∷ pxs) (there v∈xs) = All-∈ resp pxs v∈xs

    map-all : ∀ {b p} {B : Set b} {P : B → Set p} f {xs : List A} → (∀ {x} → x ∈ xs → P (f x)) → All P (map f xs)
    map-all f {[]}     pres = []
    map-all f {x ∷ xs} pres = pres (here refl) ∷ map-all f (pres ∘ there)
    
  open SetoidProperties public


  module DecSetoidProperties {a ℓ} (DS : DecSetoid a ℓ) where

    open DecSetoid DS renaming (Carrier to A)
    open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)

    deduplicate⁺ : ∀ {p} {P : A → Set p} {xs} → All P xs → All P (deduplicate xs)
    deduplicate⁺ {xs = _}      [] = []
    deduplicate⁺ {xs = x ∷ xs} (px ∷ pxs) with any (x ≟_) xs
    ... | yes _ = deduplicate⁺ pxs
    ... | no  _ = px ∷ deduplicate⁺ pxs

  open DecSetoidProperties public


  module DoubleSetoidProperties
    {a₁ ℓ₁} (S₁ : Setoid a₁ ℓ₁)
    {a₂ ℓ₂} (S₂ : Setoid a₂ ℓ₂) where

    open Setoid S₁ renaming (Carrier to A₁; refl to refl₁)
    open Setoid S₂ renaming (Carrier to A₂)

    open import Data.List.Any.Membership S₁ using () renaming (_∈_ to _∈₁_)
    open import Data.List.Any.Membership S₂ using () renaming (_∈_ to _∈₂_)

    All-combine⁺ : ∀ {b p} {B : Set b} {P : B → Set p} _•_ (xs : List A₁) (ys : List A₂) → (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x • y)) → All P (combine _•_ xs ys)
    All-combine⁺ _•_ []       ys pres = []
    All-combine⁺ _•_ (x ∷ xs) ys pres = ++⁺ (map-all S₂ (x •_) (pres (here refl₁))) (All-combine⁺ _•_ xs ys (pres ∘ there))

  open DoubleSetoidProperties public



  -- All pairs

  All⇒AllPairs : ∀ {a p ℓ} {A : Set a} {P : Pred A p} {_~_ : Rel A ℓ} {xs} →
                 All P xs → (∀ {x y} → P x → P y → x ~ y) → AllPairs _~_ xs
  All⇒AllPairs []         pres = []
  All⇒AllPairs (px ∷ pxs) pres = mapₐ (pres px) pxs ∷ (All⇒AllPairs pxs pres)
  
  AllPairs-map⁺₂ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}  {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
              {f : A → B} → f Preserves _~₁_ ⟶ _~₂_ → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ map f
  AllPairs-map⁺₂ f-pres []           = []
  AllPairs-map⁺₂ f-pres (x∉xs ∷ xs!) = All-map (mapₐ f-pres x∉xs) ∷ AllPairs-map⁺₂ f-pres xs!

  AllPairs-gfilter⁺ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} {_~₁_ : Rel A ℓ₁} {_~₂_ : Rel B ℓ₂}
                  (f : A → Maybe B) → (∀ {x y} → x ~₁ y → (f x ≡ nothing) ⊎ (f y ≡ nothing) ⊎ (Eq _~₂_ (f x) (f y)))
                  → AllPairs _~₁_ ⋐ AllPairs _~₂_ ∘ gfilter f
  AllPairs-gfilter⁺ _ _ [] = []
  AllPairs-gfilter⁺ {_~₁_ = _~₁_} {_~₂_} f f-inj {x ∷ xs} (px ∷ pxs) with f x | inspect f x
  ... | nothing | _            = AllPairs-gfilter⁺ f f-inj pxs
  ... | just v  | [ fx≡justv ] = All-gfilter⁺₁ convert px ∷ AllPairs-gfilter⁺ f f-inj pxs
    where
    convert : ∀ {a} → x ~₁ a → ∀ {b} → f a ≡ just b → v ~₂ b
    convert {a} x~a {b} fa≡justb with f-inj x~a
    ... | inj₁ fx≡nothing        = contradiction (≡-trans (≡-sym fx≡nothing) fx≡justv) λ()
    ... | inj₂ (inj₁ fa≡nothing) = contradiction (≡-trans (≡-sym fa≡nothing) fa≡justb) λ()
    ... | inj₂ (inj₂ fx~fa)      = drop-just (subst₂ (Eq _~₂_) fx≡justv fa≡justb fx~fa)






  module _ {a ℓ} {A : Set a} {_~_ : Rel A ℓ} where

    AllPairs-◂≡ : Symmetric _~_ → ∀ {x xs ys} → AllPairs _~_ (x ∷ xs) → x ◂ xs ≡ ys → AllPairs _~_ ys
    AllPairs-◂≡ sym pxs                           here             = pxs
    AllPairs-◂≡ sym ((x~z ∷ x~xs) ∷ (y~xs ∷ pxs)) (there x◂xs≡ys) = All-◂≡ (sym x~z ∷ y~xs) x◂xs≡ys ∷ (AllPairs-◂≡ sym (x~xs ∷ pxs) x◂xs≡ys)

    AllPairs-⇿ : Symmetric _~_ → ∀ {xs ys} → AllPairs _~_ xs → xs ⇿ ys → AllPairs _~_ ys
    AllPairs-⇿ sym []           []                 = []
    AllPairs-⇿ sym (x~xs ∷ pxs) (x◂zs≡ys ∷ xs⇿zs) = AllPairs-◂≡ sym (All-⇿ x~xs xs⇿zs ∷ AllPairs-⇿ sym pxs xs⇿zs) x◂zs≡ys


    AllPairs-dfilter⁺ : ∀ {p} {P : A → Set p} (P? : Decidable P)
                     → ∀ {xs} → AllPairs _~_ xs → AllPairs _~_ (dfilter P? xs)
    AllPairs-dfilter⁺ P? {_}      []           = []
    AllPairs-dfilter⁺ P? {xs = x ∷ xs} (x∉xs ∷ xs!) with P? x
    ... | no  _ = AllPairs-dfilter⁺ P? xs!
    ... | yes _ = All-dfilter⁺₂ P? x∉xs ∷ AllPairs-dfilter⁺ P? xs!
    
    AllPairs-++⁺ : ∀ {xs ys} → AllPairs _~_ xs → AllPairs _~_ ys 
                 → All (λ x → All (x ~_) ys) xs → AllPairs _~_ (xs ++ ys)
    AllPairs-++⁺ []         ~ys _              = ~ys
    AllPairs-++⁺ (px ∷ ~xs) ~ys (x~ys ∷ xs~ys) = ++⁺ px x~ys ∷ AllPairs-++⁺ ~xs ~ys xs~ys

    AllPairs-concat⁺ : ∀ {xss} → All (AllPairs _~_) xss →
                       AllPairs (λ xs ys → All (λ x → All (x ~_) ys) xs) xss →
                       AllPairs _~_ (concat xss)
    AllPairs-concat⁺ []           []              = []
    AllPairs-concat⁺ (pxs ∷ pxss) (xs~xss ∷ ~xss) = AllPairs-++⁺ pxs (AllPairs-concat⁺ pxss ~xss) (mapₐ concat⁺ (All-swap xs~xss))

    AllPairs-drop⁺ : ∀ {xs} n → AllPairs _~_ xs → AllPairs _~_ (drop n xs)
    AllPairs-drop⁺ zero    pxs       = pxs
    AllPairs-drop⁺ (suc n) []        = []
    AllPairs-drop⁺ (suc n) (_ ∷ pxs) = AllPairs-drop⁺ n pxs

    AllPairs-take⁺ : ∀ {xs} n → AllPairs _~_ xs → AllPairs _~_ (take n xs)
    AllPairs-take⁺ zero    pxs          = []
    AllPairs-take⁺ (suc n) []           = []
    AllPairs-take⁺ (suc n) (x~xs ∷ pxs) = take⁺ n x~xs ∷ (AllPairs-take⁺ n pxs)

    AllPairs-applyUpTo⁺₁ : ∀ f n → (∀ {i j} → i < j → j < n → f i ~ f j) → AllPairs _~_ (applyUpTo f n)
    AllPairs-applyUpTo⁺₁ f zero    f~ = []
    AllPairs-applyUpTo⁺₁ f (suc n) f~ = applyUpTo⁺₁ (f ∘ suc) n (f~ (s≤s z≤n) ∘ s≤s) ∷ AllPairs-applyUpTo⁺₁ (f ∘ suc) n (λ i≤j j<n → f~ (s≤s i≤j) (s≤s j<n))

    AllPairs-applyUpTo⁺₂ : ∀ f n → (∀ i j → f i ~ f j) → AllPairs _~_ (applyUpTo f n)
    AllPairs-applyUpTo⁺₂ f n f~ = AllPairs-applyUpTo⁺₁ f n (λ _ _ → f~ _ _)

    AllPairs-applyBetween⁺₁ : ∀ f s e → (∀ {i j} → s ≤ i → i < j → j < e → f i ~ f j) → AllPairs _~_ (applyBetween f s e)
    AllPairs-applyBetween⁺₁ f zero    e       Pf = AllPairs-applyUpTo⁺₁ f e (Pf z≤n)
    AllPairs-applyBetween⁺₁ f (suc s) zero    Pf = []
    AllPairs-applyBetween⁺₁ f (suc s) (suc e) Pf = AllPairs-applyBetween⁺₁ (f ∘ suc) s e (λ s≤i i<j j<e → Pf (s≤s s≤i) (s≤s i<j) (s≤s j<e))

    AllPairs-applyBetween⁺₂ : ∀ f s e → (∀ {i j} → f i ~ f j) → AllPairs _~_ (applyBetween f s e)
    AllPairs-applyBetween⁺₂ f s e Pf = AllPairs-applyBetween⁺₁ f s e (λ _ _ _ → Pf)
  

  module AllPairsDecSetoidProperties {a ℓ} (DS : DecSetoid a ℓ) where

    open DecSetoid DS renaming (Carrier to A)
    open import RoutingLib.Data.List.Membership.DecSetoid DS using (deduplicate)

    AllPairs-deduplicate⁺ : ∀ {ℓ} {_~_ : Rel A ℓ} {xs} → AllPairs _~_ xs →
                            AllPairs _~_ (deduplicate xs)
    AllPairs-deduplicate⁺ {xs = _}      [] = []
    AllPairs-deduplicate⁺ {xs = x ∷ xs} (px ∷ pxs) with any (x ≟_) xs
    ... | yes _ = AllPairs-deduplicate⁺ pxs
    ... | no  _ = deduplicate⁺ _ px ∷ AllPairs-deduplicate⁺ pxs

  open AllPairsDecSetoidProperties public
  


  module _ {a b ℓ} {A : Set a} {B : Set b} {_~_ : REL A B ℓ} where

    -- stdlib
    All₂-tabulate : ∀ {n} {f : Fin n → A} {g : Fin n → B} → (∀ i → f i ~ g i) → All₂ _~_ (tabulate f) (tabulate g)
    All₂-tabulate {n = zero} f~g = []
    All₂-tabulate {n = suc n} f~g = f~g fzero ∷ All₂-tabulate (f~g ∘ fsuc)

    -- stdlib
    All₂-++ : ∀ {ws xs ys zs} → All₂ _~_ ws xs → All₂ _~_ ys zs → All₂ _~_ (ws ++ ys) (xs ++ zs)
    All₂-++ [] ys~zs = ys~zs
    All₂-++ (w~x ∷ ws~xs) ys~zs = w~x ∷ All₂-++ ws~xs ys~zs

    -- stdlib
    All₂-concat : ∀ {xss yss} → All₂ (All₂ _~_) xss yss → All₂ _~_ (concat xss) (concat yss)
    All₂-concat [] = []
    All₂-concat (xs~ys ∷ xss~yss) = All₂-++ xs~ys (All₂-concat xss~yss)

  foldr-All₂ : ∀ {a b ℓ} {A : Set a} {B : Set b} (_~_ : REL A B ℓ)
             {_⊕ᵃ_ : Op₂ A} {_⊕ᵇ_ : Op₂ B} → 
             (∀ {w x y z} → w ~ x → y ~ z → (w ⊕ᵃ y) ~ (x ⊕ᵇ z)) →
             ∀ {xs ys e f} → e ~ f → All₂ _~_ xs ys →
             foldr _⊕ᵃ_ e xs ~ foldr _⊕ᵇ_ f ys
  foldr-All₂ _ _    e~f []            = e~f
  foldr-All₂ _ pres e~f (x~y ∷ xs~ys) = pres x~y (foldr-All₂ _ pres e~f xs~ys)





