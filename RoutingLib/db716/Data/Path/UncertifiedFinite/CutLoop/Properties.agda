module RoutingLib.db716.Data.Path.UncertifiedFinite.CutLoop.Properties where

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List ; _∷_; []; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (proj₂; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; inspect; [_])

open import RoutingLib.db716.Data.Path.UncertifiedFinite

cutLoopAuxValid : ∀ {n} (e : Edge n) (p : Path n) (e∈p : e ∈ p) → ValidPath p → ValidPath (cutLoopAux e p e∈p)
cutLoopAuxValid {n} e .(_ ∷ _) (here px) (v0 ∷ pValid) = pValid
cutLoopAuxValid {n} e (e' ∷ p) (there e∈p) (x₁ ∷ pValid) = cutLoopAuxValid e p e∈p pValid

cutLoopAux-⇿ : ∀ {n} (e e' : Edge n) (p : Path n) (e'∈p : e' ∈ p) → ValidPath p → proj₂ e ≡ proj₂ e' → e ⇿ cutLoopAux e' p e'∈p
cutLoopAux-⇿ e .(fst , snd) ((fst , snd) ∷ .[]) (here refl) (start ∷ pValid) e₂≡e₂' = start
cutLoopAux-⇿ (a , b) (a' , .b) ((a' , b') ∷ (b' , _) ∷ _) (here refl) (continue ∷ pValid) refl = continue
cutLoopAux-⇿ (a , b) (a' , .b) ((fst , snd) ∷ p) (there e'∈p) (continue ∷ pValid) refl = cutLoopAux-⇿ (a , b) (a' , b) p e'∈p pValid refl

cutLoop-⇿ : ∀ {n} (e : Edge n) (p : Path n) (loop : HasLoop p) → ValidPath p → e ⇿ p → e ⇿ cutLoop p loop
cutLoop-⇿ e ((b , b) ∷ .[]) trivial (start ∷ valid) e⇿p = start
cutLoop-⇿ (_ , b) ((b , b) ∷ (b , _) ∷ _) trivial (continue ∷ valid) continue = continue
cutLoop-⇿ (a , b) ((b , c) ∷ p) (here {_} {i} ib∈p) (continue ∷ valid) continue = cutLoopAux-⇿ (a , b) (i , b) p ib∈p valid refl
cutLoop-⇿ (a , .b) ((b , c) ∷ p) (there loop) (continue ∷ valid) continue = continue

cutLoopValid : ∀ {n} (p : Path n) → (loop : HasLoop p) → ValidPath p → ValidPath (cutLoop p loop)
cutLoopValid ((a , a) ∷ p) trivial (x ∷ valid) = valid
cutLoopValid ((a , b) ∷ e ∷ p) (here ?∈ep) (_ ∷ valid) = cutLoopAuxValid _ (e ∷ p) ?∈ep valid
cutLoopValid ((a , b) ∷ p) (there loop) (v0 ∷ valid) = cutLoop-⇿ (a , b) p loop valid v0 ∷ cutLoopValid p loop valid

cutLoopAuxDecreasesLength : ∀ {n} (e : Edge n) (p : Path n) (e∈p : e ∈ p) → suc (length (cutLoopAux e p e∈p)) ≤ length p
cutLoopAuxDecreasesLength {n} e (e' ∷ p) (here px) = ≤-reflexive refl
cutLoopAuxDecreasesLength {n} e (e' ∷ p) (there e∈p) = <-trans ( cutLoopAuxDecreasesLength e p e∈p ) (≤-reflexive refl)

cutLoopDecreasesLength : ∀ {n} (p : Path n) (loop : HasLoop p) → suc (length (cutLoop p loop)) ≤ length p
cutLoopDecreasesLength {n} ((i , i) ∷ p) trivial = ≤-reflexive refl
cutLoopDecreasesLength {n} ((i , j) ∷ e ∷ p) (here {_} {a} x) = <-trans (cutLoopAuxDecreasesLength (a , i) (e ∷ p) x) (≤-reflexive refl)
cutLoopDecreasesLength {n} (e ∷ p) (there loop) = s≤s (cutLoopDecreasesLength p loop) 

i≢j⇒cutLoopAux≢[] : ∀ {n} (i j : Fin  n) (e : Edge n) (p : Path n) (e∈p : e ∈ p) → proj₂ e ≡ i → PathTo j p → i ≢ j → cutLoopAux e p e∈p ≢ []
i≢j⇒cutLoopAux≢[] i j .(_ , j) .((_ , j) ∷ []) (here refl) e₂≡i here i≢j cutloop≡[] = i≢j (sym e₂≡i)
i≢j⇒cutLoopAux≢[] i j e .(e ∷ _ ∷ _) (here refl) e₂≡i (there (there toj)) i≢j ()
i≢j⇒cutLoopAux≢[] i j e (e' ∷ p) (there e∈p) e₂≡i (there toj) i≢j cutloop≡[] = i≢j⇒cutLoopAux≢[] i j e p e∈p e₂≡i toj i≢j cutloop≡[]

i≢j⇒cutLoop≢[] : ∀ {n} (i j : Fin  n) (p : Path n) (loop : HasLoop p) → PathFrom i p → PathTo j p → i ≢ j → cutLoop p loop ≢ []
i≢j⇒cutLoop≢[] i .i .((i , i) ∷ []) trivial here here i≢j cutloop≡[] = i≢j refl
i≢j⇒cutLoop≢[] i j .((i , i) ∷ (_ , j) ∷ []) trivial here (there here) i≢j ()
i≢j⇒cutLoop≢[] i j (.(i , _) ∷ e' ∷ p) (here {_} {a} e∈p) here (there toj) i≢j cutloop≡[] = i≢j⇒cutLoopAux≢[] i j (a , i) (e' ∷ p) e∈p refl toj i≢j cutloop≡[]

cutLoopAuxFrom' : ∀ {n} (i j : Fin n) (e : Edge n) (p : Path n) (e∈p : e ∈ p)
  → proj₂ e ≡ i → PathTo j p → ValidPath p → PathFrom i (cutLoopAux e p e∈p) ⊎ cutLoopAux e p e∈p ≡ []
cutLoopAuxFrom' .i j (a , i) .((a , i) ∷ []) (here {xs = .[]} refl) refl toj (start ∷ valid) = inj₂ refl
cutLoopAuxFrom' .i j (a , i) .((a , i) ∷ (i , _) ∷ _) (here {xs = .((i , _) ∷ _)} refl) refl toj (continue ∷ valid) = inj₁ here
cutLoopAuxFrom' i j e .(_ ∷ xs) (there {xs = xs} e∈p) proj₂e≡i (there toj) (x₁ ∷ valid) = cutLoopAuxFrom' i j e xs e∈p proj₂e≡i toj valid

cutLoopFrom' : ∀ {n} (i j : Fin n) (p : Path n) (loop : HasLoop p) → PathFrom i p → PathTo j p → ValidPath p → PathFrom i (cutLoop p loop) ⊎ cutLoop p loop ≡ []
cutLoopFrom' i .i .((i , i) ∷ []) trivial here here valid = inj₂ refl
cutLoopFrom' i j .((i , i) ∷ (i , _) ∷ _) trivial here (there toj) (continue ∷ valid) = inj₁ here
cutLoopFrom' i j ((i , k) ∷ e ∷ p) (here {_} {a} ai∈e::p) here (there toj) (v ∷ valid) = cutLoopAuxFrom' i j (a , i) (e ∷ p) ai∈e::p refl toj valid
cutLoopFrom' i j .((i , _) ∷ _) (there {e = .(i , _)} loop) here toj valid = inj₁ here

cutLoopFrom : ∀ {n} (i j : Fin  n) (p : Path n) (loop : HasLoop p) → PathFrom i p → PathTo j p → ValidPath p → i ≢ j → PathFrom i (cutLoop p loop)
cutLoopFrom i j (e ∷ p) loop from-i to-j valid i≢j with cutLoopFrom' i j (e ∷ p) loop from-i to-j valid
... | inj₁ fromi' = fromi'
... | inj₂ cutLoop≡[] = contradiction cutLoop≡[] (i≢j⇒cutLoop≢[] i j (e ∷ p) loop from-i to-j i≢j)

cutLoopAuxTo' : ∀ {n} (i j : Fin n) (e : Edge n) (p : Path n) (e∈p : e ∈ p)
  → proj₂ e ≡ i → PathTo j p → ValidPath p → PathTo j (cutLoopAux e p e∈p) ⊎ cutLoopAux e p e∈p ≡ []
cutLoopAuxTo' i j e .(e ∷ []) (here {xs = []} refl) proj₂e≡i to valid = inj₂ refl
cutLoopAuxTo' i j e .(e ∷ x ∷ xs) (here {xs = x ∷ xs} refl) proj₂e≡i (there to) valid = inj₁ to
cutLoopAuxTo' i j e .(_ ∷ xs) (there {xs = xs} e∈p) proj₂e≡i (there to) (x₁ ∷ valid) = cutLoopAuxTo' i j e xs e∈p proj₂e≡i to valid

cutLoopTo' : ∀ {n} (i j : Fin n) (p : Path n) (loop : HasLoop p) → PathFrom i p → PathTo j p → ValidPath p → PathTo j (cutLoop p loop) ⊎ cutLoop p loop ≡ []
cutLoopTo' i .i .((i , i) ∷ []) trivial here here valid = inj₂ refl
cutLoopTo' i j .((i , i) ∷ _) trivial here (there to) (x ∷ valid) = inj₁ to
cutLoopTo' i j .((i , _) ∷ e ∷ p) (here {e ∷ p} {a} ai∈ep) here (there to) (x₂ ∷ valid) = cutLoopAuxTo' i j (a , i) (e ∷ p) ai∈ep refl to valid
cutLoopTo' i j (.(i , k) ∷ p) (there {.((k , _) ∷ _)} loop) (here {k}) (there to) (continue ∷ valid) with cutLoopTo' k j p loop here to valid | k ≟ j
... | inj₁ to' | _ = inj₁ (there to')
... | inj₂ cutLoop≡[] | yes refl rewrite cutLoop≡[] = inj₁ here
... | inj₂ cutLoop≡[] | no k≢j = contradiction cutLoop≡[] (i≢j⇒cutLoop≢[] k j p loop here to k≢j)

cutLoopTo : ∀ {n} (i j : Fin  n) (p : Path n) (loop : HasLoop p) → PathFrom i p → PathTo j p → ValidPath p → i ≢ j → PathTo j (cutLoop p loop)
cutLoopTo i j (e ∷ p) loop from-i to-j valid i≢j with cutLoopTo' i j (e ∷ p) loop from-i to-j valid
... | inj₁ toj' = toj'
... | inj₂ cutLoop≡[] = contradiction cutLoop≡[] (i≢j⇒cutLoop≢[] i j (e ∷ p) loop from-i to-j i≢j)
