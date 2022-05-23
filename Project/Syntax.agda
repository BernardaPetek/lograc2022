module Project.Syntax where
open import Relation.Binary
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂; _,_ )
open import Relation.Binary.PropositionalEquality using (cong)


data Type : Set where
  Nat : Type
  unit : Type
  _⇒'_ : Type → Type → Type
  _×'_ : Type → Type → Type


data Ctx' : Set where
  ● : Ctx'
  _∷_ : Ctx' → Type → Ctx'


data _∈'_ : Type → Ctx' → Set where
  ∈'-here : {x : Type} → {xs : Ctx'} → x ∈' (xs ∷ x)
  ∈'-there : {x y : Type} {xs : Ctx'} → x ∈' xs → x ∈' (xs ∷ y)

Ctx = List Type


data _⊢_ (Γ : Ctx') : Type → Set where
  * : Γ ⊢ unit
  var : ∀ {A} → A ∈' Γ → Γ ⊢ A
  ⟨_,_⟩ : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ×' B)
  fst'_ : ∀ {A B} → Γ ⊢ (A ×' B) → Γ ⊢ A
  snd'_ : ∀ {A B} → Γ ⊢ (A ×' B) → Γ ⊢ B
  _·'_ : ∀ {A B} → Γ ⊢ (A ⇒' B) → Γ ⊢ A → Γ ⊢ B
  λ' : ∀ {A B} → (Γ ∷ A) ⊢ B → Γ ⊢ (A ⇒' B)
  zero' : Γ ⊢ Nat
  suc' : Γ ⊢ Nat → Γ ⊢ Nat
  primrec : ∀ {A} →  Γ ⊢ Nat → Γ ⊢ A → ((Γ ∷ Nat) ∷ A) ⊢ A → Γ ⊢ A


prec : {A : Set} → ℕ → A → ( ℕ → A → A ) → A
prec zero v w = v
prec (suc n) v w = w n ( prec n v w )
 

〚_〛ᵗ : Type → Set
〚 Nat 〛ᵗ = ℕ
〚 unit 〛ᵗ = ⊤
〚 t1 ⇒' t2 〛ᵗ = 〚 t1 〛ᵗ → 〚 t2 〛ᵗ
〚 t1 ×' t2 〛ᵗ = 〚 t1 〛ᵗ × 〚 t2 〛ᵗ

〚_〛ᶜ : Ctx' → Set
〚 ● 〛ᶜ = ⊤
〚 Γ ∷ A 〛ᶜ = 〚 Γ 〛ᶜ × 〚 A 〛ᵗ

〚_〛 :  {Γ : Ctx'} {A : Type} → Γ ⊢ A → 〚 Γ 〛ᶜ → 〚 A 〛ᵗ
〚 * 〛 y = tt
〚 var ∈'-here 〛 y = proj₂ y
〚 var (∈'-there x) 〛 y = 〚 var x 〛(proj₁ y) 
〚 ⟨ x , x1 ⟩ 〛 y =  (〚 x 〛 y) , (〚 x1 〛 y)
〚 fst' x 〛 y = ( proj₁ (〚 x 〛 y))
〚 snd' x 〛 y = ( proj₂ (〚 x 〛 y))
〚 x ·' x1 〛 y = ( 〚 x 〛 y ) (〚 x1 〛 y )
〚 λ' x 〛 y = ( λ x1 → (〚 x 〛 (y , x1)) )
〚 zero' 〛 y = zero
〚 suc' x 〛 y = suc (〚 x 〛 y)
〚 primrec n v w 〛 y =  ( prec ( 〚 n 〛 y ) ( 〚 v 〛 y ) (λ x1 → ( λ x2 → (〚 w 〛 ( (y , x1) , x2 ) ) ) ) )










  
  
  


