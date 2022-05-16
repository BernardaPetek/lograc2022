module Project.Syntax where
open import Relation.Binary
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List
open import Data.Nat using (ℕ)

data Type : Set where
  Nat : Type
  unit : Type
  _⇒'_ : Type → Type → Type
  _×_ : Type → Type → Type


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
  ⟨_,_⟩ : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A × B)
  fst_ : ∀ {A B} → Γ ⊢ (A × B) → Γ ⊢ A
  snd_ : ∀ {A B} → Γ ⊢ (A × B) → Γ ⊢ B
  _·_ : ∀ {A B} → Γ ⊢ (A ⇒' B) → Γ ⊢ A → Γ ⊢ B
  λ' : ∀ {A B} → (Γ ∷ A) ⊢ B → Γ ⊢ (A ⇒' B)
  zero : Γ ⊢ Nat
  suc : Γ ⊢ Nat → Γ ⊢ Nat
  primrec : ∀ {A} →  Γ ⊢ Nat → Γ ⊢ A → ((Γ ∷ Nat) ∷ A) ⊢ A → Γ ⊢ A
  
  
  


