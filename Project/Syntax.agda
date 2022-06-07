module Project.Syntax where
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂; _,_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)

infixr 20 _⇒_

infixl 35 _·_
infixl 30 _×'_

infix 15 _⊢_

-- types in STLC
data Type : Set where
  Nat : Type
  unit : Type
  _⇒_ : Type → Type → Type
  _×'_ : Type → Type → Type

-- Ctx are lists of types
data Ctx : Set where
  ● : Ctx
  _∷_ : Ctx → Type → Ctx
  
-- check and prove where the Type is in the Ctx
data _∈_ : Type → Ctx → Set where
  ∈-here : {x : Type} → {xs : Ctx} → x ∈ (xs ∷ x)
  ∈-there : {x y : Type} {xs : Ctx} → x ∈ xs → x ∈ (xs ∷ y)

-- Γ ⊢ A represents a term of type A in context Γ 
data _⊢_ (Γ : Ctx) : Type → Set where
  ⋆ : Γ ⊢ unit
  var : ∀ {A} → A ∈ Γ → Γ ⊢ A
  ⟨_,_⟩ : ∀ {A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A ×' B)
  fst_ : ∀ {A B} → Γ ⊢ (A ×' B) → Γ ⊢ A
  snd_ : ∀ {A B} → Γ ⊢ (A ×' B) → Γ ⊢ B
  _·_ : ∀ {A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  fun : ∀ {A B} → (Γ ∷ A) ⊢ B → Γ ⊢ (A ⇒ B)
  zero : Γ ⊢ Nat
  suc : Γ ⊢ Nat → Γ ⊢ Nat
  primrec : ∀ {A} →  Γ ⊢ Nat → Γ ⊢ A → ((Γ ∷ Nat) ∷ A) ⊢ A → Γ ⊢ A

-- primitive recursion written in Agda
prec : {A : Set} → ℕ → A → ( ℕ → A → A ) → A
prec zero v w = v
prec (suc n) v w = w n ( prec n v w )
 
-- mapping Type to Agda types
〚_〛ᵗ : Type → Set
〚 Nat 〛ᵗ = ℕ
〚 unit 〛ᵗ = ⊤
〚 A ⇒ B 〛ᵗ = 〚 A 〛ᵗ → 〚 B 〛ᵗ
〚 A ×' B 〛ᵗ = 〚 A 〛ᵗ × 〚 B 〛ᵗ

-- mapping Ctx to Agda Types
〚_〛ᶜ : Ctx → Set
〚 ● 〛ᶜ = ⊤
〚 Γ ∷ A 〛ᶜ = 〚 Γ 〛ᶜ × 〚 A 〛ᵗ

-- mapping to Agda types
〚_〛 :  {Γ : Ctx} {A : Type} → Γ ⊢ A → 〚 Γ 〛ᶜ → 〚 A 〛ᵗ
〚 ⋆ 〛 η = tt
〚 var ∈-here 〛 η = proj₂ η
〚 var (∈-there e) 〛 η = 〚 var e 〛(proj₁ η) 
〚 ⟨ e₁ , e₂ ⟩ 〛 η =  (〚 e₁ 〛 η) , (〚 e₂ 〛 η)
〚 fst e 〛 η = ( proj₁ (〚 e 〛 η))
〚 snd e 〛 η = ( proj₂ (〚 e 〛 η))
〚 e₁ · e₂ 〛 η = ( 〚 e₁ 〛 η ) (〚 e₂ 〛 η )
〚 fun e 〛 η = ( λ e₁ → (〚 e 〛 (η , e₁)) )
〚 zero 〛 η = zero
〚 suc e 〛 η = suc (〚 e 〛 η)
〚 primrec n v w 〛 η =  ( prec ( 〚 n 〛 η ) ( 〚 v 〛 η ) (λ e₁ → ( λ e₂ → (〚 w 〛 ( (η , e₁) , e₂ ) ) ) ) )


-- programming in STLC

-- addition in STLC 
add : {Γ : Ctx} → Γ ⊢ Nat ⇒ Nat ⇒ Nat
add =  fun (
           fun (
             primrec
                (var ( ∈-there ∈-here ))
                (var ∈-here)
                (suc ( var ∈-here ))
            )
       )


-- multiplication in STLC
mult : {Γ : Ctx} → Γ ⊢ Nat ⇒ Nat ⇒ Nat
mult =  fun (
            fun (
              primrec
                ( var ( ∈-there ∈-here ) )
                zero
                ( add ·  ( var (∈-there (∈-there ∈-here ) ) ) · ( var ∈-here )  )
            )
        )

-- mapping natural numbers to type Nat in STLC
numeral : ℕ → { Γ : Ctx } → Γ ⊢ Nat
numeral zero = zero
numeral (suc n) = suc (numeral n)



-- soundness proofs

--   primrec
primrec-zero-≡ : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} {A : Type} {e : Γ ⊢ A} {h : ((Γ ∷ Nat) ∷ A) ⊢ A} →
                 (〚 primrec zero e h 〛 η ) ≡ (〚 e  〛 η )
primrec-zero-≡ {Γ} {η} {A} {e} {h} =
               begin
                 〚 primrec zero e h 〛 η
                 ≡⟨  refl ⟩
                  ( prec  ( 〚 zero 〛 η )  ( 〚 e 〛 η ) (λ e₁ → ( λ e₂ → (〚 h 〛 ( ( η , e₁) , e₂ ) ) ) ) )
                 ≡⟨ refl ⟩
                   (〚 e  〛 η )
                 ∎

primrec-step-≡ : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} {A : Type} {n : Γ ⊢ Nat} {a : Γ ⊢ A}  {h : ((Γ ∷ Nat) ∷ A) ⊢ A} →
                 (〚 primrec (suc n) a h 〛 η ) ≡  (λ e₁ → ( λ e₂ → (〚 h 〛 ( ( η  , e₁) , e₂ ) ) ) ) (〚 n 〛 η ) (〚 primrec n a h 〛 η )
primrec-step-≡ {Γ} {η} {A} {n} {a} {h} =
               begin
                  (〚 primrec (suc n) a h 〛 η )
                 ≡⟨ refl ⟩
                  ( prec ( 〚 suc n 〛  η ) ( 〚 a 〛  η ) (λ e₁ → ( λ e₂ → (〚 h 〛 ( ( η , e₁) , e₂ ) ) ) ) )
                  ≡⟨ refl  ⟩
                  (λ e₁ → ( λ e₂ → (〚 h 〛 ( ( η  , e₁) , e₂ ) ) ) ) (〚 n 〛 η ) (〚 primrec n a h 〛 η )
                 ∎


-- addition
numeral-≡ : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} (n : ℕ) → 〚 numeral n 〛 η ≡ n
numeral-≡ {Γ} {η} zero = refl
numeral-≡ {Γ} {η} (suc n) =
                           begin
                             suc (〚 numeral n 〛 η)
                           ≡⟨ cong suc (numeral-≡ n) ⟩
                             suc n
                           ∎

add-≡ :  ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} → (m n : ℕ) → 〚 ( add · (numeral m)) · (numeral n) 〛 η ≡ m + n
add-≡  {Γ} {η} zero n =
                      begin
                        〚 numeral n 〛 η
                      ≡⟨ numeral-≡ n  ⟩
                         n
                      ∎
add-≡  {Γ} {η} (suc m) n =
                  begin
                    suc (prec (〚 numeral m 〛 η) (〚 numeral n 〛 η) (λ e₁ e₂ → suc e₂))
                  ≡⟨  cong suc (add-≡ m n)  ⟩
                    suc m + n
                  ∎ 

-- projections
-- first 
fst-≡ : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} {A : Type} {e₁ : Γ ⊢ A}  {e₂ : Γ ⊢ A} → 〚 fst ⟨ e₁ , e₂ ⟩ 〛 η ≡ 〚 e₁ 〛 η
fst-≡  {Γ} {η} {A} {e₁} {e₂} =
                        begin
                          〚 fst ⟨ e₁ , e₂ ⟩ 〛 η
                        ≡⟨ refl ⟩
                         proj₁ ((〚 e₁ 〛 η) , (〚 e₂ 〛 η))
                        ≡⟨ refl ⟩
                         〚 e₁ 〛 η
                        ∎

-- second
snd-≡ : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} {A : Type} {e₁ : Γ ⊢ A} {e₂ : Γ ⊢ A} → 〚 snd ⟨ e₁ , e₂ ⟩ 〛 η ≡ 〚 e₂ 〛 η
snd-≡  {Γ} {η} {A} {e₁} {e₂} =
                        begin
                          〚 snd ⟨ e₁ , e₂ ⟩ 〛 η
                        ≡⟨ refl ⟩
                         proj₂ ((〚 e₁ 〛 η) , (〚 e₂ 〛 η))
                        ≡⟨ refl ⟩
                         〚 e₂ 〛 η
                        ∎


-- beta reduction
β-reduction : ∀ {Γ : Ctx} {η : 〚 Γ 〛ᶜ} {A : Type} {B : Type} {e₁ : (Γ ∷ A) ⊢ B} {e₂ : Γ ⊢ A} → 〚 (fun e₁) · e₂ 〛 η ≡ 〚 e₁ 〛 (η , 〚 e₂ 〛 η)
β-reduction {Γ} {η} {A} {B} {e₁} {e₂} =
                            begin
                              〚 (fun e₁) · e₂ 〛 η
                            ≡⟨ refl ⟩
                              ( ( λ e₃ → (〚 e₁ 〛 (η , e₃)) ) ) (〚 e₂ 〛 η )
                            ≡⟨ refl  ⟩
                              〚 e₁ 〛 (η , 〚 e₂ 〛 η)
                            ∎
  
  






  
  
  


