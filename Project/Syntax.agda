module Project.Syntax where
open import Relation.Binary
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂; _,_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎)
open import Data.Nat.Properties

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


-- primeri programov

-- primer:
--   kontekst:     x₀ : Nat
--   tip programa: Nat × Nat ⇒ Nat × Nat
--   koda:         λ p . (x0, fst p)
--
--   Python: lambda p: (x0,  p[0])

primer1 : (● ∷ Nat) ⊢ ((Nat ×' Nat) ⇒' (Nat ×' Nat))
primer1 = λ' ⟨ (var (∈'-there ∈'-here)) , fst' (var (∈'-here)) ⟩


-- primer: seštevanje
-- kontekst: poljuben
-- tip programa: Nat ⇒ Nat ⇒ Nat
-- koda: plus := (λ m . λ n . primrec m n (λ x . suc x))
-- premisli, da je to seštevanje:


plus : {Γ : Ctx'} → Γ ⊢ (Nat ⇒' (Nat ⇒' Nat))
plus =  λ' ( λ' ( primrec (var ( ∈'-there ∈'-here ) ) ( var ( ∈'-here ) ) ( ( suc' ( var ( ∈'-here ) ) ) ) ) )


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



--primer: mnozenje
-- kontekst: poljuben
-- tip programa: Nat ⇒ Nat ⇒ Nat

krat : {Γ : Ctx'} → Γ ⊢ (Nat ⇒' (Nat ⇒' Nat))
krat =  λ' ( λ' ( primrec ( var ( ∈'-there ∈'-here ) ) zero' ( ( plus ·'  ( var (∈'-there (∈'-there ∈'-here ) ) ) ) ·' ( ( var (∈'-here )  )  ) ) ) )


test : ● ⊢ Nat
test =( plus ·' (suc' (suc' zero'))) ·' (suc' (suc' (suc' (suc' (suc' zero')))))

test2 : ● ⊢ Nat
test2 =( krat ·' (suc' (suc' (suc' zero')))) ·' ((suc' (suc' (suc' (suc' (suc' zero'))))))


numeral : ℕ → { Γ : Ctx' } → Γ ⊢ Nat
numeral zero = zero'
numeral (suc n) = suc' (numeral n)

--   primrec 0 x h = x
primrec-zero-≡ : ∀ {Γ : Ctx'} {η : 〚 Γ 〛ᶜ} {A : Type} {x : Γ ⊢ A} {h : ((Γ ∷ Nat) ∷ A) ⊢ A} →
                 (〚 primrec zero' x h 〛 η ) ≡ (〚 x  〛 η )
primrec-zero-≡ {Γ} {η} {A} {x} {h} =
               begin
                 〚 primrec zero' x h 〛 η
                 ≡⟨  refl ⟩
                  ( prec  ( 〚 zero' 〛 η )  ( 〚 x 〛 η ) (λ x1 → ( λ x2 → (〚 h 〛 ( ( η , x1) , x2 ) ) ) ) )
                 ≡⟨ refl ⟩
                   (〚 x  〛 η )
                 ∎

primrec-step-≡ : ∀ {Γ : Ctx'} {η : 〚 Γ 〛ᶜ} {A : Type} {n : Γ ⊢ Nat} {y : Γ ⊢ A}  {h : ((Γ ∷ Nat) ∷ A) ⊢ A} →
                 (〚 primrec (suc' n) y h 〛 η ) ≡  (λ x1 → ( λ x2 → (〚 h 〛 ( ( η  , x1) , x2 ) ) ) ) (〚 n 〛 η ) (〚 primrec n y h 〛 η )
primrec-step-≡ {Γ} {η} {A} {n} {y} {h} =
               begin
                  (〚 primrec (suc' n) y h 〛 η )
                 ≡⟨ refl ⟩
                  ( prec ( 〚 suc' n 〛  η ) ( 〚 y 〛  η ) (λ x1 → ( λ x2 → (〚 h 〛 ( ( η , x1) , x2 ) ) ) ) )
                  ≡⟨ refl  ⟩
                  (λ x1 → ( λ x2 → (〚 h 〛 ( ( η  , x1) , x2 ) ) ) ) (〚 n 〛 η ) (〚 primrec n y h 〛 η )
                 ∎


-- sestevanje
pomozna-sestevanje : ∀ {Γ : Ctx'} {η : 〚 Γ 〛ᶜ} (n : ℕ) → 〚 numeral n 〛 η ≡ n
pomozna-sestevanje {Γ} {η} zero = refl
pomozna-sestevanje {Γ} {η} (suc n) =
                           begin
                             suc (〚 numeral n 〛 η)
                           ≡⟨ cong suc (pomozna-sestevanje n) ⟩
                             suc n
                           ∎

sestevanje-≡ :  ∀ {Γ : Ctx'} {η : 〚 Γ 〛ᶜ} → (m n : ℕ) → 〚 ( plus ·' (numeral m)) ·' (numeral n) 〛 η ≡ m + n
sestevanje-≡  {Γ} {η} zero n =
                      begin
                        〚 numeral n 〛 η
                      ≡⟨ pomozna-sestevanje n  ⟩
                         n
                      ∎
sestevanje-≡  {Γ} {η} (suc m) n =
                  begin
                    suc (prec (〚 numeral m 〛 η) (〚 numeral n 〛 η) (λ x1 x2 → suc x2))
                  ≡⟨  cong suc (sestevanje-≡ m n)  ⟩
                    suc m + n
                  ∎ 








  
  
  


