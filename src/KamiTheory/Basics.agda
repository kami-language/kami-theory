
module KamiTheory.Basics where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Sum.Base
open import Agda.Builtin.Nat using (Nat; zero; suc)

--------------------------------------------------
-- equality

open import Agora.Conventions using (_≡_ ; refl-≡)

-- we say refl instead of refl-≡
pattern refl = refl-≡

--------------------------------------------------
-- decidable equality




--------------------------------------------------
-- derivability syntax sugar


open import Agora.Conventions using (Maybe ; just)

record isDerivable {𝑖} (A : Set 𝑖) : Set 𝑖 where
  field derive : Maybe A

open isDerivable {{...}} public

record isTrue {𝑖} (A : Set 𝑖) : Set 𝑖 where
  constructor because
  field proof : A

open isTrue {{...}} public

instance
  isTrue:isDerivable : ∀{𝑖} {A : Set 𝑖} -> {{der : isDerivable A}} {a : A} -> {{_ :  derive {{der}} ≡ just a}} -> isTrue A
  isTrue:isDerivable {a = a} = record { proof = a }


--------------------------------------------------
-- others

_↯_ : ∀ {𝒶 ℓ} {A : Set 𝒶} {W : Set ℓ} → A → ¬ A → W
a ↯ ¬a = ⊥-elim (¬a a)

length : ∀ {A : Set} → List A → Nat
length []        =  zero
length (x ∷ xs)  =  suc (length xs)



----------------------------------------------------------
--

open Agora.Conventions
open import Data.Fin

macro
  𝔽 : ∀ n -> _
  𝔽 n = #structureOn (Fin n)


----------------------------------------------------------
--
record ∑ₕ {A : 𝒰 𝑖} (B : {{_ : A}} -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  constructor make∑ₕ
  field {{fst}} : A
  field snd : B {{fst}}
open ∑ₕ public

pattern _,ₕ_ f s = make∑ₕ {{f}} s
infixr 30 _,ₕ_

record hasNotation-! (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field _! : (a : A) -> B a
  infixl 200 _!

open hasNotation-! {{...}} public

record hasNotation-wk (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field wk : (a : A) -> B a

open hasNotation-wk {{...}} public

record hasNotation-𝕠 (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field 𝕠 : (a : A) -> B a

open hasNotation-𝕠 {{...}} public


record hasNotation-refine (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) : 𝒰 (𝑖 ､ 𝑗) where
  field refine : (a : A) -> B a

open hasNotation-refine {{...}} public

record hasNotation-⋆ (A : 𝒰 𝑖) (B : A -> 𝒰 𝑗) (C : ∀(a : A) -> B a -> 𝒰 𝑘) : 𝒰 (𝑖 ､ 𝑗 ､ 𝑘) where
  field _⋆_ : (a : A) -> (b : B a) -> C a b

  infixl 40 _⋆_

open hasNotation-⋆ {{...}} public



module _ {A B : 𝒰 𝑖} where
  transp-≡ : (A ≡ B) -> A -> B
  transp-≡ refl-≡ a = a

module _ {A : 𝒰 𝑖} {B : 𝒰 𝑗} {C : 𝒰 𝑘} where
  cong₂-≡ : (f : A -> B -> C) -> ∀{a₀ a₁ : A} -> ∀{b₀ b₁ : B} -> a₀ ≡ a₁ -> b₀ ≡ b₁ -> f a₀ b₀ ≡ f a₁ b₁
  cong₂-≡ f refl-≡ refl-≡ = refl-≡

-- cong-≡ : {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> (f : (a : A) -> B a) -> {a b : A} -> (a ≡ b) -> f a ≡ f b
cong-≡ : {A : 𝒰 𝑖} {B : 𝒰 𝑗} -> (f : A -> B) -> {a b : A} -> (a ≡ b) -> f a ≡ f b
cong-≡ f refl-≡ = refl-≡

ap₀ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≡ b -> A
ap₀ {a = a} _ = a

ap₁ : ∀{A : 𝒰 𝑖} {a b : A} -> a ≡ b -> A
ap₁ {b = b} _ = b

J1 : ∀{A : 𝒰 𝑖} {B : 𝒰 𝑘} -> ∀{a b : A} -> (p : a ≡ b) -> (F : A -> 𝒰 𝑗) -> (f : ∀ a -> F a -> B) -> (x : F a) -> f b (transp-≡ (cong-≡ F p) x) ≡ f a x
J1 refl-≡ F f x = refl-≡

K1 : ∀{A : 𝒰 𝑖} -> {a : A} -> (p : a ≡ a) -> p ≡ refl-≡
K1 refl-≡ = refl-≡

-- _≡⟨_⟩≡_ : {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} -> {a₀ a₁ : A} -> (b₀ : B a₀) -> (a₀ ≡ a₁) -> (b₁ : B a₁) -> 𝒰 _
-- _≡⟨_⟩≡_ b₀ p b₁ = transp-≡ (cong-≡ _ p) b₀ ≡ b₁

_≡⟨_⟩≡_ : {A B : 𝒰 𝑖} -> (a : A) -> (A ≡ B) -> (b : B) -> 𝒰 _
_≡⟨_⟩≡_ a p b = transp-≡ p a ≡ b

--  : ∀{A : 𝒰 𝑖} -> ∀{a b : A} -> (p : a ≡ b) -> (B : A -> 𝒰 𝑗) -> {C : (a : A) -> (B a) -> 𝒰 𝑘}  -> (f : ∀ a -> (b : B a) -> C a b) -> (x : B a) -> f a (transp-≡ (cong-≡ B p) x) ≡ f b x
-- J2 = ?
-- J1 refl-≡ F f x = refl-≡


-- module _ {A : 𝒰 𝑖} {B : A -> 𝒰 𝑗} {C : ∀ a -> B a -> 𝒰 𝑘} where
--   cong₂d-≡ : (f : (a : A) -> (b : B a) -> C a b) -> ∀{a₀ a₁ : A} -> (p : a₀ ≡ a₁) -> ∀{b₀ : B a₀} -> {b₁ : B a₁} -> transp-≡ (cong-≡ B p) b₀ ≡ b₁ -> J1 p B f b₀ ≡ f a₁ b₁
--   cong₂d-≡ f = ?
  -- refl-≡ refl-≡ = refl-≡


typed : (A : 𝒰 𝑖) -> A -> A
typed A a = a

syntax typed A a = a ∶ A

module _ {A : 𝒰 𝑖} where
  head-≡ : {a b : A} {as bs : List A} -> (a ∷ as) ≡ (b ∷ bs) -> a ≡ b
  head-≡ refl-≡ = refl-≡

  tail-≡ : {a b : A} {as bs : List A} -> (a ∷ as) ≡ (b ∷ bs) -> as ≡ bs
  tail-≡ refl-≡ = refl-≡


