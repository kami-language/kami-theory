
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Instances where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Modality.Definition

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product


-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

-- module Typecheck (P' : Preorder (ℓ₀ , ℓ₀ , ℓ₀)) {{_ : hasDecidableEquality ⟨ P' ⟩}} {{_ : isDecidablePreorder ′ ⟨ P' ⟩ ′}} {{_ : hasFiniteMeets ′ ⟨ P' ⟩ ′}} where
-- {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

module Typecheck (P : ModeSystem 𝑖) where

  open Judgements P

  -- private
  --   P : 𝒰 _
  --   P = ⟨ graph P' ⟩

  private variable
    -- n m : Nat
    k l : Mode P
    μs : ModeHom P k l
    p q : Term P n
    t u : Term P n
    Γ  : Con (Entry P) n
    A B : Term P n
    E F : Entry P n
    M : Restriction k n
    -- W : P


  Result : 𝒰 𝑖 -> 𝒰 𝑖
  Result X = String +-𝒰 X

  map-Result : ∀{A B : 𝒰 𝑖} -> (A -> B) -> Result A -> Result B
  map-Result f (left a) = left a
  map-Result f (right b) = right (f b)

  bind-Result : ∀{A B : 𝒰 𝑖} -> Result A -> (A -> Result B) -> Result B
  bind-Result (left a) f = left a
  bind-Result (right b) f = f b

  private
    -- _>>=_ = bind-Maybe
    _>>=_ = bind-Result


  {-# TERMINATING #-}
  derive-Entry : ∀ (Γ : Con (Entry P) n) E -> Result (Γ ⊢Entry E)
  derive-Ctx : ∀ (Γ : Con (Entry P) n) -> (M : Restriction k n) -> Result (⊢Ctx Γ ∥ M)
  derive-Term-Sort↓,Mod↓ : ∀ Γ -> (t A : Term P n) → (p : Restriction k n) -> Result (Γ ⊢ t ∶ A ∥ p)

  derive-Term-Sort↑,Mod↑ : ∀ Γ -> (t : Term P n) → Result (∑ λ (E : Target n) -> (Γ ⊢ t ∶ E))

  derive-Term-Sort↑,Mod↓ : ∀ Γ -> (t : Term P n) (M : Restriction k n) → Result (∑ λ (A : Term P n) -> (Γ ⊢ t ∶ A ∥ M))


  derive-Entry Γ (UU ∥ μs)    = map-Result (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Entry Γ (NN ∥ μs)    = map-Result (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Entry Γ (BB ∥ μs)    = map-Result (λ P -> BBⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Entry Γ (Vec A t ∥ μs) = do
    A′ <- derive-Entry Γ (A ∥ μs )
    t′ <- derive-Term-Sort↓,Mod↓ Γ t NN (μs)
    just (Vecⱼ A′ t′)

  derive-Entry Γ (_∥_ {k = k} (gen (main 𝓀-Modal) (incl (l ↝ k0 ∋ μ) ⦊ term A ∷ []))(M)) with k0 ≟ k
  ... | no p = no ""
  ... | yes refl-≡ = do
          A' <- derive-Entry Γ (A ∥ μ ↳ M)
          just (Modalⱼ A')



  derive-Entry Γ (var x ξ ∥ M) = do
    res <- derive-Term-Sort↓,Mod↓ Γ (var x ξ) UU M
    just (Univⱼ res)
  derive-Entry Γ ((t ∘[ μ ] s) ∥ M) = do
    res <- derive-Term-Sort↓,Mod↓ Γ (t ∘[ μ ] s) UU M
    just (Univⱼ res)
  derive-Entry Γ ((Π A // incl (_ ↝ k ∋ μ) ▹ B) ∥[ l ] M) with k ≟ l
  ... | no _ = no "fail in Entry Π"
  ... | yes refl = do
    A' <- derive-Entry Γ (A ∥ (μ ↳ M))
    B' <- derive-Entry (Γ ∙ (A / μ)) (B ∥ (id ∷ M))
    just (Πⱼ A' ▹ B')
  -- derive-Entry Γ ((Σ A // incl (k0 ↝ k ∋ μ) ▹ B) // l ↝ _ ∋ η) with k ≟ l
  -- ... | no _ = no "fail in Entry Σ"
  -- ... | yes refl with k0 ≟ k
  -- ... | no _ = no "fail in Entry Σ"
  -- ... | yes refl with μ ≟ id
  -- ... | no _ = no "fail in Entry Σ"
  -- ... | yes refl = do
  --   A' <- derive-Entry Γ (A / η)
  --   B' <- derive-Entry (Γ ∙ (A / η)) (B / η)
  --   just (Σⱼ A' ▹ B')
  derive-Entry Γ E = no "fail in Entry: not implemented"


  derive-Ctx ε [] = just ε
  derive-Ctx (Γ ∙ (A // (_ ↝ b ∋ μ))) (_∷_ {l = l} η M)
    with l ≟ b
  ... | no p = no ""
  ... | yes refl = do
    E' <- derive-Entry Γ (A ∥ μ ↳ M)
    Γ' <- derive-Ctx Γ M
    just (Γ' ∙ E')


  -- infer-Var : ∀ Γ -> (t : Fin n) -> (M : Restriction k n) -> ∑ λ (E : Entry P n) -> ∑ λ (η : ModeHom P k l) -> t ∶ E ⇒ η ∈ Γ ∥ M
  -- infer-Var (Γ ∙ (A // μ)) x0 (η ∷ M) = _ , _ , zero {ω = hom μ} {η = η} {M = M}
  -- infer-Var (Γ ∙ x) (_+1 t) (η ∷ M)
  --   with ((A // μ) , η , Ep) <- infer-Var Γ t M = _ , _ , suc Ep


  derive-Var-Sort↑,Mod↓ : ∀ Γ -> (t : Fin n) -> (M : Restriction k n) -> (∑ λ (E : Entry P n) -> ∑ λ l -> ∑ λ (η : ModeHom P k l) -> t ∶ E ⇒ η ∈ Γ ∥ M)
  derive-Var-Sort↑,Mod↓ (Γ ∙ (A // μ)) x0 (Judgements._∷_ {l = l₁} η M) = (_ , _ , _ , zero {ω = hom μ} {η = η} {M = M})
  -- -- ... | no _ = no "fail in derive-Var, dom/cod don't match"
  -- ... | yes refl = yes 
  derive-Var-Sort↑,Mod↓ (Γ ∙ x) (_+1 t) (η ∷ M)
    with derive-Var-Sort↑,Mod↓ Γ t M
  ... | ((A // μ) , _ , _ , X) = (_ , _ , _ , suc X)

  -- derive-Var-Sort↓,Mod↓ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → (p : SomeModeHom P) -> Maybe (t ∶ A // p ∈ Γ)
  -- derive-Var-Sort↓,Mod↓ Γ t A p = {!!}
  -- with infer-Var Γ t
  -- ... | (E , η , Ep) with E ≟ (A // p)
  -- ... | no p = nothing
  -- ... | yes refl-≡ = yes Ep

  -- derive-Var-Sort↓,Mod↑ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → Maybe (∑ λ μs -> t ∶ A // μs ∈ Γ)
  -- derive-Var-Sort↓,Mod↑ Γ t A with infer-Var Γ t
  -- ... | ((A' // μs) , Ap) with A ≟ A'
  -- ... | no p = nothing
  -- ... | yes refl-≡ = yes (μs , Ap)


  ------------------------------------------------------------------------
  -- Terms (infering Sort, infering Mod)

  -- derive-Term-Sort↑,Mod↑ Γ (var x (incl (μ ⇒ η ∋ ξ)))
  --   with ((vA // μ') , A') <- infer-Var Γ x
  --   with (_ ↝ _ ∋ μ) ≟ μ'
  -- ... | no p = no "fail in Sort↑,Mod↑: var, modalities don't match"
  -- ... | yes refl = do
  --   G' <- derive-Ctx Γ
  --   just ((vA ^[ _ ⇒ _ ∋ ξ ] / η) , var A' (_ ⇒ _ ∋ ξ))

  derive-Term-Sort↑,Mod↑ Γ _ = no "fail in Sort↑,Mod↑: not implemented"


  ------------------------------------------------------------------------
  -- Terms (infering Sort, checking Mod)

  derive-Term-Sort↑,Mod↓ {k = k} Γ (var x (incl (_⇒_∋_ {n = n} μ η ξ))) M
    with k ≟ n
  ... | no p = no "fail in Sort↑,Mod↓: var, modalities don't match"
  ... | yes refl

    with derive-Var-Sort↑,Mod↓ Γ x M
  ... | ((A // μ') , l , η' , Ap)

    with (_ ↝ _ ∋ μ) ≟ μ'
  ... | no p = no "fail in Sort↑,Mod↓: var, modalities don't match"
  ... | yes refl

    with _≟-SomeModeHom_ {M = P} (_ ↝ _ ∋ η) (_ ↝ _ ∋ η')
  ... | no p = no "fail in Sort↑,Mod↓: var, modalities don't match"
  ... | yes refl = do

    G' <- derive-Ctx Γ M
    yes (_ , var Ap ξ)

  derive-Term-Sort↑,Mod↓ Γ _ M = no "fail in Sort↑,Mod↓: not implemented"


  ------------------------------------------------------------------------
  -- Terms (checking Sort, checking Mod)

  -------------------
  -- modalities
  derive-Term-Sort↓,Mod↓ {k = k} Γ (mod[[ incl μ ]] t) (Modal A (incl μ')) M with μ ≟ μ'
  ... | no _ = no "fail in Sort↓,Mod↓: mod, modalities don't match"
  ... | yes refl with μ .cod ≟ k
  ... | no _ = no "fail in Sort↓,Mod↓: mod, modalities don't match"
  ... | yes refl with derive-Term-Sort↓,Mod↓ Γ t A (hom μ ↳ M)
  ... | no msg =  no ("fail in Sort↓,Mod↓: mod:: " <> msg)
  ... | yes Ap = yes (modⱼ Ap)


  derive-Term-Sort↓,Mod↓ {k = k} Γ (letunmod[[ incl μ ]] t into Y by s) Y' M
    with k ≟ cod μ
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, modalities don't match ")
  ... | yes refl

    with derive-Term-Sort↑,Mod↓ Γ t (hom μ ↳ M)
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes (T@(Modal X (incl η)) , tP)

   with cod η ≟ dom μ
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, modalities don't match ")
  ... | yes refl

    with derive-Entry (Γ ∙ (Modal X (incl η) / (hom μ))) (Y ∥ (id ∷ M))
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes Yp

    with derive-Term-Sort↓,Mod↓ (Γ ∙ (X / hom η ◆ hom μ)) s (Y [ mod[[ incl μ ]] (var x0 id) ]↑) (id ∷ M)
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes sP

    with Y [ t ] ≟ Y'
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, motive type doesn't match")
  ... | yes refl

    = yes (letunmodⱼ[ hom μ ] tP into Yp by sP)

  derive-Term-Sort↓,Mod↓ Γ (letunmod[[ incl μ ]] t into Y by s) Y' ω | yes _ | yes _ = no ("fail in Sort↓,Mod↓: letunmod, first term is not of modal type")


  -------------------
  -- standard MLTT - Terms of the universe

  derive-Term-Sort↓,Mod↓ Γ (UU) UU μs    = map-Result (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Term-Sort↓,Mod↓ Γ (NN) UU μs    = map-Result (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Term-Sort↓,Mod↓ Γ (BB) UU μs    = map-Result (λ P -> BBⱼ {{ΓP = because P}}) (derive-Ctx Γ μs)
  derive-Term-Sort↓,Mod↓ Γ (Vec A t) UU μs = do
    A′ <- derive-Term-Sort↓,Mod↓ Γ A UU μs
    t′ <- derive-Term-Sort↓,Mod↓ Γ t NN μs
    just (Vecⱼ A′ t′)

  derive-Term-Sort↓,Mod↓ {k = k} Γ (gen (main 𝓀-Modal) (incl (l ↝ k0 ∋ μ) ⦊ term A ∷ [])) UU (M) with k0 ≟ k
  ... | no p = no ""
  ... | yes refl-≡ = do
          A' <- derive-Term-Sort↓,Mod↓ Γ A UU (μ ↳ M)
          just (Modalⱼ A')


  derive-Term-Sort↓,Mod↓ {k = l} Γ (Π A // incl (_ ↝ k ∋ μ) ▹ B) UU M with k ≟ l
  ... | no _ = no "fail in Term-Sort↓,Mod↓ Π"
  ... | yes refl = do
    A' <- derive-Term-Sort↓,Mod↓ Γ A UU (μ ↳ M)
    B' <- derive-Term-Sort↓,Mod↓ (Γ ∙ (A / μ)) B UU (id ∷ M)
    just (Πⱼ A' ▹ B')





  -------------------
  -- standard MLTT - Terms
  derive-Term-Sort↓,Mod↓ Γ (var x (incl (μ ⇒ η ∋ ξ))) A M
    with derive-Var-Sort↑,Mod↓ Γ x M
  ... | ((vA // μ') , l , η' , A') with (_ ↝ _ ∋ μ) ≟ μ'
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl with _≟-SomeModeHom_ {M = P} (_ ↝ _ ∋ η) (_ ↝ _ ∋ η')
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl with vA ^[ _ ⇒ _ ∋ ξ ] ≟ A
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl = do
          G' <- derive-Ctx Γ M
          just (var A' (ξ))

  derive-Term-Sort↓,Mod↓ Γ (var x id) A μ = no "fail in Sort↓,Mod↓: var (id)"
  derive-Term-Sort↓,Mod↓ Γ (var x (fail msg)) A μ = no ("fail in Sort↓,Mod↓: var (fail): " <> msg)

  derive-Term-Sort↓,Mod↓ {k = k} Γ (lam↦ t) (Π A // (incl η) ▹ B) M
    with cod η ≟ k
  ... | no _ = no "fail in Sort↓,Mod↓: lam, modalities don't match."
  ... | yes refl = do
    A' <- derive-Entry Γ (A ∥ (hom η ↳ M))
    t' <- derive-Term-Sort↓,Mod↓ (Γ ∙ (A / (hom η))) t B (id ∷ M)
    just (lamⱼ A' ↦ t')

  derive-Term-Sort↓,Mod↓ {k = k} Γ (t ∘[[ incl η' ]] s) B' M with derive-Term-Sort↑,Mod↓ Γ t M
  ... | no p = no "fail in Sort↓,Mod↓: ∘"
  ... | yes (F , Fp) with F
  ... | (Π A // incl η ▹ B) with k ≟ cod η
  ... | no p = no "fail in Sort↓,Mod↓: ∘"
  ... | yes refl with η ≟ η'
  ... | no p = no "fail in Sort↓,Mod↓: ∘"
  ... | yes refl with derive-Term-Sort↓,Mod↓ Γ s A (hom η ↳ M)
  ... | no p = no "fail in Sort↓,Mod↓: ∘"
  ... | yes sP with B' ≟ (B [ untransform-Term s ])
  ... | no p = no "fail in Sort↓,Mod↓: ∘"
  ... | yes refl = just (Fp ∘ⱼ sP)
  derive-Term-Sort↓,Mod↓ Γ (t ∘[[ incl η' ]] s) B' p | yes _ | _ = no "fail in Sort↓,Mod↓: ∘, expected Π type"


  -- Boleans
  derive-Term-Sort↓,Mod↓ Γ (trueₜ) BB M with derive-Ctx Γ M
  ... | no p = no p
  ... | yes Γp = just (trueⱼ)
  -- ... | yes Γp = just (trueⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (falseₜ) BB M with derive-Ctx Γ M
  ... | no p = no p
  ... | yes Γp = just (falseⱼ )
  -- ... | yes Γp = just (falseⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (boolrec b into G false: f true: t) X μ with X ≟ G [ b ]
  ... | no p = no "fail in Sort↓,Mod↓: boolrec, Motive does not match"
  ... | yes refl = do
    bP <- derive-Term-Sort↓,Mod↓ Γ b BB μ
    GP <- derive-Entry (Γ ∙ (BB / id)) (G ∥ (id ∷ μ))
    fP <- derive-Term-Sort↓,Mod↓ Γ f (G [ falseₜ ]) μ
    tP <- derive-Term-Sort↓,Mod↓ Γ t (G [ trueₜ ]) μ
    yes (boolrecⱼ bP into GP false: fP true: tP)


  -- Naturals
  derive-Term-Sort↓,Mod↓ Γ (zeroₜ) NN M with derive-Ctx Γ M
  ... | no p = no p
  ... | yes Γp = just (zeroⱼ)
  -- ... | yes Γp = just (zeroⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (sucₜ t) NN μ with derive-Term-Sort↓,Mod↓ Γ t NN μ
  ... | no p = no p
  ... | yes tp = just (sucⱼ tp)


  derive-Term-Sort↓,Mod↓ Γ _ A p = no "fail in Sort↓,Mod↓: not implemented"

  instance
    isDerivable:Con : isDerivable (⊢Ctx Γ ∥ M)
    isDerivable:Con = record { derive = derive-Ctx _ _ }

  instance
    isDerivable:Entry : isDerivable (Γ ⊢Entry A ∥ M)
    isDerivable:Entry = record { derive = derive-Entry _ _ }
  instance
    isDerivable:Term : isDerivable (Γ ⊢ t ∶ A ∥ M)
    isDerivable:Term = record { derive = derive-Term-Sort↓,Mod↓ _ _ _ _ }


  -- typecheck : ∀{μs} -> {@(tactic solveWith (derive-Term-Sort↓,Mod↓ Γ t A μs)) derivation : Γ ⊢ t ∶ A // μs} -> Γ ⊢ t ∶ A // μs
  -- typecheck {derivation = derivation} = derivation

