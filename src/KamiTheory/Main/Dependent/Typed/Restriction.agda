
module KamiTheory.Main.Dependent.Typed.Restriction where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_ ; _≡⟨_⟩_ ; _∎ ; sym)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import Prelude.Equality using (eqReasoningStep ; _∎ ; cong ; sym )

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.Basics hiding (wk)
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Typed.Instances

-- open import KamiTheory.Data.Open.Definition
-- open import KamiTheory.Data.UniqueSortedList.Definition
-- open import KamiTheory.Order.StrictOrder.Base


-- data isLoc


module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}}
       {{_ : isDecidablePreorder ′ P ′}}
       {{_ : hasDecidableEquality P}} where

  private variable
    -- n m : Nat
    p q : Term P n
    Γ  : Con (Term P) n
    A B : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Term P n
    t s : Term P n
    f g : Term P n
    U V R W W₀ W₁ : P


  restrict-GenTs : ∀{bs} -> P -> GenTs (Term P) n bs -> GenTs (Term P) n bs
  restrict : P -> Term P n -> Term P n

  restrict-GenTs P [] = []
  restrict-GenTs P (t ∷ ts) = restrict P t ∷ restrict-GenTs P ts

  restrict W₁ (var x) = var x
  restrict W₁ (constₜ x) = constₜ x
  restrict W₁ (gen 𝓀-loc (constₜ (location U) ∷ (t ∷ []))) with decide-≤ U W₁
  ... | no x = gen (main 𝓀-locskip) []
  ... | yes x = gen 𝓀-loc ((constₜ (location U)) ∷ (restrict W₁ t) ∷ [])
  restrict W₁ a@(gen 𝓀-loc (c ∷ (t ∷ []))) = a -- IMPOSSIBLE in well-typed terms
  restrict W₁ (gen (main k) c) = gen (main k) (restrict-GenTs W₁ c)

  lemma0 : ∀ W (B : Term P _) (σ : Subst P m n)
         -> restrict W (subst σ B) ≡ (subst (λ x -> restrict W (σ x)) (restrict W B))
  lemma0 W B a = {!!}


  mutual
    lemma6 : ∀ {W a bs} {c : GenTs (Term P) (1+ n) bs} → (restrict-GenTs {n = n} {bs} W (substGen (sgSubst a) c)) ≡ (substGen (sgSubst (restrict W a)) (restrict-GenTs W c))
    lemma6 {c = []} = refl
    lemma6 {W = W} {a = a} {c = _∷_ {b = b} t c} =
       _ ≡⟨ cong (_ ∷_) lemma6 ⟩
       _ ≡⟨ cong (_∷ _) (lemmagen b W t a)⟩ _ ∎

    helper2 : ∀ b W (B : Term P _) (a : Term P n) → (restrict W (subst (liftSubst (liftSubstn (consSubst var a) b)) B)) ≡ (subst (liftSubst (liftSubstn (consSubst var (restrict W a)) b)) (restrict W B))
    helper2 = {!!}

    lemmagen : ∀ b W (B : Term P _) (a : Term P n) -> restrict W (subst (liftSubstn (sgSubst a) b) B) ≡ subst (liftSubstn (sgSubst (restrict W a)) b) (restrict W B)
    lemmagen n0 W (var zero) a = refl
    lemmagen n0 W (var (suc x)) a = refl
    lemmagen n0 W (constₜ x) a = refl
    lemmagen n0 W (gen (main x) []) a = refl
    lemmagen n0 W (gen 𝓀-loc (constₜ (location U) ∷ (t ∷ []))) a with decide-≤ U W
    ... | no x = refl
    ... | yes x = cong (loc U) (lemmagen 0 W t a)
    lemmagen n0 W (gen (main x) (_∷_ {b = b} {bs} t c)) a =
      cong (gen (main x))
      (_ ≡⟨ cong (_∷ _) (lemmagen b W t a) ⟩
       _ ≡⟨ cong (_ ∷_) lemma6 ⟩  _ ∎)
    lemmagen n0 W (gen 𝓀-loc (c ∷ (t ∷ []))) a = {!!}

    lemmagen (1+ b) W (var zero) a = refl
    lemmagen (1+ b) W (var (suc x)) a = restrict W ((liftSubst (liftSubstn (sgSubst a) b)) (suc x)) ≡⟨ {!lemmagen b W ? a!} ⟩
      (liftSubst (substVar (liftSubstn (sgSubst (restrict W a)) b))) (suc x)
      ≡⟨ ? ⟩
      (liftSubst (liftSubstn (sgSubst (restrict W a)) b))
      (suc x) ∎



-- restrict W (wk (step id) ((liftSubstn (sgSubst a) b) x)) ≡⟨ {!x!} ⟩ restrict W (wk (step id) ((liftSubstn (sgSubst a) b) x)) ≡⟨ {!!} ⟩ wk (step id) ((liftSubstn (sgSubst (restrict W a)) b) x) ∎
    lemmagen (1+ b) W (gen 𝓀-loc (constₜ (location U) ∷ (t ∷ []))) a with decide-≤ U W
    ... | no x = refl
    ... | yes x = cong (loc U) (lemmagen (1+ b) W t a)
    lemmagen (1+ b) W (gen (main x) []) a = cong (gen (main x)) refl
    lemmagen (1+ b) W (gen (main x) (_∷_ {b = b₁} t c)) a = cong (gen (main x)) {!!}
    lemmagen (1+ b) W (gen 𝓀-loc (c ∷ (t ∷ []))) a = {!!}
    lemmagen (1+ b) W (constₜ x) a = refl


  lemma1 : ∀ W (B : Term P _) (a : Term P n) -> restrict W (B [ a ]) ≡ (restrict W B [ restrict W a ])
  lemma1 W B a = lemmagen 0 W B a
  
{-

  mutual
    lemma6 : ∀ {W a bs} {c : GenTs (Term P) (1+ n) bs} → (restrict-GenTs {n = n} {bs} W (substGen (sgSubst a) c)) ≡ (substGen (sgSubst (restrict W a)) (restrict-GenTs W c))
    lemma6 {c = []} = refl
    lemma6 {W = W} {a = a} {c = _∷_ {b = b} t c} =
       _ ≡⟨ cong (_ ∷_) lemma6 ⟩
       _ ≡⟨  cong (_∷ _) (lemmagen b W t a)⟩ _ ∎

    lemma1 : ∀ W (B : Term P _) (a : Term P n) -> restrict W (B [ a ]) ≡ (restrict W B [ restrict W a ])
    lemma1 W (var zero) a = refl
    lemma1 W (var (suc x)) a = refl
    lemma1 W (constₜ x) a = refl
    lemma1 W (gen (main x) []) a = refl
    lemma1 W (gen (main x) (_∷_ {b = b} {bs} t c)) a =
      cong (gen (main x))
           ((restrict W (subst (liftSubstn (sgSubst a) b) t) ∷ restrict-GenTs W (substGen (sgSubst a) c))
            ≡⟨ cong (_∷ _) ((lemma1 W {!t!} {!!})) ⟩
            (subst (liftSubstn (sgSubst (restrict W a)) b) (restrict W t) ∷ restrict-GenTs W (substGen (sgSubst a) c))
            ≡⟨  cong (_ ∷_) lemma6 ⟩             
        (subst (liftSubstn (sgSubst (restrict W a)) b) (restrict W t) ∷
         substGen (sgSubst (restrict W a)) (restrict-GenTs W c)) ∎)

       
    lemma1 W (gen 𝓀-loc (constₜ (location U) ∷ (t ∷ []))) a with decide-≤ U W
    ... | no x = refl
    ... | yes x = cong (loc U) (lemma1 W t a)
    
    lemma1 W (gen 𝓀-loc (c ∷ (t ∷ []))) a =  restrict W (gen 𝓀-loc (c ∷ (t ∷ [])) [ a ]) ≡⟨ {!refl!} ⟩ (gen 𝓀-loc (c ∷ (t ∷ [])) [ restrict W a ]) ≡⟨ cong (_[ restrict W a ]) refl ⟩ restrict W (gen 𝓀-loc (c ∷ (t ∷ []))) [ restrict W a ] ∎ -- IMPOSSIBLE in well-typed terms

-}

{-
  restrict-Con : P -> Con (Term P) n -> Con (Term P) n
  restrict-Con W₁ ε = ε
  restrict-Con W₁ (Γ ∙ x) = (restrict-Con W₁ Γ) ∙ (restrict W₁ x)


  restrict-Ctx : W₁ ≤ W₀ -> W₀ ⊢Ctx Γ -> W₁ ⊢Ctx restrict-Con W₁ Γ
  restrict-Entry : W₁ ≤ W₀
                   -> W₀ ∣ Γ ⊢Entry A
                   -> W₁ ∣ restrict-Con W₁ Γ ⊢Entry restrict W₁ A

  restrict-Sort : W₁ ≤ W₀ -> W₀ ∣ Γ ⊢Sort A -> W₁ ∣ restrict-Con W₁ Γ ⊢Sort restrict W₁ A

  restrict-Term : W₁ ≤ W₀
                  -> W₀ ∣ Γ ⊢ t ∶ A / p
                  -> W₁ ∣ restrict-Con W₁ Γ ⊢ restrict W₁ t ∶ restrict W₁ A / restrict W₁ p

  restrict-Ctx ϕ ε = ε
  restrict-Ctx ϕ (Γ ∙ x) = (restrict-Ctx ϕ Γ) ∙ restrict-Entry ϕ x

  restrict-Entry ϕ UUⱼ = {!!}
  restrict-Entry ϕ NNⱼ = {!!}
  restrict-Entry ϕ Emptyⱼ = {!!}
  restrict-Entry ϕ Unitⱼ = {!!}
  restrict-Entry ϕ (Πⱼ T ▹ T₁) = Πⱼ restrict-Entry ϕ T ▹ restrict-Entry ϕ T₁
  restrict-Entry ϕ (Σⱼ T ▹ T₁) = {!!}
  restrict-Entry ϕ (Univ-Comⱼ x) = {!!}
  restrict-Entry ϕ (Locⱼ U T) = {!!}
  restrict-Entry ϕ (Comⱼ T) = {!!}
  restrict-Entry ϕ (Endⱼ T) = {!!}
  restrict-Entry ϕ (T ≫ⱼ T₁) = {!!}
  restrict-Entry ϕ (Shareⱼ U V ϕ₁ T) = {!!}
  restrict-Entry ϕ (Vecⱼ A t) = Vecⱼ (restrict-Entry ϕ A) (restrict-Term ϕ t)

  restrict-Term ϕ (comⱼ x t) = {!!}
  restrict-Term ϕ (comtypeⱼ x t) = {!!}
  restrict-Term ϕ (comvalⱼ x t) = {!!}
  restrict-Term ϕ (endⱼ t) = {!!}
  restrict-Term ϕ (t >ⱼ t₁) = {!!}
  restrict-Term ϕ (shareⱼ x t ϕ₁) = {!!}
  restrict-Term {W₁ = W₁} {W₀ = W₀} ϕ (locⱼ {U = U} ψ t) with decide-≤ U W₁
  ... | no x = locskipⱼ {!!}
  ... | yes ψ' = locⱼ ψ' (restrict-Term ϕ t)
  restrict-Term ϕ (locskipⱼ ¬ψ) = locskipⱼ λ ζ -> ¬ψ (ζ ⟡ ϕ)
  restrict-Term ϕ (unlocⱼ t) = {!!}
  restrict-Term ϕ ℕⱼ = {!!}
  restrict-Term ϕ (Vecⱼ t t₁) = {!!}
  restrict-Term ϕ (var x) = {!!}
  restrict-Term ϕ (lamⱼ A t) = lamⱼ (restrict-Entry ϕ A ) (restrict-Term ϕ t)
  restrict-Term {W₁ = W₁} {W₀ = W₀} ϕ (_∘ⱼ_ {B = B} {a = a} t s) rewrite lemma1 W₁ B a = restrict-Term ϕ t ∘ⱼ restrict-Term ϕ s
  restrict-Term ϕ (prodⱼ A B t t₁) = {!!}
  restrict-Term ϕ (fstⱼ _ B t) = {!!}
  restrict-Term ϕ (sndⱼ A B t) = {!!}
  restrict-Term ϕ (zeroⱼ {{ΓP = because ΓP}}) = zeroⱼ {{ΓP = because (restrict-Ctx ϕ ΓP)}}
  restrict-Term ϕ (sucⱼ t) = {!!}
  restrict-Term ϕ (natrecⱼ x t t₁ t₂) = {!!}
  restrict-Term ϕ nilⱼ = {!!}
  restrict-Term ϕ (consⱼ t t₁) = {!!}
  restrict-Term ϕ (vecrecⱼ t t₁ t₂) = {!!}

  restrict-Sort ϕ (UUⱼ {{ΓP = ΓP}}) = {!UUⱼ!}
  restrict-Sort ϕ NNⱼ = {!!}
  restrict-Sort ϕ (Vecⱼ J x) = {!!}
  restrict-Sort ϕ Emptyⱼ = {!!}
  restrict-Sort ϕ Unitⱼ = {!!}
  restrict-Sort ϕ (Πⱼ x ▹ J) = {!!}
  restrict-Sort ϕ (Σⱼ x ▹ J) = {!!}
  restrict-Sort ϕ (Locⱼ U J) = {!!}

-}


