
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Rules-OneSpace where

open import Agora.Conventions hiding (Σ ; Lift ; k ; m ; n)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_ ; _≰_ ; _/_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.UniqueSortedList hiding (img)
open import KamiD.Dev.2024-01-20.Space
open import KamiD.Dev.2024-01-20.Sheaf
open import KamiD.Dev.2024-01-20.Open
open import KamiD.Dev.2024-01-20.StrictOrder.Base

-- We have type contexts and normal contexts which additionally
-- contain location assignments.

---------------------------------------------
-- Base type layer

data BaseType : 𝒰₀ where
  BB NN : BaseType

--
-- We define a basic type theory with a global parameter P
--
Param = Space

private variable P : Param

---------------------------------------------
-- Normal type system layer


module _ {P : Param} where

  private variable
    U V W : ⟨ P ⟩

  data Ctx : 𝒰₀

  private variable
    Γ : Ctx

  -- setup of kinds for types and spaces
  data Kind : 𝒰₀ where
    type : Kind
    local : Kind
    com : ⟨ P ⟩ -> Kind

  private variable
    k l : Kind


  data _⊢Sort_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀

  private variable
    S : Γ ⊢Sort k
    T : Γ ⊢Sort l



  TypeSyntax : ∀ (Γ : Ctx) -> 𝒰 _
  TypeSyntax Γ = Γ ⊢Sort type

  syntax TypeSyntax Γ = Γ ⊢Type

  private variable
    A : Γ ⊢Type
    B : Γ ⊢Type

  LocalSyntax : ∀ (Γ : Ctx) -> 𝒰 _
  LocalSyntax Γ = Γ ⊢Sort local

  syntax LocalSyntax Γ = Γ ⊢Local

  private variable
    L : Γ ⊢Local
    M : Γ ⊢Local
    N : Γ ⊢Local

  ComSyntax : ∀ (Γ : Ctx) -> ⟨ P ⟩ -> 𝒰 _
  ComSyntax Γ U = Γ ⊢Sort com U

  syntax ComSyntax Γ U = Γ ⊢Com U

  private variable
    C : Γ ⊢Com U
    D : Γ ⊢Com V


  -- _⊢Mod_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀
  -- Γ ⊢Mod type = 𝟙-𝒰
  -- Γ ⊢Mod local = ⟨ P ⟩
  -- Γ ⊢Mod com x = Γ ⊢Type

  data _⊢Mod_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀ where
    type : Γ ⊢Mod type
    local : ⟨ P ⟩ -> Γ ⊢Mod local
    com : Γ ⊢Type -> Γ ⊢Mod (com U)

  private variable
    m : Γ ⊢Mod k
    n : Γ ⊢Mod l

  record _⊢Entry_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
    inductive ; pattern
    constructor _/_
    field fst : Γ ⊢Sort k
    field snd : Γ ⊢Mod k

  infixl 25 _/_

  open _⊢Entry_ public

  private variable
    E F : Γ ⊢Entry k


  data Ctx where
    [] : Ctx
    _,[_] : ∀ (Γ : Ctx) -> (A : Γ ⊢Entry k) -> Ctx

  infixl 30 _,[_]


  -- data _⊢Mods : (Γ : Ctx) -> 𝒰₀ where
  --   [] : [] ⊢Mods
  --   _,[_] : Γ ⊢Mods -> (m : Γ ⊢Mod k) -> {T : Γ ⊢Sort k} -> Γ ,[ T ] ⊢Mods


  data _⊢Var_ : ∀ Γ -> Γ ⊢Entry k -> 𝒰₀
  data _⊢_ : ∀ Γ -> Γ ⊢Entry k -> 𝒰₀

  private variable
    t : Γ ⊢ E
    s : Γ ⊢ F



  --------------------------------------------------------------
  -- Context setup

  data _⊢Ctx₊ : Ctx -> 𝒰₂

  _⋆-Ctx₊_ : ∀ (Γ : Ctx) -> Γ ⊢Ctx₊ -> Ctx

  data _⊢Ctx₊ where
    [] : Γ ⊢Ctx₊
    _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Entry k -> Γ ⊢Ctx₊

  -- _⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

  -- assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≣ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

  -- Δ ⋆-Ctx₊₂ [] = Δ
  -- Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≣ (cong-≣ _⇂_⊢Type (sym-≣ assoc-⋆-Ctx₊)) x ]

  Γ ⋆-Ctx₊ [] = Γ
  Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

  -- instance
  --   hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx) (_⊢Ctx₊) (λ _ _ -> Ctx)
  --   hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }


  {-

  assoc-⋆-Ctx₊ {E = []} = refl-≣
  assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
    let p = sym-≣ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
    in J1 p _⊢Type _,[_] x

  {-# REWRITE assoc-⋆-Ctx₊ #-}
  -}



  infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_


  -- End Context setup
  --------------------------------------------------------------


  wk-Sort : Γ ⊢Sort k -> Γ ,[ E ] ⊢Sort k
  su-Sort : (t : Γ ⊢ E) -> Γ ,[ E ] ⊢Sort k -> Γ ⊢Sort k

  wk-Entry : Γ ⊢Entry k -> Γ ,[ E ] ⊢Entry k
  su-Entry : (t : Γ ⊢ E) -> Γ ,[ E ] ⊢Entry k -> Γ ⊢Entry k

  wk-Term : Γ ⊢ E -> Γ ,[ F ] ⊢ wk-Entry E

  wk-Mod : Γ ⊢Mod k -> Γ ,[ E ] ⊢Mod k

  special-su-top : Γ ,[ E ] ⊢ wk-Entry F ->  Γ ,[ F ] ⊢Sort k -> Γ ,[ E ] ⊢Sort k
  special-su-top t T = {!!} -- su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)

  -- wk-Mod (type) m  = tt
  -- wk-Mod (local) m = m
  -- wk-Mod (com x) m = wk-Sort m





  {-# NO_POSITIVITY_CHECK #-}
  data _⊢Sort_ where

    --------------------------------------------------------------
    -- Generic
    ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    ⨅ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : (A B : Γ ⊢Sort k) -> Γ ⊢Sort k

    --------------------------------------------------------------
    -- Local

    Base : BaseType -> Γ ⊢Local

    Loc : (U : ⟨ P ⟩) -> Γ ⊢Local -> Γ ⊢Type

    Ext : Γ ⊢ Loc U L / type -> (ϕ : U ≤ V) -> Γ ⊢Type


    --------------------------------------------------------------
    -- Types
    Com : ⟨ P ⟩ -> Γ ⊢Type -> Γ ⊢Type

    --------------------------------------------------------------
    -- Com
    End : Γ ⊢Com U
    [_to[_⨾_⨾_]_⨾_]►_ : (L : Γ ⊢Local) -> ∀ W U V -> (ϕ : W ≤ U) -> (ψ : U ≤ V) -> Γ ,[ L ＠ V / type ] ⊢Com W -> Γ ⊢Com W



  -- infixr 40 _⇒_
  infixr 50 _⊗_

  syntax Loc U L = L ＠ U
  infixl 90 Loc


  data _⊢Var_ where
    zero : Γ ,[ E ] ⊢Var wk-Entry E
    suc : Γ ⊢Var E -> Γ ,[ F ] ⊢Var wk-Entry E





  ------------------------------------------------------------------------
  -- Weakening


  {-# TERMINATING #-}
  wk-Ctx₊ : (Δ : Γ ⊢Ctx₊) -> Γ ,[ E ] ⊢Ctx₊


  wk-Mod,ind : ∀ Δ -> (m : Γ ⋆-Ctx₊ Δ ⊢Mod k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Mod k

  wk-Sort,ind : ∀ Δ -> (S : Γ ⋆-Ctx₊ Δ ⊢Sort k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Sort k

  wk-Entry,ind : ∀ Δ -> (E : Γ ⋆-Ctx₊ Δ ⊢Entry k) -> Γ ,[ F ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Entry k
  wk-Entry,ind Δ (S / m) = wk-Sort,ind Δ S / wk-Mod,ind Δ m

  wk-Mod,ind Δ type = type
  wk-Mod,ind Δ (local x) = local x
  wk-Mod,ind Δ (com x) = com (wk-Sort,ind Δ x)


  wk-Term,ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Entry k} -> Γ ⋆-Ctx₊ Δ ⊢ AX -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢ wk-Entry,ind Δ AX

 --  wk-Term,ind [] t

  -- wk-Var-ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Sort k} -> Γ ⋆-Ctx₊ Δ ⊢Var AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Var wk-Sort,ind Δ AX

  wk-Ctx₊ [] = []
  wk-Ctx₊ (Δ ,[ E ]) = wk-Ctx₊ Δ ,[ wk-Entry,ind Δ E ]


  wk-Sort,ind Δ (Base x) = Base x
  wk-Sort,ind Δ (⨆ A B) = {!!}
  wk-Sort,ind Δ (⨅ S B) = ⨅ (wk-Entry,ind Δ S) (wk-Sort,ind (Δ ,[ S ]) B)
  wk-Sort,ind Δ (Loc U x) = Loc U (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (Ext x ϕ) = Ext (wk-Term,ind Δ x) ϕ -- ϕ (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (A ⊗ B) = wk-Sort,ind Δ A ⊗ wk-Sort,ind Δ B
  wk-Sort,ind Δ (Com x x₁) = {!!}
  wk-Sort,ind Δ End = End
  wk-Sort,ind Δ ([_to[_⨾_⨾_]_⨾_]►_ x U V W ϕ ψ P) = {!!}

  wk-Sort S = wk-Sort,ind [] S
  wk-Mod m = wk-Mod,ind [] m
  wk-Entry m = wk-Entry,ind [] m
  wk-Term t = wk-Term,ind [] t


  -- wk-Comm,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Comm ) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Comm 
  -- wk-Comm,ind E (⟮ U ↝ V ⨾ ϕ ⟯[ A ] Z) = ⟮ U ↝ V ⨾ ϕ ⟯[ wk-Sort,ind E A ] wk-Comm,ind (E ,[ Fill _ _ ]) Z
  -- wk-Comm,ind E End = End
  -- wk-Comm,ind E (El-Comm x) = El-Comm (wk-Term-ind E x)

  -- wk-Sort : Γ ⊢Sort k -> Γ ,[ A ] ⊢Sort k
  -- wk-Sort AX = wk-Sort,ind [] AX -- [ wk-⇛♮ id-⇛♮ ]-Type

  -- wk-≤-Local,ind E (Base b {ϕ = ϕ}) = Base b {ϕ = ϕ}
  -- wk-≤-Local,ind E (Fam ϕ m n) = Fam ϕ (wk-Term-ind E m) (wk-Term-ind E n)


  -- wk-Term : {AX : Γ ⊢Sort k} -> Γ ⊢ AX -> Γ ,[ A ] ⊢ wk-Sort AX
  -- wk-Term t = ? -- wk-Term-ind [] t


  -- wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

  -- weakening over a whole context
  -- wks-Sort : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Sort k) -> Γ ⋆-Ctx₊ E ⊢Sort k
  -- wks-Sort [] A = A
  -- wks-Sort (E ,[ x ]) A = wk-Sort (wks-Sort E A)

  -- β-wk-Sort,ind,empty : ∀{A : Γ ,[ B ] ⊢Sort k} -> wk-Sort,ind [] A ≣ A
  -- β-wk-Sort,ind,empty = ?



  -- End weakening
  ------------------------------------------------------------------------


  data _⊢_ where

    ---------------------------------------------
    -- Terms
    var : Γ ⊢Var E -> Γ ⊢ E

    b0 : Γ ⊢ Base BB / local U
    b1 : Γ ⊢ Base BB / local U
    n0 : Γ ⊢ Base NN / local U

    loc : Γ ⊢ L / local U -> Γ ⊢ (L ＠ U) / type
    [_]unloc : (ϕ : U ≤ V) -> Γ ⊢ (L ＠ U) / type -> Γ ⊢ L / local V

    fromext : {ϕ : U ≤ V} -> {val : Γ ⊢ L ＠ U / type} -> Γ ⊢ Ext val ϕ / type -> Γ ⊢ L ＠ V / type


    lam : Γ ,[ E ] ⊢ S / wk-Mod m  -> Γ ⊢ ⨅ E S / m
    app : Γ ⊢ ⨅ (T / m) S / m -> (t : Γ ⊢ T / m) -> Γ ⊢ su-Sort t S / m


    π₁ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ T / m
    π₂ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ S / m
    _,_ : Γ ⊢ T / m -> Γ ⊢ S / m -> Γ ⊢ (T ⊗ S) / m


    -------------------
    -- protocols
    _∋_ : (P : Γ ⊢Com U) -> Γ ⊢ P / com T -> Γ ⊢ Com U T / type

    _►_ : ∀{U V W : ⟨ P ⟩} -> {ϕ : U ≤ V} -> {ψ : V ≤ W}
        -> ∀ {C}
        -> (val : Γ ⊢ L ＠ V / type)
        -> Γ ,[ Ext val ψ / type ] ⊢ special-su-top (fromext (var zero) ) C / com (wk-Sort B)
        -> Γ ⊢ ([ L to[ U ⨾ V ⨾ W ] ϕ ⨾ ψ ]► C) / com B

    ret : Γ ⊢ B / type -> Γ ⊢ End {U = U} / com B

    -- inh : U ≰ ⊥ -> Γ ⊢ Inh U







    -- elim-BB : Γ ⊢ A -> Γ ⊢ A -> Γ ⊢ Base BB ⇒ wk-Sort A

    -- lam : (t : Γ ,[ A over One ] ⊢ B) -> Γ ⊢ A ⇒ B
    -- app : (f : Γ ⊢ A ⇒ B) -> (t : Γ ⊢ A) -> Γ ⊢ su-Sort t B

    -- forget : List ((List (Γ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a) -> Γ ⊢ Forget X




{-


  ------------------------------------------------------------------------
  -- Substitution

  su-Ctx₊ : (Γ ⊢ T) -> Γ ,[ T ] ⊢Ctx₊ -> Γ ⊢Ctx₊

  su-Sort,ind : (t : Γ ⊢ T) -> ∀ E -> (S : Γ ,[ T ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
  -- su-≤-Local,ind : {Γ : Ctx}{A : Γ ⊢Sort k} -> ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Local U} {BY : Γ ⋆-Ctx₊ E ⇂ V ⊢Local} -> .{ϕ : V ≤ U} -> _ ⇂ ϕ ⊢ AX ≤-Local BY -> _ ⇂ ϕ ⊢ su-Sort,ind {A = A} E AX ≤-Local su-Sort,ind E BY
  -- su-Term-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢ AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢ su-Sort,ind E AX
  -- su-Var-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢Var AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢Var su-Sort,ind E AX

  su-Ctx₊ t [] = []
  su-Ctx₊ t (E ,[ x ]) = su-Ctx₊ t E ,[ su-Sort,ind t _ x ]

  su-Sort,ind t E (Base x) = Base x
  su-Sort,ind t E (⨆ A B) = {!!}
  su-Sort,ind t E (⨅ S B) = ⨅ (su-Sort,ind t E S) (su-Sort,ind t (E ,[ S ]) B)
  su-Sort,ind t E _ = {!!}


  su-Sort t T = su-Sort,ind t [] T


  -- su-Ctx₊ : (E : Γ ,[ A ] ⊢Ctx₊) -> (t : Γ ⊢ A) -> Γ ⊢Ctx₊

  -- su₂-Type,ind : ∀ E -> {A : Γ ⊢Sort k} -> (t : Γ ⋆-Ctx₊ E ⊢ wks-Sort E A) -> (Z : Γ ,[ A ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
  -- su₂-Type,ind E t Y = ?

  special-su-top : Γ ,[ B ] ⊢ wk-Sort A ->  Γ ,[ A ] ⊢Sort k -> Γ ,[ B ] ⊢Sort k
  special-su-top t T = su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)

  -- End Substitution
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Equality

  data _⊢_≡_ : ∀ Γ {A : Γ ⊢Type} -> (a b : Γ ⊢ A) -> 𝒰₀ where
    -- β-rest-lam : ∀{F : Γ ,[ X ] ,[ A ] ⊢Type} {u v} (ϕ : Γ ⊢ u ≼ v) -> (t : Γ ,[ su-Sort v A ] ⊢ su-Sort,ind v _ F) -> Γ ⊢ rest (⨅ A F) ϕ (lam t) ≡ lam {!!}


  -- End Equality
  ------------------------------------------------------------------------

-}



module Examples where

  PP : Space
  PP = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))

  uu vv : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  vv = ⦗ # 1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])

  ε : Ctx {PP}
  ε = []

  T0 : ∀{Γ : Ctx {PP}} -> Γ ⊢Type
  T0 = (Base NN ＠ uu) ⊗ (Base NN ＠ vv)

  t1 : ε ⊢ ⨅ (T0 / type) (Base NN ＠ uu) / type
  t1 = lam (π₁ (var zero))

  t2 : ε ⊢ ⨅ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / type) ((Base NN ⊗ Base NN) ＠ uu) / type
  t2 = lam (loc ([ reflexive ]unloc (π₁ (var zero)) , [ reflexive ]unloc (π₁ (var zero))))

  t3 : ε ⊢ ⨅ (Base NN ＠ uu / type) (Com (uu ∧ vv) (Base NN ＠ vv)) / type
  t3 = lam (([ Base NN to[ (uu ∧ vv) ⨾ uu ⨾ (uu ∨ vv) ] (π₀-∧) ⨾ (ι₀-∨) ]► End) ∋ (var zero ► ret (loc ([ {!!} ]unloc (fromext (var zero) )))))



{-

{-

    -- T0 : [] ⊢ ⨅ (Free (Base BB)) Type
    -- T0 = lam (type (Inh (u ∧ atom (var zero)) ⇒ Base NN))

    T0 : [] ⊢Sheaf (Free (Base BB))
    T0 = Base NN ＠ gen uu

    -- T1 : [] ,[ Free (Base BB) ] ⊢Type
    -- T1 = Yo (gen u) (var zero) ⇒ Base NN

    t0 : [] ⊢ Ap T0 (gen (uu ∨ vv))
    t0 = loc λ a -> n0

    t1 : [] ⊢ Ap T0 (gen uu)
    t1 = rest T0 (gen ι₀-∨) t0

    t2 : [] ⊢ Ap ((Base NN ＠ gen uu) ⇒i ((Base NN ＠ gen uu) ⊗ (Base NN ＠ gen vv))) (gen (uu ∨ vv))
    t2 = {!!}

    -- T0 : [] ⊢Sheaf (Free (Base BB))
    -- T0 = (Base NN ＠ u) ⊗ (Base BB ＠ v)

    -- t0 : [] ⊢ Ap T0 u
    -- t0 = ap ((loc (λ x → n0)) , (loc (λ x → b0)))

    -- t1 : [] ⊢ Ap T0 v
    -- t1 = ap ((loc (λ x → n0)) , (loc (λ x → b0)))

    -- t2 : [] ⊢ Ap T0 (u ∨ v)
    -- t2 = ap (glueP {U = u} {V = v} (tm t0) ((tm t1)) {!!})

    -- t3 : [] ⊢ ⨅ₛ (Free (Base BB)) (Ap (Base NN ＠ (u ∧ v)) (atom (var zero)) ⇒ Ap (Base NN ＠ (u ∧ v)) ((atom (var zero))))
    -- t3 = lamₛ (lami (ap (tm (var zero))))



    -- t3 : [] ⊢ ⨅ Spc (⨅ (Sh (spc (var zero))) (Ap (shf (var zero)) ⊥))
    -- t3 = {!!}

    -- TN : [] ⊢Type
    -- TN = (Base NN over Free (Base BB)) ⊗ Base NN
    -- tn : [] ⊢ TN ＠ Free (Base BB)
    -- tn = loc u , loc (v ∧ u)




  {-
  data _⊢_/_ : ∀ Γ {X} {A} -> (t : Γ ⊢ A) -> (l : Γ ⊢ X ⨞ A) -> 𝒰₂ where

  -- also we can build a generic sheaf (it should be the same)
  -- on open sets:
  sheaf2 : Γ ⊢ X ⨞ A -> Sheaf (Γ ⊢Open' X) _
  sheaf2 {Γ = Γ} F = (λ U -> ∑ λ t -> Γ ⊢ t / F) since {!!}

  -- Now we can compute the etale space E of that sheaf,
  -- and the prime filters of E. They should be given by
  -- prime filters of (Γ ⊢Open X) together with matching terms.
  --
  -- I can interpret 







  --------------------------------------------------------------


  -- We have A over X and want to restrict to A over a smaller BY
  -- For that we need to give a map BY -> AX (or AX -> BY) which describes this
  -- restriction

  -- bind-Open : ⟨ Σ ⊢Open AX ⟩ -> 

  -- map-loc2 : Γ ⊢ A ＠ AX -> Σ ⊢Atom (BY ⇒i AX) -> Γ ⊢ A ＠ BY
  -- map-loc2 = {!!}

  -- map-loc : Γ ⊢ A ＠ X -> Γ ⊢Atom (X ⇒i Y) -> Γ ⊢ A ＠ X
  -- map-loc (L , M) f = map-loc L f , map-loc M f
  -- map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)

  -- su-Space : Γ ⊢ A -> Γ ⊢Open X -> Γ ,[ A over X ] ⊢Space -> Γ ⊢Space
  -- su-Space = {!!}

  wk-Space : Γ ⊢Space -> Γ ,[ X under A ] ⊢Space
  wk-Space = {!!}

  -- map-loc : Γ ⊢ A ＠ AX -> Σ ⊢Atom (AX ⇒i BY) -> Γ ⊢ A ＠ BY
  -- map-loc (L , M) f = map-loc L f , map-loc M f
  -- map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)


  _⊢Sheaf_ : ∀ Γ X -> _
  Γ ⊢Sheaf X = ∑ λ (A : Γ ⊢Type X) -> Γ ⊢ X ⨞ A

  pu-Type : (Γ ⊢Atom (X ⇒i Y)) -> Γ ⊢Sheaf X -> Γ ⊢Sheaf Y
  pu-Type f (.(_ under _ ⊗ _) , (F , F₁)) = {!? ⊗ ?!} , {!!}
  pu-Type f (A , loc x) = {!!}
  -- pu-Type f (Base x) = {!Base x!}
  -- pu-Type f (X under A ⊗ T) = {!? ⊗ ?!} -- _ under (pu-Type f A) ⊗ {!!}
  -- pu-Type f One = {!!}
  -- pu-Type f (Forget X g) = Forget X (compi g f)

  -- restr : Γ ⊢ X ⨞ A -> (f : Γ ⊢Atom (X ⇒i Y)) -> Γ ⊢ Y ⨞ pu-Type f A
  -- restr T f = {!!}

  -- restr (t , s) F = {!!}
  -- restr (loc U) F = loc (app-Open F U)

  {-

  -}

    -- T0 : [] ⊢Space
    -- T0 = Free (Base BB) [ Base BB ]⇒ Free (Base BB)
    -- t0 : [] ⊢Atom T0
    -- t0 = lami (free (app (elim-BB {A = Forget (Free (Base BB))} (forget (⦗ val b0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[]))) (forget (⊤))) (var zero)))


  {-

  ---------------------------------------------
  -- Space layer

  -- There is a notion of spatial extension of a type context
  data SCtx : Ctx -> 𝒰₀

  private variable
    Σ : SCtx Γ

  -- We have a notion of space over a space context
  data _⨾_⊢Space : ∀ Γ -> (Σ : SCtx Γ) -> 𝒰₀

  private variable
    AX : Γ ⊢Space
    BY : Γ ⊢Space

  -- We have a notion of term/open set of a space
  data _⊢Atom_ : ∀ Σ -> Γ ⊢Space -> 𝒰₀

  _⊢Open_ : ∀ Σ -> Γ ⊢Space -> Space
  _⨾_⊢Open_ : ∀ Γ Σ -> Γ ⊢Space -> Space

  instance
    hasStrictOrder:Atom : hasStrictOrder (Σ ⊢Atom X)
    hasStrictOrder:Atom = {!!}

  data SCtx where
    [] : SCtx []
    _,[_] : (Σ : SCtx Γ) -> Γ ⊢Space -> SCtx (Γ ,[ A ])

  data _⨾_⊢Space where
    One : Γ ⊢Space

    _⊗_ : (AX : Γ ⊢Space) -> (BY : Γ ,[ A ] ,[ AX ] ⊢Space) -> Γ ⊢Space
    _⇒_ : (AX : Γ ⊢Space) -> (BY : Γ ,[ A ] ,[ AX ] ⊢Space) -> Γ ⊢Space

    _⇒i_ : (AX BY : Γ ⊢Space) -> Γ ⊢Space

    Free : (A : Γ ⊢Type) -> Γ ⊢Space

    Sub : (AX : Γ ⊢Space) -> (U : List ((List (Σ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a)) -> Γ ⊢Space
    -- Sub : (AX : Γ ⊢Space) -> (U : List ((List (Σ ⊢Atom X) :& isUniqueSorted)) :& (isIndependent2Base λ a b -> ∑ λ x -> (x ∈ ⟨ a ⟩) ×-𝒰 (x ∉ ⟨ b ⟩) )) -> Γ ⊢Space
    -- Sub : (AX : Γ ⊢Space) -> (U : 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Σ ⊢Atom X) since hasStrictOrder:Atom))) -> Γ ⊢Space

  su-Atom-Space : Γ ⊢ A -> Σ ⊢Atom X -> Γ ,[ A ] ,[ AX ] ⊢Space -> Γ ⊢Space
  su-Atom-Space = {!!}

  data _⊢Atom_ where
    val : Γ ⊢ A -> Σ ⊢Atom Free A
    app : Σ ⊢Atom X ⇒ BY -> (a : Γ ⊢ A) -> (x : Σ ⊢Atom X) -> Σ ⊢Atom su-Atom-Space a x BY
    appi : Σ ⊢Atom (AX ⇒i BY) -> (x : Σ ⊢Atom X) -> Σ ⊢Atom BY

    liftfree : Γ ⊢ A ⇒ wk-Sort B -> Σ ⊢Atom (Free A ⇒i Free B)

    -- free : ⟨ Γ ,[ A ] ,[ Free A ] ⊢Open AX ⟩ -> Σ ,[ Free A ] ⊢Atom X


  Σ ⊢Open AX = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ ((Σ ⊢Atom X) since hasStrictOrder:Atom))


  su-Space : Γ ⊢ A -> ⟨ Σ ⊢Open AX ⟩ -> Γ ,[ A ] ,[ AX ] ⊢Space -> Γ ⊢Space
  su-Space t s One = {!!}
  su-Space t s (BY ⊗ BY₁) = {!!}
  su-Space t s (AX ⇒ BY) = {!!}
  su-Space t s (AX ⇒i BY) = {!!}
  su-Space t s (Free A) = {!!}
  su-Space t s (Sub BY U) = Sub ({!!}) {!!}

  -- data _⨾_⊢Open_ where

  -- _≤-SCtx_ : SCtx -> SCtx -> 

  ---------------------------------------------
  -- Location layer

  -- We have an assignment of locations in a space to a type
  data _⨾_⊢_＠_ : (Γ : Ctx) -> (Σ : SCtx Γ) -> Γ ⊢Type -> Γ ⊢Space -> 𝒰₂ where

    -- _,dep_ : (Γ ⊢ A ＠ AX) -> Γ ,[ A ] ,[ AX ] ⊢ B ＠ BY -> Γ ⊢ (A ⊗ B) ＠ (AX ⊗ BY)

    _,_ : (Γ ⊢ A ＠ AX) -> (Γ ⊢ B ＠ AX) -> Γ ⊢ (A ∥ B) ＠ AX

    loc : ∀{A} -> ⟨ Σ ⊢Open AX ⟩ -> Γ ⊢ (Base A) ＠ AX

  -- If we have a location assignment, we can restrict it along a ?


  -- We have A over X and want to restrict to A over a smaller BY
  -- For that we need to give a map BY -> AX (or AX -> BY) which describes this
  -- restriction

  -- bind-Open : ⟨ Σ ⊢Open AX ⟩ -> 

  map-loc2 : Γ ⊢ A ＠ AX -> Σ ⊢Atom (BY ⇒i AX) -> Γ ⊢ A ＠ BY
  map-loc2 = {!!}

  map-loc : Γ ⊢ A ＠ AX -> Σ ⊢Atom (AX ⇒i BY) -> Γ ⊢ A ＠ BY
  map-loc (L , M) f = map-loc L f , map-loc M f
  map-loc (loc x) f = loc (bind-Space (λ x -> ⦗ appi f x ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) x)



  -- restr : Γ ⊢ A ＠ AX -> ⟨ Σ ,[ AX ] ⊢Open BY ⟩ -> Γ ⊢ A ＠ su-Space {!!} {!!} BY
  -- restr = {!!}


  -- -- And a context "extension" which assigns locations 
  -- data LCtx : (Γ : Ctx) -> Γ ⊢Space -> 𝒰₂



  module Example where
    T0 : [] ⊢Type
    T0 = Base NN ∥ Base NN

    T1 : [] ⨾ [] ⊢ T0 ＠ Free (Base BB)
    T1 = loc (⦗ val b0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])) , loc (⦗ val b1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[]))



  ---------------------------------------------
  -- types

  -- private variable
  --   U V : ⟨ L ⟩





  {-


  -- KindedPartialType : (Γ : Ctx) -> {U V : UniqueSortedList R} -> .(ψ : U ≤ V) -> 𝒰₁
  -- KindedPartialType Γ ψ = Γ ⇂ Partial ψ ⊢Type


  -- syntax KindedPartialType Γ ψ = Γ ⇂ ψ ⊢Partial

  KindedLocalType : (Γ : Ctx) -> (U : ⟨ L ⟩) -> 𝒰₂
  KindedLocalType Γ U = Γ ⊢ Local U Type

  syntax KindedLocalType Γ U = Γ ⊢Local U

  KindedGlobalType : (Γ : Ctx) -> 𝒰₂
  KindedGlobalType Γ = Γ ⊢ Global Type

  syntax KindedGlobalType Γ = Γ ⊢Global



  -- KindedCommType : ∀ R -> (Γ : Ctx) -> 𝒰₁
  -- KindedCommType R Γ = Γ ⊢Comm 

  -- syntax KindedCommType L Γ = Γ ⊢Comm L Type



  private variable
    AX : Γ ⊢Sort k
    BY : Γ ⊢Sort k

  data _⊢Var_ : ∀ (Γ : Ctx) -> (A : Γ ⊢Sort k) -> 𝒰₂
  data _⊢_ : ∀ (Γ : Ctx) -> (A : Γ ⊢Sort k) -> 𝒰₂



























  infixl 40 _,[_]

  -- _[_]-Type : Δ ⊢Sort k -> Γ ⇛♮ Δ -> Γ ⇂ {!!} ⊢Type

  -- ♮-⇛ : Γ ⇛ Δ -> Γ ⇛♮ Δ
  -- ♮-⇛ = {!!}

  -- data _⇛_ where
  --   id : ∀{Γ : Ctx} -> Γ ⇛ Γ
  --   π₁ : ∀{Γ Δ : Ctx} -> ∀{A} -> Γ ⇛ (Δ ,[ A ]) -> Γ ⇛ Δ
  --   _,_ : ∀{Γ Δ : Ctx} -> (δ : Γ ⇛ Δ) -> ∀{A} -> Γ ⊢ (A [ ♮-⇛ δ ]-Type) -> Γ ⇛ Δ ,[ A ]
  --   _◆-⇛_ : ∀{Γ Δ Ε : Ctx} -> Γ ⇛ Δ -> Δ ⇛ Ε -> Γ ⇛ Ε
  --   ε : Γ ⇛ []

  -- data _⇛♮_ where
  --   ε : Γ ⇛♮ []
  --   _,_ : ∀{A} -> (σ : Γ ⇛♮ Δ) -> Γ ⊢ (A [ σ ]-Type) -> Γ ⇛♮ Δ ,[ A ]











  -- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
  -- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

  -- ⟨_⊢⇂_⇃⟩ : ∀ (Γ : Ctx) -> {A B : Γ ⊢Type} -> (A ≣ B) -> Γ ⊢ A -> Γ ⊢ B
  -- ⟨_⊢⇂_⇃⟩ Γ {A} {B} p x = transp-≣ (cong-≣ (Γ ⊢_) p) x

  -- _∥⊢Type↷_ : Γ ≣ Δ -> Γ ⊢Type -> Δ ⊢Type
  -- _∥⊢Type↷_ p A = transp-≣ (cong-≣ (_⊢Type) p) A


  ------------------------------------------------------------------------
  -- Filtering (Definition)

  {-
  _⇂_ : Ctx -> UniqueSortedList R -> Ctxartial
  _⇂-Type_ : Γ ⊢ R Type -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢ Partial Type

  [] ⇂ U = []
  Γ ,[ A ] ⇂ U = Γ ⇂ ψ ,[ A ⇂-Type U ]

  _⇂-Ctx₊_ : {Γ : Ctx} -> Γ ⊢Ctx₊ -> (U : UniqueSortedList R) -> Γ ⇂ ψ ⊢Ctx₊
  filter-Type,Ctx₊ : {Γ : Ctx} -> (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E ⊢Type) -> (U : UniqueSortedList R) -> (Γ ⇂ ψ) ⋆-Ctx₊ (E ⇂-Ctx₊ U) ⊢Type

  [] ⇂-Ctx₊ U = []
  E ,[ x ] ⇂-Ctx₊ U = E ⇂-Ctx₊ U ,[ filter-Type,Ctx₊ E x U ]

  σ-⋆,⇂,Ctx : ∀ E U -> ((Γ ⋆-Ctx₊ E) ⇂ U) ≣ (Γ ⇂ ψ ⋆-Ctx₊ E ⇂-Ctx₊ U)
  filter-Type,Ctx₊ {Γ = Γ} E A U = σ-⋆,⇂,Ctx E U ∥⊢Type↷ (A ⇂-Type U)

  σ-⋆,⇂,Ctx [] U = refl-≣
  σ-⋆,⇂,Ctx (E ,[ x ]) U = sym-≣ $ J1 (σ-⋆,⇂,Ctx E U) _⊢Type _,[_] (x ⇂-Type U)

  {-# REWRITE σ-⋆,⇂,Ctx #-} -- we need this for `wk-Sort,ind` and for `σ-wk-⇂-Ctx₊`

  -- we also need to reduce `σ-⋆,⇂,Ctx` to refl:
  isRefl:σ-⋆,⇂,Ctx : ∀ {E : Γ ⊢Ctx₊} {U} -> σ-⋆,⇂,Ctx E U ≣ refl-≣
  isRefl:σ-⋆,⇂,Ctx = K1 _

  {-# REWRITE isRefl:σ-⋆,⇂,Ctx #-}


  infixl 40 _⇂_ _⇂-Type_ _⇂-Ctx₊_

  _⇂-Partial_ : {U V : UniqueSortedList R} -> Γ ⇂ V ⊢ Partial Type -> (U ≤ V) -> Γ ⇂ ψ ⊢ Partial Type
  _⇂-Partial_ = {!!}

  filter-Partial : (U V : UniqueSortedList R) -> Γ ⇂ V ⊢ Partial Type -> Γ ⇂ ψ ⊢ Partial Type
  filter-Partial U V A = {!!}
    -- we have to check that U ≤ V, if that is the case,
    -- we can restrict all things in the context properly. If that is not the case,
    -- we can return 𝟙 because this means that our current type is not filterable
    -- to U

  -}
  -- End Filtering (Definition)
  ------------------------------------------------------------------------

  -- Flat : Γ ⊢Comm -> Γ ⊢Global

  -- Restrict-Local : (ϕ : U ≤ V) -> Γ ⇂ V ⊢Local -> Γ ⊢Local U
  -- local : {U V : 𝒫ᶠⁱⁿ R} .{ϕ : U ≤ V} -> Γ ⇂ ϕ ⊢Partial -> Γ ⇂ V ⊢Local

  data BaseType : 𝒰₀ where
    NN End : BaseType
    AA : BaseType

  -- data _⇂_⊢_≤-Local_ : ∀ Γ -> .(V ≤ U) -> (Γ ⊢Local U) -> (Γ ⇂ V ⊢Local) -> 𝒰₁
  -- data _⇂_⊢_≤-Term_ : ∀ (Γ : Ctx) -> .{ϕ : V ≤ U} -> {A : Γ ⊢Local U} {B : Γ ⇂ V ⊢Local} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ A -> (Γ ⊢ B) -> 𝒰₁

  data _⊢_⇂_↦_ : ∀ (Γ : Ctx) -> (AX : Γ ⊢Global) -> (U : ⟨ L ⟩) -> (A : Γ ⊢Local U) -> 𝒰₂ where

  data _⊢domain_↦_ : ∀ (Γ : Ctx) -> (AX : Γ ⊢Global) -> (U : ⟨ L ⟩) -> 𝒰₂ where

  data _⊢_≡_Type : ∀(Γ : Ctx) -> (AX BY : Γ ⊢Sort k) -> 𝒰₂ where
  data _⊢_≡_/_ : ∀(Γ : Ctx) -> {AX BY : Γ ⊢Sort k} (x : Γ ⊢ AX) (y : Γ ⊢ BY) -> (Γ ⊢ AX ≡ BY Type) -> 𝒰₂ where

  data _⊢_Type where

    Base : BaseType -> Γ ⊢ Local U Type

    -- A local type can be embedded as global type
    Loc : ∀ U -> Γ ⊢ Local U Type -> Γ ⊢ Global Type

    -- A global type can be restricted to an open set
    _⇂_ : {Γ : Ctx} -> Γ ⊢ Global Type -> (U : ⟨ L ⟩) -> Γ ⊢Local U


    _⊗_ : (AX BY : Γ ⊢Sort k) -> Γ ⊢Sort k
    -- _⊗_ : (AX BY : Γ ⊢Global) -> Γ ⊢Global
    -- _⊠_ : (AX : Γ ⊢Local U) (BY : Γ ⊢Local V) -> Γ ⊢Local (U ∨ V)
    _⇒_ : (AX : Γ ⊢Global) -> (BY : Γ ,[ AX ] ⊢Global) -> Γ ⊢Global

    _⇒ₗ_ : (AX : Γ ⊢Local U) -> (BY : Γ ,[ Loc U AX ] ⊢Local U) -> Γ ⊢Local U



  infixr 50 _⊗_
  infixr 40 _⇒_ _⇒ₗ_
  infixl 35 _⇂_

  {-
    located : (U : 𝒫ᶠⁱⁿ R) -> (A : Γ ⊢Local U) -> Γ ⊢Global --V ≤ ?)

    Base : BaseType -> Γ ⊢Local U

    _⇒_ : (A : Γ ⊢Sort k) -> (B : Γ ,[ A ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : (A : Γ ⊢Sort k) -> (B : Γ ,[ A ] ⊢Sort k) -> Γ ⊢Sort k

    Unit : Γ ⊢Sort k

    Val : {U V : 𝒫ᶠⁱⁿ R} .(ϕ : U ≤ V) -> {A : Γ ⇂ V ⊢Local} -> {B : Γ ⊢Local U} -> (Γ ⇂ ϕ ⊢ A ≤-Local B) -> Γ ⊢ located U B -> Γ ⇂ ϕ ⊢Partial -- next step: Use relation here instead of restrict-local function

    Fill : .(ϕ : U ≤ V) -> Γ ⇂ ϕ ⊢Partial -> Γ ⊢Global

    Fam : ∀ (U : 𝒫ᶠⁱⁿ R) -> Γ ⊢ (located U (Base NN)) -> Γ ⊢Local U

    U-Comm : Γ ⊢Global

    Comm : (Y : Γ ⊢Comm ) -> Γ ,[ Flat Y ] ⊢Global -> Γ ⊢Global


    -------------------
    -- Normalizable:

    -- [_]⇂_ : 


  data _⇂_⊢_≤-Term_ where

  data _⇂_⊢_≤-Local_ where
    Base : ∀ b -> .{ϕ : U ≤ V} -> Γ ⇂ ϕ ⊢ Base b ≤-Local Base b
    Fam : ∀ {U V : 𝒫ᶠⁱⁿ R} -> .(ϕ : V ≤ U)
        -> (m : Γ ⊢ (located U (Base NN))) -> (n : Γ ⊢ (located V (Base NN)))
        -- -> (Γ ⇂ ? ⊢ m ≤-Term n)
        -> Γ ⇂ ϕ ⊢ Fam U m ≤-Local Fam V n
    -- Γ ⊢ (located U (Base NN)) -> Γ ⊢Local U

  -}


  syntax Loc A Y = Y ＠ A


  {-
  Restrict-Local ϕ (Base x) = Base x
  Restrict-Local ϕ (A ⇒ A₁) = {!!}
  Restrict-Local ϕ (A ⊗ A₁) = {!!}
  Restrict-Local ϕ Unit = {!!}
  Restrict-Local ϕ (Fam _ x) = {!!}

  local (A ⇒ A₁) = {!!}
  local Unit = {!!}
  local (Val ϕ {A = A} Φ x) = A



  data _⊢Comm where
    ⟮_↝_⨾_⟯[_]_ : (U V : 𝒫ᶠⁱⁿ R) -> {W : 𝒫ᶠⁱⁿ R} -> .(ϕ : W ≤ U) -> (A : Γ ⇂ (ϕ ⟡ ι₀-∨ {b = V}) ⊢Partial) -> Γ ,[ Fill (ϕ ⟡ ι₀-∨ {b = V}) A ] ⊢Comm -> Γ ⊢Comm 
    -- ⩒⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ (reflexive / ⦗ a ⦘ ≤ ⦗ a ⦘) ⊢ R Type) -> Γ ,[ A ] ⊢Comm -> Γ ⊢Comm 
    -- ⩑⟮_⟯[_]_ : (a : ⟨ R ⟩) -> (A : Γ ⇂ (reflexive / ⦗ a ⦘ ≤ ⦗ a ⦘) ⊢ R Type) -> Γ ,[ A ] ⊢Comm -> Γ ⊢Comm 
    End : Γ ⊢Comm

    El-Comm : Γ ⊢ U-Comm -> Γ ⊢Comm



  -}











  data _⊢Var_ where
    zero : Γ ,[ A ] ⊢Var (wk-Sort A)
    suc : Γ ⊢Var A -> Γ ,[ B ] ⊢Var (wk-Sort A)

  -- data _⊢Var : Ctx -> 𝒰₀ where
  --   zero : Γ ,[ A ] ⊢Var
  --   suc : Γ ⊢Var -> Γ ,[ A ] ⊢Var

  -- KindedLocalTerm : ∀ (Γ : Ctx) -> ∀ U -> (A : Γ ⊢Local U) -> 𝒰 _
  -- KindedLocalTerm Γ U A = Γ ⊢ A

  -- syntax KindedLocalTerm Γ U A = Γ ⇂ U ⊢ A


  data _⊢_ where

    -- we have variables
    var : Γ ⊢Var A -> Γ ⊢ A

    -- we can take a global computation and use it in a more local context
    global : {U : ⟨ L ⟩} -> {AX : Γ ⊢Global} -> Γ ⊢ AX -> Γ ⊢ AX ⇂ U

    -- we can construct Loc terms
    loc : (U : ⟨ L ⟩) -> (BY : Γ ⊢ Local U Type) -> Γ ⊢ BY -> Γ ⊢ Loc U BY
    local : {Γ : Ctx} (U : ⟨ L ⟩) -> (AX : Γ ⊢Global) -> Γ ⊢domain AX ↦ U -> (BY : Γ ⊢Local U)
            -> Γ ⊢ AX ⇂ U -> Γ ⊢ AX

    glue : {Γ : Ctx} -> {AX : Γ ⊢Global} -> (U V : ⟨ L ⟩)
            -> Γ ⊢ AX ⇂ U -> Γ ⊢ AX ⇂ V
            -> Γ ⊢ AX ⇂ (U ∨ V)

    ev-⊗ : Γ ⊢ (AX ⊗ BY) ⇂ U -> Γ ⊢ (AX ⇂ U) ⊗ (BY ⇂ U)
    ve-⊗ : ∀{Γ : Ctx} -> {AX BY : Γ ⊢Global} -> {U : ⟨ L ⟩}
          -> Γ ⊢ (AX ⇂ U) ⊗ (BY ⇂ U) -> Γ ⊢ (AX ⊗ BY) ⇂ U

    ev-⇒ : Γ ⊢ (AX ⇒ BY) ⇂ U -> Γ ⊢ (AX ⇂ U) ⇒ₗ (special-su-top {!!} BY ⇂ U)

    -- functions
    lam : Γ ,[ A ] ⊢ B -> Γ ⊢ A ⇒ B
    app : Γ ⊢ A ⇒ B -> (t : Γ ⊢ A) -> Γ ⊢ su-Sort t B



  module Examples where
    open import KamiD.Dev.2024-01-20.Open
    open import KamiD.Dev.2024-01-20.StrictOrder.Base

    AXXA : hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁} (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))
    AXXA = it

    LL : _ :& hasFiniteJoins {𝑖 = ℓ₁ , ℓ₁ , ℓ₁}
    LL = (𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)))

    ε : CtxL
    ε = []

    u v uv : 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))
    u = ⦗ # 0 ⦘ ∷ [] since ([] ∷ [])
    v = ⦗ # 1 ⦘ ∷ [] since ([] ∷ [])
    uv = u ∨ v
    -- uv = ⦗ # 0 ⦘ ∷ ⦗ # 1 ⦘ ∷ []

    Ni : ∀{Γ : CtxL} -> 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2)) -> Γ ⊢ Global Type
    Ni w = Loc (w) (Base NN)

    T1 : ∀{Γ : CtxL} -> Γ ⊢ Global Type
    T1 = Loc u (Base NN) ⊗ Loc v (Base NN)

    T2 : ∀{Γ : CtxL} -> Γ ⊢ Global Type
    T2 = Ni u ⇒ wk-Sort T1

    t2 : ε ,[ T2 ] ⊢ Ni u ⇒ Ni u ⇒ Ni v
    t2 = lam (lam (local uv (Ni v) {!!} {!!} (glue u v (global {!!}) {!!})))

  {-
  -}
    -- lam (local uv (wk-Sort T1) {!!} (Base NN ⊗ₗ Base NN) {!!} {!!})


  -}
  -}


  -}
  -}
  -}
