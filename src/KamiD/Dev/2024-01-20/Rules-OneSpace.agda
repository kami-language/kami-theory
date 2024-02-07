
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
    U₀ U₁ : ⟨ P ⟩
    W₀ W₁ : ⟨ P ⟩
    R : ⟨ P ⟩

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


  data _⊢Mod_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀ where
    type : Γ ⊢Mod type
    local : (U : ⟨ P ⟩) -> Γ ⊢Mod local -- U tells us at which location this value is located
    com : (R : ⟨ P ⟩) -> (A : Γ ⊢Type) -> Γ ⊢Mod (com R) -- A tells us the result type of the communication, R the "root"-location of the protocol


  private variable
    m : Γ ⊢Mod k
    n : Γ ⊢Mod l

  record _⊢Entry_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
    inductive ; eta-equality
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


  data _⊢Var_ : ∀ Γ -> Γ ⊢Entry k -> 𝒰₀
  data _∣_⊢_ : ∀ (W : ⟨ P ⟩) -> ∀ Γ -> Γ ⊢Entry k -> 𝒰₀

  private variable
    t : W ∣ Γ ⊢ E
    s : W ∣ Γ ⊢ F



  --------------------------------------------------------------
  -- Context extensions

  data _⊢Ctx₊ : Ctx -> 𝒰₂

  _⋆-Ctx₊_ : ∀ (Γ : Ctx) -> Γ ⊢Ctx₊ -> Ctx

  data _⊢Ctx₊ where
    [] : Γ ⊢Ctx₊
    _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Entry k -> Γ ⊢Ctx₊


  Γ ⋆-Ctx₊ [] = Γ
  Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]




  infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_


  -- End Context setup
  --------------------------------------------------------------


  wk-Sort : Γ ⊢Sort k -> Γ ,[ E ] ⊢Sort k
  su-Sort : (t : W ∣ Γ ⊢ E) -> Γ ,[ E ] ⊢Sort k -> Γ ⊢Sort k

  wk-Entry : Γ ⊢Entry k -> Γ ,[ E ] ⊢Entry k
  su-Entry : (t : W ∣ Γ ⊢ E) -> Γ ,[ E ] ⊢Entry k -> Γ ⊢Entry k

  wk-Term : W ∣ Γ ⊢ E -> W ∣ Γ ,[ F ] ⊢ wk-Entry E

  wk-Mod : Γ ⊢Mod k -> Γ ,[ E ] ⊢Mod k

  special-su-top : W ∣ Γ ,[ E ] ⊢ wk-Entry F ->  Γ ,[ F ] ⊢Sort k -> Γ ,[ E ] ⊢Sort k
  special-su-top t T = {!!} -- su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)






  data _⊢Sort_ where

    --------------------------------------------------------------
    -- Generic
    ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    ⨅ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : (A B : Γ ⊢Sort k) -> Γ ⊢Sort k

    --------------------------------------------------------------
    -- Local

    Base : BaseType -> Γ ⊢Local

    _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Type

    -- NOTE, only well "modalized" if W is the current global
    -- modality
    Ext : W ∣ Γ ⊢ L ＠ V / type -> (ϕ : U ≤ V) -> Γ ⊢Type


    --------------------------------------------------------------
    -- Types
    Com : ⟨ P ⟩ -> Γ ⊢Type -> Γ ⊢Type

    --------------------------------------------------------------
    -- Com
    End : Γ ⊢Com U

    -- A single communication of a protocol with R participants.
    -- We are sending local data from location U₀ to be accessible
    -- at location U₁
    [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / type ] ⊢Com R) -> Γ ⊢Com R



  -- infixr 40 _⇒_
  infixr 50 _⊗_

  -- syntax Loc U L = L ＠ U
  infixl 90 _＠_


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

  wk-Mod,ind Δ (type) = type
  wk-Mod,ind Δ (local U) = local U
  wk-Mod,ind Δ (com R A) = com R (wk-Sort,ind Δ A)


  -- wk-Var-ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Sort k} -> Γ ⋆-Ctx₊ Δ ⊢Var AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Var wk-Sort,ind Δ AX

  wk-Term,ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Entry k} -> W ∣ Γ ⋆-Ctx₊ Δ ⊢ AX -> W ∣ Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢ wk-Entry,ind Δ AX
  wk-Term,ind = {!!}


  wk-Ctx₊ [] = []
  wk-Ctx₊ (Δ ,[ E ]) = wk-Ctx₊ Δ ,[ wk-Entry,ind Δ E ]


  wk-Sort,ind Δ (Base x) = Base x
  wk-Sort,ind Δ (⨆ A B) = {!!}
  wk-Sort,ind Δ (⨅ S B) = ⨅ (wk-Entry,ind Δ S) (wk-Sort,ind (Δ ,[ S ]) B)
  wk-Sort,ind Δ (x ＠ U) = (wk-Sort,ind Δ x) ＠ U
  wk-Sort,ind Δ (Ext x ϕ) = Ext (wk-Term,ind Δ x) ϕ -- ϕ (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (A ⊗ B) = wk-Sort,ind Δ A ⊗ wk-Sort,ind Δ B
  wk-Sort,ind Δ (Com x x₁) = {!!}
  wk-Sort,ind Δ End = End
  wk-Sort,ind Δ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► x) = {!!}

  wk-Sort S = wk-Sort,ind [] S
  wk-Mod (m) = wk-Mod,ind [] m
  wk-Entry m = wk-Entry,ind [] m
  wk-Term t = wk-Term,ind [] t




  -- End weakening
  ------------------------------------------------------------------------


  data _∣_⊢_ where

    ---------------------------------------------
    -- Terms
    var : Γ ⊢Var E -> W ∣ Γ ⊢ E

    b0 : W ∣ Γ ⊢ Base BB / local U
    b1 : W ∣ Γ ⊢ Base BB / local U
    n0 : W ∣ Γ ⊢ Base NN / local U

    -- We only have to implement this term if our current location `U`
    -- Is part of the implemented locations `W`
    loc : (W ∣ Γ ⊢ L / local U) -> W ∣ Γ ⊢ (L ＠ U) / type

    -- loc : (Γ ⊢ L / local U) -> Γ ⊢ (L ＠ U) / type

    -- Given a value of type L at location U, we can make it into a local
    -- value of type L at location V, as long as V is a location which can access U
    -- (ie, is a superset).
    [_]unloc : (ϕ : U ≤ V) -> W ∣ Γ ⊢ (L ＠ U) / type -> W ∣ Γ ⊢ L / local V




    fromext : {ϕ : V ≤ U} -> {val : W ∣ Γ ⊢ L ＠ U / type} -> W ∣ Γ ⊢ Ext val ϕ / type -> W ∣ Γ ⊢ L ＠ V / type


    lam : W ∣ Γ ,[ E ] ⊢ S / wk-Mod m  -> W ∣ Γ ⊢ ⨅ E S / m
    app : W ∣ Γ ⊢ ⨅ (T / m) S / n -> (t : W ∣ Γ ⊢ T / m) -> W ∣ Γ ⊢ su-Sort t S / n


    π₁ : W ∣ Γ ⊢ (T ⊗ S) / m -> W ∣ Γ ⊢ T / m
    π₂ : W ∣ Γ ⊢ (T ⊗ S) / m -> W ∣ Γ ⊢ S / m
    _,_ : W ∣ Γ ⊢ T / m -> W ∣ Γ ⊢ S / m -> W ∣ Γ ⊢ (T ⊗ S) / m


    -------------------
    -- protocols
    _∋_ : (P : Γ ⊢Com R) -> W ∣ Γ ⊢ P / com R A -> W ∣ Γ ⊢ Com R A / type

    _►_ : {ϕ : R ≤ U₁} -> {ψ : U₁ ≤ U₀}
        -> ∀ {C}
        -> (val : W ∣ Γ ⊢ L ＠ U₀ / type)
        -> W ∣ Γ ,[ Ext val ψ / type ] ⊢ special-su-top (fromext (var zero) ) C / com R (wk-Sort A)
        -> W ∣ Γ ⊢ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) / com R A

    ret : W ∣ Γ ⊢ A / type -> W ∣ Γ ⊢ End / com R A


  data _∣_⊢WFMod_ : ∀(W : ⟨ P ⟩) -> ∀ Γ -> Γ ⊢Mod k -> 𝒰₀
  data _∣_⊢WFSort_ : ∀(W : ⟨ P ⟩) -> ∀ Γ -> Γ ⊢Entry k -> 𝒰₀

  record _∣_⊢WFEntry_ (W : ⟨ P ⟩) (Γ : Ctx) (E : Γ ⊢Entry k) : 𝒰₀ where
    inductive ; eta-equality
    constructor _/_
    field fst : W ∣ Γ ⊢WFSort E
    field snd : W ∣ Γ ⊢WFMod (snd E)

  data _∣_⊢WFSort_ where
    -- tt : W ∣ Γ ⊢WFSort S / m

    --------------------------------------------------------------
    -- Generic
    -- ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k

    ⨅ₜ : W ∣ Γ ⊢WFEntry E -> W ∣ Γ ,[ E ] ⊢WFSort T / type -> W ∣ Γ ⊢WFSort (⨅ E T) / type
    ⨅ₗ : W ∣ Γ ⊢WFEntry E -> W ∣ Γ ,[ E ] ⊢WFSort T / local U -> W ∣ Γ ⊢WFSort (⨅ E T) / local U

    -- (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : W ∣ Γ ⊢WFSort S / m -> W ∣ Γ ⊢WFSort T / m -> W ∣ Γ ⊢WFSort (S ⊗ T) / m

    --------------------------------------------------------------
    -- Local

    Base : ∀{B} -> W ∣ Γ ⊢WFSort (Base B) / m

    Loc : W ∣ Γ ⊢WFSort L / local U -> W ∣ Γ ⊢WFSort (L ＠ U) / type


    -- NOTE, only well "modalized" if W is the current global
    -- modality
    -- Ext : W ∣ Γ ⊢ Loc V L / type -> (ϕ : U ≤ V) -> Γ ⊢Type


    -- --------------------------------------------------------------
    -- -- Types
    -- Com : ⟨ P ⟩ -> Γ ⊢Type -> Γ ⊢Type

    -- --------------------------------------------------------------
    -- -- Com
    -- End : Γ ⊢Com U

    -- -- A single communication of a protocol with R participants.
    -- -- We are sending local data from location U₀ to be accessible
    -- -- at location U₁
    -- [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / type ] ⊢Com R) -> Γ ⊢Com R



  data _∣_⊢WFMod_ where
    type : W ∣ Γ ⊢WFMod type
    local : W ∣ Γ ⊢WFMod local U
    com : W ∣ Γ ⊢WFSort (A / type) -> W ∣ Γ ⊢WFMod com R A


  data _∣_⊢WFCtx : ⟨ P ⟩ -> ∀ (Γ : Ctx) -> 𝒰₀ where
    [] : W ∣ [] ⊢WFCtx
    _,[_] : W ∣ Γ ⊢WFCtx -> W ∣ Γ ⊢WFEntry E -> W ∣ Γ ,[ E ] ⊢WFCtx



  ----------------------------------------------------------
  -- Meta theorems

  -- We can restrict terms to smaller locations (W)
  --

  -- _∣_⊢WFEntry_ : ⟨ P ⟩ -> ∀ (Γ : Ctx) -> Kind -> 𝒰₀
  -- _∣_⊢WFEntry_ W Γ k = ∑ λ (E : Γ ⊢Entry k) -> W ∣ Γ ⊢WFSort E

  -- restrict-Sort : W₀ ≤ W₁ -> Γ ⊢Sort k -> Γ ⊢Sort k
  -- restrict-Sort ϕ S = {!!}

  restrict-Ctx : W₀ ≤ W₁ -> ∀ Γ -> W₁ ∣ Γ ⊢WFCtx -> Ctx
  restrict-Sort : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> (S : Γ ⊢Sort k) -> (m : Γ ⊢Mod k) -> W₁ ∣ Γ ⊢WFSort (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Sort k
  restrict-Mod : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx ) -> (m : Γ ⊢Mod k) -> W₁ ∣ Γ ⊢WFMod m -> restrict-Ctx ϕ Γ ΓP ⊢Mod k

  restrict-Entry : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> W₁ ∣ Γ ⊢WFEntry (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Entry k
  restrict-Entry = {!!}

  restrict-Mod ϕ ΓP .type type = type
  restrict-Mod ϕ ΓP (local U) local = local U
  restrict-Mod ϕ ΓP (com R A) (com Ap) = com R (restrict-Sort ϕ ΓP A type Ap)



  restrict-Ctx ϕ [] P = []
  restrict-Ctx ϕ (Γ ,[ S / m ]) (ΓP ,[ SP / mP ]) = restrict-Ctx ϕ Γ ΓP ,[ restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP  ]


  restrict-Sort ϕ ΓP (⨆ E S) m P = {!!}
  restrict-Sort ϕ ΓP (⨅ (S / m) T) .type (⨅ₜ (SP / mP) TP) = ⨅ (restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP) (restrict-Sort ϕ (ΓP ,[ SP / mP ]) T type TP)
  restrict-Sort ϕ ΓP (⨅ (S / m) T) .(local _) (⨅ₗ (SP / mP) TP) = {!!} -- ⨅ (restrict-Sort ϕ ΓP S m {!!} / m) {!!}
  restrict-Sort ϕ ΓP (S ⊗ T) m (SP ⊗ TP) = restrict-Sort ϕ ΓP S m SP ⊗ restrict-Sort ϕ ΓP T m TP
  restrict-Sort ϕ ΓP (Base x) m Base = Base x
  restrict-Sort ϕ ΓP (L ＠ U) m (Loc P) = restrict-Sort ϕ ΓP L (local U) P ＠ U
  restrict-Sort ϕ ΓP (Ext x ϕ₁) m P = {!!}
  restrict-Sort ϕ ΓP (Com x x₁) m P = {!!}
  restrict-Sort ϕ ΓP End m P = {!!}
  restrict-Sort ϕ ΓP ([ L from U₀ to U₁ [ ϕ₁ ⨾ ψ ]on W ]► C) m P = {!!}


  restrict-Term : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> (SP : W₁ ∣ Γ ⊢WFSort (S / m)) -> (mP : W₁ ∣ Γ ⊢WFMod m)
                  -> W₁ ∣ Γ ⊢ S / m
                  -> W₀ ∣ restrict-Ctx ϕ Γ ΓP ⊢ restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP
  restrict-Term ϕ ΓP SP mP (var x) = {!!}
  restrict-Term ϕ ΓP SP mP b0 = {!!}
  restrict-Term ϕ ΓP SP mP b1 = {!!}
  restrict-Term ϕ ΓP SP mP n0 = {!!}
  restrict-Term ϕ ΓP (Loc SP) type (loc t) = loc (restrict-Term ϕ ΓP SP (local) t)
  restrict-Term ϕ ΓP SP mP ([ ϕ₁ ]unloc t) = {!!}
  restrict-Term ϕ ΓP SP mP (fromext t) = {!!}
  restrict-Term ϕ ΓP SP mP (lam t) = {!!}
  restrict-Term ϕ ΓP SP mP (app t s) = {!app ? ?!}
  restrict-Term ϕ ΓP SP mP (π₁ t) = {!!}
  restrict-Term ϕ ΓP SP mP (π₂ t) = {!!}
  restrict-Term ϕ ΓP SP mP (t , t₁) = {!!}

  -- restrict-Term : (ϕ : W₀ ≤ W₁) -> W₁ ∣ Γ ⊢ E -> W₀ ∣ Γ ⊢ restrict-Entry ϕ E
  -- restrict-Term = {!!}

{-
  restrict : W₀ ≤ W₁ -> W₁ ∣ Γ ⊢ T / m -> W₀ ∣ Γ ⊢ T / m
  restrict ϕ (var x) = var x
  restrict ϕ (loc x) = loc λ ψ -> restrict ϕ (x (ψ ⟡ ϕ))
  restrict ϕ (fromext {val = val} t) = fromext {val = restrict ϕ val} {!!}
  restrict ϕ (lam t) = lam (restrict ϕ t)
  restrict ϕ (app {m = m} {n = n} t s) = let z = app (restrict ϕ t) (restrict ϕ s) in {!!}
  restrict ϕ (π₁ t) = {!!}
  restrict ϕ (π₂ t) = {!!}
  restrict ϕ (t , t₁) = {!!}
  restrict ϕ (P ∋ t) = {!!}
  restrict ϕ b0 = {!!}
  restrict ϕ b1 = {!!}
  restrict ϕ n0 = {!!}
  restrict ϕ ([ ϕ₁ ]unloc X) = {!!}
  restrict ϕ (X ► X₁) = {!!}
  restrict ϕ (ret X) = {!!}
  -}



module Examples where

  PP : Space
  PP = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))

  uu vv : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  vv = ⦗ # 1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  all = uu ∨ vv

  ε : Ctx {PP}
  ε = []

  T0 : ∀{Γ : Ctx {PP}} -> Γ ⊢Type
  T0 = (Base NN ＠ uu) ⊗ (Base NN ＠ vv)

  t1 : all ∣ ε ⊢ ⨅ (T0 / type) (Base NN ＠ uu) / type
  t1 = lam (π₁ (var zero))

  -- t2 : all ∣ ε ⊢ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / type) → ((Base NN ⊗ Base NN) ＠ uu) / type

  t2 : all ∣ ε ⊢ ⨅ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / type) ((Base NN ⊗ Base NN) ＠ uu) / type
  t2 = lam (loc ((let x = π₂ (var zero) in [ {!!} ]unloc x) , {!!}))
  -- lam (loc ([ reflexive ]unloc (π₁ (var zero)) , [ reflexive ]unloc (π₁ (var zero))))

  f : (uu ∧ vv) ≤ vv
  f = π₁-∧

  t3 : all ∣ ε ⊢ ⨅ (Base NN ＠ uu / type) (Com (uu ∧ vv) (Base NN ＠ vv)) / type
  t3 = {!!} -- lam (([ Base NN from uu to (uu ∧ vv) [ reflexive ⨾ π₀-∧ ]on all ]► End) ∋ (var zero ► ret (loc λ _ -> [ f ]unloc (fromext (var zero)))))






