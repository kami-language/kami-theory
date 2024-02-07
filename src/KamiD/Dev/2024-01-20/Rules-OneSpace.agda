
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
    global : Kind
    local : Kind
    com : ⟨ P ⟩ -> Kind

  private variable
    k l : Kind


  data _⊢Sort_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀

  private variable
    S : Γ ⊢Sort k
    T : Γ ⊢Sort l


  GlobalSyntax : ∀ (Γ : Ctx) -> 𝒰 _
  GlobalSyntax Γ = Γ ⊢Sort global

  syntax GlobalSyntax Γ = Γ ⊢Global

  private variable
    A : Γ ⊢Global
    B : Γ ⊢Global

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

  data DepMod : Kind -> 𝒰₀ where
    global : DepMod global
    local : (U : ⟨ P ⟩) -> DepMod local

  private variable
    d : DepMod k

  data _⊢Mod_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀ where
    Dep : DepMod k -> Γ ⊢Mod k
    -- type : Γ ⊢Mod type
    -- local : (U : ⟨ P ⟩) -> Γ ⊢Mod local -- U tells us at which location this value is located
    Com : (R : ⟨ P ⟩) -> (A : Γ ⊢Global) -> Γ ⊢Mod (com R) -- A tells us the result type of the communication, R the "root"-location of the protocol

  pattern Local U = Dep (local U)
  pattern Global = Dep global


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

    _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Global

    -- NOTE, only well "modalized" if W is the current global
    -- modality
    Ext : W ∣ Γ ⊢ L ＠ V / Global -> (ϕ : U ≤ V) -> Γ ⊢Global


    --------------------------------------------------------------
    -- Types
    Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global

    --------------------------------------------------------------
    -- Com
    End : Γ ⊢Com U

    -- A single communication of a protocol with R participants.
    -- We are sending local data from location U₀ to be accessible
    -- at location U₁
    [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / Global ] ⊢Com R) -> Γ ⊢Com R



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

  wk-Mod,ind Δ (Dep t) = Dep t
  -- wk-Mod,ind Δ (local U) = local U
  wk-Mod,ind Δ (Com R A) = Com R (wk-Sort,ind Δ A)


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

    b0 : W ∣ Γ ⊢ Base BB / Local U
    b1 : W ∣ Γ ⊢ Base BB / Local U
    n0 : W ∣ Γ ⊢ Base NN / Local U

    -- We only have to implement this term if our current location `U`
    -- Is part of the implemented locations `W`
    loc : (W ∣ Γ ⊢ L / Local U) -> W ∣ Γ ⊢ (L ＠ U) / Global

    -- loc : (Γ ⊢ L / Local U) -> Γ ⊢ (L ＠ U) / Global

    -- Given a value of type L at location U, we can make it into a local
    -- value of type L at location V, as long as V is a location which can access U
    -- (ie, is a superset).
    [_]unloc : (ϕ : U ≤ V) -> W ∣ Γ ⊢ (L ＠ U) / Global -> W ∣ Γ ⊢ L / Local V




    fromext : {ϕ : V ≤ U} -> {val : W ∣ Γ ⊢ L ＠ U / Global} -> W ∣ Γ ⊢ Ext val ϕ / Global -> W ∣ Γ ⊢ L ＠ V / Global


    lam : W ∣ Γ ,[ E ] ⊢ S / (Dep d)  -> W ∣ Γ ⊢ ⨅ E S / (Dep d)
    app : W ∣ Γ ⊢ ⨅ (T / (Dep d)) S / n -> (t : W ∣ Γ ⊢ T / (Dep d)) -> W ∣ Γ ⊢ su-Sort t S / n


    π₁ : W ∣ Γ ⊢ (T ⊗ S) / m -> W ∣ Γ ⊢ T / m
    π₂ : W ∣ Γ ⊢ (T ⊗ S) / m -> W ∣ Γ ⊢ S / m
    _,_ : W ∣ Γ ⊢ T / m -> W ∣ Γ ⊢ S / m -> W ∣ Γ ⊢ (T ⊗ S) / m


    -------------------
    -- protocols
    _∋_ : (P : Γ ⊢Com R) -> W ∣ Γ ⊢ P / Com R A -> W ∣ Γ ⊢ Com R A / Global

    _►_ : {ϕ : R ≤ U₁} -> {ψ : U₁ ≤ U₀}
        -> ∀ {C}
        -> (val : W ∣ Γ ⊢ L ＠ U₀ / Global)
        -> W ∣ Γ ,[ Ext val ψ / Global ] ⊢ special-su-top (fromext (var zero) ) C / Com R (wk-Sort A)
        -> W ∣ Γ ⊢ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) / Com R A

    ret : W ∣ Γ ⊢ A / Global -> W ∣ Γ ⊢ End / Com R A


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

    ⨅ : W ∣ Γ ⊢WFEntry E -> W ∣ Γ ,[ E ] ⊢WFSort T / (Dep d) -> W ∣ Γ ⊢WFSort (⨅ E T) / (Dep d)

    -- (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : W ∣ Γ ⊢WFSort S / m -> W ∣ Γ ⊢WFSort T / m -> W ∣ Γ ⊢WFSort (S ⊗ T) / m

    --------------------------------------------------------------
    -- Local

    Base : ∀{B} -> W ∣ Γ ⊢WFSort (Base B) / m

    Loc : W ∣ Γ ⊢WFSort L / Local U -> W ∣ Γ ⊢WFSort (L ＠ U) / Global


    -- NOTE, only well "modalized" if W is the current global
    -- modality
    -- Ext : W ∣ Γ ⊢ Loc V L / Global -> (ϕ : U ≤ V) -> Γ ⊢Global


    -- --------------------------------------------------------------
    -- -- Types
    -- Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global

    -- --------------------------------------------------------------
    -- -- Com
    -- End : Γ ⊢Com U

    -- -- A single communication of a protocol with R participants.
    -- -- We are sending local data from location U₀ to be accessible
    -- -- at location U₁
    -- [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / Global ] ⊢Com R) -> Γ ⊢Com R



  data _∣_⊢WFMod_ where
    -- type : W ∣ Γ ⊢WFMod global
    -- local : W ∣ Γ ⊢WFMod local U
    Dep : ∀ (d : DepMod k) -> W ∣ Γ ⊢WFMod (Dep d)
    Com : W ∣ Γ ⊢WFSort (A / Global) -> W ∣ Γ ⊢WFMod Com R A


  data _∣_⊢WFCtx : ⟨ P ⟩ -> ∀ (Γ : Ctx) -> 𝒰₀ where
    [] : W ∣ [] ⊢WFCtx
    _,[_] : W ∣ Γ ⊢WFCtx -> W ∣ Γ ⊢WFEntry E -> W ∣ Γ ,[ E ] ⊢WFCtx



  ----------------------------------------------------------
  -- Meta theorems

  -- We can restrict terms to smaller locations (W)
  --


  restrict-Ctx : W₀ ≤ W₁ -> ∀ Γ -> W₁ ∣ Γ ⊢WFCtx -> Ctx
  restrict-Sort : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> (S : Γ ⊢Sort k) -> (m : Γ ⊢Mod k) -> W₁ ∣ Γ ⊢WFSort (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Sort k
  restrict-Mod : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx ) -> (m : Γ ⊢Mod k) -> W₁ ∣ Γ ⊢WFMod m -> restrict-Ctx ϕ Γ ΓP ⊢Mod k

  -- restrict-Entry : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> W₁ ∣ Γ ⊢WFEntry (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Entry k
  -- restrict-Entry = {!!}

  restrict-Mod ϕ ΓP (Dep d) (Dep d) = Dep d
  restrict-Mod ϕ ΓP (Com R A) (Com Ap) = Com R (restrict-Sort ϕ ΓP A Global Ap)


  restrict-Ctx ϕ [] P = []
  restrict-Ctx ϕ (Γ ,[ S / m ]) (ΓP ,[ SP / mP ]) = restrict-Ctx ϕ Γ ΓP ,[ restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP  ]


  restrict-Sort ϕ ΓP (⨆ E S) m P = {!!}
  restrict-Sort ϕ ΓP (⨅ (S / m) T) (Dep d') (⨅ (SP / mP) TP) = ⨅ (restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP) (restrict-Sort ϕ (ΓP ,[ SP / mP ]) T (Dep d') TP)
  restrict-Sort ϕ ΓP (S ⊗ T) m (SP ⊗ TP) = restrict-Sort ϕ ΓP S m SP ⊗ restrict-Sort ϕ ΓP T m TP
  restrict-Sort ϕ ΓP (Base x) m Base = Base x
  restrict-Sort ϕ ΓP (L ＠ U) m (Loc P) = restrict-Sort ϕ ΓP L (Local U) P ＠ U
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
  restrict-Term ϕ ΓP (Loc {U = U} SP) (Dep .global) (loc t) = loc (restrict-Term ϕ ΓP SP (Dep (local U)) t)
  restrict-Term ϕ ΓP SP mP ([ ϕ₁ ]unloc t) = {!!}
  restrict-Term ϕ ΓP SP mP (fromext t) = {!!}
  restrict-Term ϕ ΓP (⨅ TP SP) (Dep d) (lam t) = lam (restrict-Term ϕ (ΓP ,[ TP ]) SP (Dep d) t )
  restrict-Term ϕ ΓP SP mP (app t s) = {!app ? ?!}
  restrict-Term ϕ ΓP SP mP (π₁ t) = {!!}
  restrict-Term ϕ ΓP SP mP (π₂ t) = {!!}
  restrict-Term ϕ ΓP SP mP (t , t₁) = {!!}






module Examples where

  PP : Space
  PP = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))

  uu vv : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  vv = ⦗ # 1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  all = uu ∨ vv

  ε : Ctx {PP}
  ε = []

  T0 : ∀{Γ : Ctx {PP}} -> Γ ⊢Global
  T0 = (Base NN ＠ uu) ⊗ (Base NN ＠ vv)

  t1 : all ∣ ε ⊢ ⨅ (T0 / Global) (Base NN ＠ uu) / Global
  t1 = lam (π₁ (var zero))

  -- t2 : all ∣ ε ⊢ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / Global) → ((Base NN ⊗ Base NN) ＠ uu) / Global

  t2 : all ∣ ε ⊢ ⨅ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / Global) ((Base NN ⊗ Base NN) ＠ uu) / Global
  t2 = lam (loc ((let x = π₂ (var zero) in [ {!!} ]unloc x) , {!!}))
  -- lam (loc ([ reflexive ]unloc (π₁ (var zero)) , [ reflexive ]unloc (π₁ (var zero))))

  f : (uu ∧ vv) ≤ vv
  f = π₁-∧

  t3 : all ∣ ε ⊢ ⨅ (Base NN ＠ uu / Global) (Com (uu ∧ vv) (Base NN ＠ vv)) / Global
  t3 = {!!} -- lam (([ Base NN from uu to (uu ∧ vv) [ reflexive ⨾ π₀-∧ ]on all ]► End) ∋ (var zero ► ret (loc λ _ -> [ f ]unloc (fromext (var zero)))))






