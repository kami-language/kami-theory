


module KamiTheory.Experiments.tst where



module Version1 where
  mutual
    data Ctx : Set where
      _,_ : (Γ : Ctx) -> Type Γ -> Ctx

    data Type : Ctx -> Set where
      Pi : ∀{Γ A} -> Type (Γ , A) -> Type Γ



module Version2 where

  data Ctx : Set
  data Type : Ctx -> Set

  data Ctx where
    _,_ : (Γ : Ctx) -> Type Γ -> Ctx

  data Type where
    Pi : ∀{Γ A} -> Type (Γ , A) -> Type Γ



