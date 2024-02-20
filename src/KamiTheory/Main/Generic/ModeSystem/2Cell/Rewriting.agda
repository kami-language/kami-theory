
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Generic.ModeSystem.2Cell.Rewriting where

open import Agora.Conventions
open import KamiTheory.Basics
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.Modality
-- open import KamiTheory.Main.Generic.ModeSystem.LinearFSM.Definition
open import KamiTheory.Order.StrictOrder.Base

open import Data.Fin using (Fin ; zero ; suc)


import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition as D


module 2CellRewriting (G : 2Graph 𝑖) where
  open D.2CellDefinition G

  private variable
    a b c d e f : 0Cell G
    μ : 1Cell G a b
    η : 1Cell G b c
    ω : 1Cell G c d
    η₀ η₁ : 1Cell G b c
    τ₀ τ₁ : 1Cell G e f
    ξ₀ ξ₁ : 1Cell G e f
    v : Visibility

  ------------------------------------------------------------------------
  -- 2Cell patterns

  record SingleFace v (a d : 0Cell G) : 𝒰 𝑖 where
    constructor _⌟[_]⌞_
    field {pb pc} : 0Cell G
    field idₗ : 1Cell G a pb
    field {cξ₀ cξ₁} : 1Cell G pb pc
    field face : Face G v cξ₀ cξ₁
    field idᵣ : 1Cell G pc d

  open SingleFace public

  as2CellGen : ∀{v} -> (ξ : SingleFace v a d) -> Some2CellGen v ((ξ .idₗ) ◆ (ξ .cξ₀) ◆ (ξ .idᵣ)) ((ξ .idₗ) ◆ (ξ .cξ₁) ◆ (ξ .idᵣ))
  as2CellGen (μ ⌟[ ξ ]⌞ η) = incl (μ ⌟[ ξ ]⌞ η ⌟)


  record SubSingleFace v {a d : 0Cell G} (ξ : SingleFace v a d) : 𝒰 𝑖 where
    field {a' d'} : 0Cell G
    field extₗ : 1Cell G a a'
    field keepₗ : 1Cell G a' (ξ .pb)
    field keepᵣ : 1Cell G (ξ .pc) d'
    field extᵣ : 1Cell G d' d
    field proofₗ : extₗ ◆ keepₗ ≡ ξ .idₗ
    field proofᵣ : keepᵣ ◆ extᵣ ≡ ξ .idᵣ

  open SubSingleFace public

  record Some2CellGenOnPoints v (a b : 0Cell G) : 𝒰 𝑖 where
    field top : 1Cell G a b
    field bottom : 1Cell G a b
    field get : Some2CellGen v top bottom

  open Some2CellGenOnPoints public



  record 2CellLinePattern v 𝑗 (n : ℕ) : 𝒰 (𝑗 ⁺ ､ 𝑖) where
    field State : ℕ -> 𝒰 𝑗
    field start : State zero
    field step : ∀{i} -> (s : State i)
                 -> ∀{a b}
                 -> (ξ : SingleFace v a b)
                 -- -> Maybe (SubSingleFace v ξ ×-𝒰 State (suc i))
                 -> Maybe (Some2CellGenOnPoints v a b ×-𝒰 State (suc i))

  open 2CellLinePattern public






  ----------------------------------------------------------
  -- Splits

  record SplitGen v (a d : 0Cell G) : 𝒰 𝑖 where -- (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⧓⌞_⌟⧓_ -- [_,_]
    field {pb pc} : 0Cell G
    field {left₀ left₁} : 1Cell G a pb
    field {right₀ right₁} : 1Cell G pc d
    field leftξ : Some2CellGen v left₀ left₁
    field center : Some2CellGenOnPoints v pb pc
    field rightξ : Some2CellGen v right₀ right₁
    -- field proof₀ : left₀ ◆ (center .top) ◆ right₀ ≡ μ
    -- field proof₁ : left₁ ◆ (center .bottom) ◆ right₁ ≡ η

  open SplitGen


  _↷-SplitGen_ : ∀{v} -> {ω₀ ω₁ : 1Cell G a b} -> (ξ : Some2CellGen v ω₀ ω₁) -> SplitGen v b c -> SplitGen v a c
  _↷-SplitGen_ {ω₀ = ω₀} {ω₁} ξ (leftξ ⧓⌞ center ⌟⧓ rightξ) = (ξ ⧓ leftξ) ⧓⌞ center ⌟⧓ rightξ
  -- _↷-SplitGen_ = {!!} -- {ω₀ = ω₀} {ω₁} ξ (leftξ ⧓⌞ center ⌟⧓ rightξ [ proof₀ , proof₁ ]) = (ξ ⧓ leftξ) ⧓⌞ center ⌟⧓ rightξ [ cong-≡ (ω₀ ◆_) proof₀ , cong-≡ (ω₁ ◆_) proof₁ ]



  -- Given a pattern, we try to find the next matching face in a gen-row
  findNext : ∀{n}
             -> {v : Visibility}
             -> 2CellLinePattern v 𝑗 (suc n)
             -> {a b : 0Cell G} (ϕs : FreeParts a b) {μ η : 1Cell G a b}
             -> {μp : Partition m ϕs μ}
             -> {ηp : Partition m ϕs η}
             -> 2CellGen v ϕs μp ηp
             -> Maybe (SplitGen v a b ×-𝒰 2CellLinePattern v 𝑗 n)
  findNext pat ([ ϕ ]) (ϕ ⌟) = nothing
  findNext pat (ϕ ∷ [ ψ ]) (ϕ ⌟[ ξ ]⌞ .ψ ⌟) with (pat .step (pat .start) (ϕ ⌟[ ξ ]⌞ ψ))

  ... | no x = nothing
  ... | yes (ξ₊ , s) = yes ( (incl (id ⌟) ⧓⌞ ξ₊ ⌟⧓ incl (id ⌟))
                           , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })
  -- yes ((incl (ξ₊ .extₗ ⌟) ⧓⌞ ξ₊ .keepₗ ⌟[ ξ ]⌞ ξ₊ .keepᵣ ⌟⧓ incl (ξ₊ .extᵣ ⌟) [ {!!} , {!!} ])
  --                          , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

  -- ... | yes (ξ₊ , s) = yes ((incl (ξ₊ .extₗ ⌟) ⧓⌞ ξ₊ .keepₗ ⌟[ ξ ]⌞ ξ₊ .keepᵣ ⌟⧓ incl (ξ₊ .extᵣ ⌟) [ {!!} , {!!} ])
  --                          , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

  findNext pat (ϕ ∷ (ψ ∷ ψs)) (ϕ ⌟[ ξ ]⌞ ξs) with (pat .step (pat .start) (ϕ ⌟[ ξ ]⌞ ψ))

  findNext pat (ϕ ∷ (ψ ∷ ψs)) (ϕ ⌟[ ξ ]⌞ .ψ ⌟[ ζ ]⌞ ξs) | yes (ξ₊ , s) = yes (((incl (id ⌟) ⧓⌞ ξ₊ ⌟⧓ incl (id ⌟[ ζ ]⌞ ξs)))
                                                                         , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

      --   yes ((incl (ξ₊ .extₗ ⌟) ⧓⌞ ξ₊ .keepₗ ⌟[ ξ ]⌞ ξ₊ .keepᵣ ⌟⧓ (incl ((ξ₊ .extᵣ ) ⌟[ ζ ]⌞ ξs)) [ {!!} , {!!} ])

      -- , record { State = λ i → pat .State (suc i) ; start = s ; step = λ s -> pat .step s })

  ... | nothing with findNext pat _ ξs
  ... | nothing = nothing
  ... | yes ((incl leftξ ⧓⌞ center ⌟⧓ rightξ ) , nextpat) = yes ((incl (ϕ ⌟[ ξ ]⌞ leftξ) ⧓⌞ center ⌟⧓ rightξ )
                                                                   , nextpat
                                                                   )




  record Split v (a d : 0Cell G) : 𝒰 𝑖 where -- (μ η : 1Cell G a d) : 𝒰 𝑖 where
    constructor _⧓⌞_⌟⧓_
    field {pb pc} : 0Cell G
    field {left₀ left₁} : 1Cell G a pb
    field {center₀ center₁} : 1Cell G pb pc
    field {right₀ right₁} : 1Cell G pc d
    field leftξ : 2Cell v left₀ left₁
    field centerξ : 2Cell v center₀ center₁
    field rightξ : 2Cell v right₀ right₁

  open Split

  splitFromGen : ∀{v} -> SplitGen v a b -> (Split v a b)
  splitFromGen (leftξ ⧓⌞ center ⌟⧓ rightξ) = (leftξ ∷ []) ⧓⌞ (center .get ∷ []) ⌟⧓ (rightξ ∷ [])

  tryMergeSplit : ∀{v} -> SplitGen v a b -> Split v a b -> Maybe (Split v a b)
  tryMergeSplit g s with pb s ≟ pb g | pc s ≟ pc g
  ... | no _ | Y = nothing
  ... | yes refl | no _ = nothing
  ... | yes refl | yes refl with decide-≡-Path (g .left₁) (s .left₀)
  ... | no x = nothing
  ... | yes refl with decide-≡-Path (g .right₁) (s .right₀)
  ... | no x = nothing
  -- ... | yes refl = {!!} -- with decide-≡-Path (g .center .idₗ ◆ g .center .cξ₁ ◆ g .center .idᵣ) (s .center₀)
  ... | yes refl with decide-≡-Path (g .center .bottom) (s .center₀)
  ... | no x = nothing
  ... | yes refl = yes ((g .leftξ ∷ s .leftξ) ⧓⌞ (g .center) .get ∷ s .centerξ ⌟⧓ (g .rightξ ∷ s .rightξ))




  --
  -- |---- overfind --->|
  -- | l  | center | r  |   | direction of 2cells
  -- |--- underfind --->|   v
  -- |----- bottom ---->|
  --
  record Result:findAllLocked v (overfind bottom : 1Cell G a d) : 𝒰 𝑖 where
    field underfind : 1Cell G a d
    field split : Split v a d
    -- field split : Split v overfind underfind
    field bottomξ : 2Cell v underfind bottom

  open Result:findAllLocked

  record Result:findAll v (top bottom : 1Cell G a d) : 𝒰 𝑖 where
    field {overfind} : 1Cell G a d
    field topξ : 2Cell v top overfind
    field result : Result:findAllLocked v overfind bottom

  open Result:findAll



  {-# TERMINATING #-}
  -- Under the assumption that we already "locked in" the 2CellLinePattern,
  -- find the rest of it downstream
  findAllLocked : ∀ n -> ∀ {m k v}
            -- The pattern we are searching for
            -> 2CellLinePattern v 𝑗 (suc n)

            -- We have two 1cells and corresponding current 2cellgens,
            -- one is on the left, which we already checked, and one is
            -- on the right, which we are going to check now
            -> {μ₀ μ₁ : 1Cell G a b}        -> {η₀ η₁ : 1Cell G b c}

            -> {ϕs : FreeParts a b}         -> {ψs : FreeParts b c}
            -> {μ₀p : Partition m ϕs μ₀}     -> {η₀p : Partition k ψs η₀}
            -> {μ₁p : Partition m ϕs μ₁}     -> {η₁p : Partition k ψs η₁}
            -> (ξ : 2CellGen v ϕs μ₀p μ₁p)  -> (ζ : 2CellGen v ψs η₀p η₁p)

            -- Next, we have the rest of the 2cell which is still left "downwards"
            -- (ω is the target 1cell of this whole 2cell)
            -> {ω₀ ω : 1Cell G a c}
            -> 2Cell v ω₀ ω
            -- -> 2Cell v (μ₁ ◆ η₁) ω

            -- We return a split of the upsteam 2cell if we find the pattern
            -> String +-𝒰 (Result:findAllLocked v (μ₀ ◆ η₀) (ω))

  -- We recurse on ζ:
  --
  -- Case 1: if ζ is empty, this means we found nothing in the current
  --         row, so we can return
  findAllLocked n pat ξ (_ ⌟) rest = left "ζ empty case 1"
  --
  -- Case 2: if ζ is not empty, try to find the next face which satisfies the pattern
  findAllLocked n {v = v} pat {μ₁ = μ₁} {η₁ = η₁} ξ ζs@(ϕ ⌟[ ξ₁ ]⌞ ζ) rest with findNext pat _ ζs
  --
  -- Case 2.1: Nothing was found in the current row. So exit.
  ... | no x = no "end 2.1"
  --
  -- Case 2.2: We found a satisfying face.
  --           This means the following:
  --             - We have to call ourselves recursively, to try to
  --               find the rest of the pattern.
  --             - If the recursive call does not work out, we still
  --               continue to search the current line, with the right-part
  --               of the currently returned `SplitGen`, as it might be that
  --               another satisfying face is hiding behind the current one
  --
  --           But, first we need to check whether n is now zero, because if
  --           it is, this means that we finished the whole pattern!
  --
  -- Case 2.2.1: (n = 0): We finished the pattern!
  findAllLocked zero pat ξ (_ ⌟[ ξ₁ ]⌞ ζ) rest | yes (sp , pat2) =
    let x = sp
    in yes (record
      { underfind = _
      ; split = splitFromGen (incl ξ ↷-SplitGen sp)
      ; bottomξ = rest
      })
  --
  -- Case 2.2.2: (n > 0): We still have to search
  --
  -- Case 2.2.2.1: But we don't have any rest-2cell left over (rest = []), so we
  --               cannot complete the pattern. Thus return nothing.
  findAllLocked (suc n) pat ξ (_ ⌟[ ξ₁ ]⌞ ζ) [] | yes (sp , pat2) = no "end 2.2.2.1"
  --
  -- Case 2.2.2.2: We have a rest, and we can take a ζ-new with which to
  --               initialize the recursive call. We also use the new pattern `pat2`
  findAllLocked (suc n) {v = v} pat {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest) | yes (sp@(_⧓⌞_⌟⧓_ {left₁ = left₁} {right₁ = right₁} foundₗ found foundᵣ ) , pat2) with findAllLocked n pat2 (id ⌟) (ζ-new .get) rest
  --
  -- Case 2.2.2.2.1: The recursive call was successful!
  --                 That means that we have to merge the recursive Split with the currently gotten SplitGen
  --                 We have:
  --                  - sp     : SplitGen v (ϕ ◆ ξ₀ ◆ μ) (ϕ ◆ ξ₂ ◆ η₂)
  --                  - res     : Result:findAllLocked v (μ₁ ◆ ϕ ◆ ξ₂ ◆ η₂) ω
  --                 This means that first we can add μ₁ on the left side of sp, by doing (μ₁ ↷-SplitGen sp),
  --                 and then we try to merge with the split in res.
  ... | yes res with tryMergeSplit (incl ξ ↷-SplitGen sp) (res .split)
  --
  -- Case 2.2.2.2.1.1: The merging was successful. This means this is our new result, and we can return :)
  ... | yes newsplit = yes (record { underfind = _ ; split = newsplit ; bottomξ = res .bottomξ })
  --
  -- Case 2.2.2.2.1.2: The merging was not successful, back to the drawing board! We do the same thing as in
  --                   case 2.2.2.2.2
  findAllLocked (suc n) {v = v} pat {μ₀ = μ₀} {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest)
    | yes (sp@(_⧓⌞_⌟⧓_ {left₀ = left₀} {left₁ = left₁} {right₀ = right₀} {right₁ = right₁} foundₗ found foundᵣ ) , pat2)
    | yes res
    | no p with findAllLocked (suc n) pat (get (incl ξ ⧓ (foundₗ ⧓ found .get ))) (foundᵣ .get) (ζ-new ∷ rest)

    -- where ζ-new' : Some2CellGen _ (μ₁ ◆ left₁ ◆ found .idₗ ◆ found .cξ₁ ◆ found .idᵣ ◆ right₁) _
    --       ζ-new' = transp-≡ (cong-≡ (λ ξ -> Some2CellGen v (μ₁ ◆ ξ) η) (sym-≡ pf₁)) ζ-new

  ... | no x = no "end 2.2.2.2.1.2"
  ... | yes res = yes (record { underfind = _ ; split = res .split ; bottomξ = res .bottomξ })
    -- where split-new = transp-≡ (cong-≡ (λ ξ -> Split v (μ₀ ◆ ξ) (underfind res)) (pf₀)) (res .split)
  --
  -- Case 2.2.2.2.2: The recursive call wasn't successful. But this is no reason
  --                 to be sad because as noted in 2.2, there is still a chance that
  --                 we are going to find another satisfying face in the current row
  --                 So we recurse into the current row with the original pattern `pat`.
  --
  --                 Note that agda doesn't see that this call terminates because it doesn't know that
  --                 the foundᵣ is going to be smaller than ζ
  findAllLocked (suc n) {v = v} pat {μ₀ = μ₀} {μ₁ = μ₁} {η₁ = η₁} ξ (_ ⌟[ ξ₁ ]⌞ ζ) (_∷_ {η = η} ζ-new rest)
    | yes (sp@(_⧓⌞_⌟⧓_ {left₁ = left₁} {right₁ = right₁} foundₗ found foundᵣ ) , pat2)
    | no p with findAllLocked (suc n) pat (get (incl ξ ⧓ (foundₗ ⧓ found .get ))) (foundᵣ .get) (ζ-new ∷ rest)

    -- where ζ-new' : Some2CellGen _ (μ₁ ◆ left₁ ◆ found .idₗ ◆ found .cξ₁ ◆ found .idᵣ ◆ right₁) _
    --       ζ-new' = transp-≡ (cong-≡ (λ ξ -> Some2CellGen v (μ₁ ◆ ξ) η) (sym-≡ pf₁)) ζ-new
  --
  -- Case 2.2.2.2.2.1: We are still not successful in this row. This means that we can stop trying now.
  ... | no x = no "end 2.2.2.2.2.1"
  --
  -- Case 2.2.2.2.2.2: We were actually successful! So update the result.
  ... | yes res = yes (record { underfind = _ ; split = res .split ; bottomξ = res .bottomξ })
    -- where split-new = transp-≡ (cong-≡ (λ ξ -> Split v (μ₀ ◆ ξ) (underfind res)) (pf₀)) (res .split)




  -- Repeatedly try to lock in a pattern, and find the rest of it downstream
  findAll : ∀{n v}
            -- The pattern we are searching for
            -> 2CellLinePattern v 𝑗 (suc n)

            -- The top(μ) and bottom(ω) 1cell
            -> {μ ω : 1Cell G a b}

            -- The 2Cell between them which we are searching
            -> 2Cell v μ ω

            -- We return a 4-way split if we find the pattern
            -> String +-𝒰 (Result:findAll v μ ω)

  -- Case 1: we don't allow for empty patterns,
  -- thus this means that we didn't find this
  -- pattern
  findAll pat [] = no "findall empty"

  -- Case 2: we have a 2CellGen ξ which we can check
  findAll pat (ξ ∷ ξs) with findAllLocked _ pat (id ⌟) (ξ .get) ξs

  -- Case 2.1: the happy case, we found our pattern! Now we have
  --           to return the result
  ... | yes res = yes (record { topξ = [] ; result = res })

  -- Case 2.2: if we could not lock-in the pattern in this row,
  --           we recursively try the next
  ... | no prev with findAll pat ξs

  -- Case 2.2.1: the recursive case found it!
  --             we simply add the current row to the top of the result
  ... | yes res = yes (record { topξ = ξ ∷ topξ res ; result = result res })

  -- Case 2.2.2: even the recursive call didn't find this pattern
  --             this means that it doesn't exist, so we return nothing
  ... | no msg = no ("exhausted: " <> msg <> ", prev: " <> prev)








 
