module ExtensionSystem where

open import Level
open import Function using (_$_)
open import Data.Product renaming (_×_ to _∧_)
open import Categories.Category
open import Categories.Functor renaming (id to Id)
open import Categories.Monad.Relative renaming (Monad to RMonad)
open import Categories.Monad
open import Categories.NaturalTransformation

-- formalizing the notion 'extension system', formerly known as 'kleisli-triple' and proving that it is equivalent to a monad
-- https://ncatlab.org/nlab/show/extension+system

private
    variable
        o ℓ e : Level


-- typedef, an extensionsystem is a specilization of RMonad
ExtensionSystem : (𝒞 : Category o ℓ e) → Set (o ⊔ ℓ ⊔ e)
ExtensionSystem 𝒞 = (RMonad (Id {C = 𝒞}))


--*
-- Proposition: ExtensionSystem is an equivalent definition of monad
--*

-- '→' 
ExtensionSystem→Monad : ∀ {𝒞 : Category o ℓ e} → ExtensionSystem 𝒞 → Monad 𝒞
ExtensionSystem→Monad {𝒞 = 𝒞} 𝐾 = record
    { F = T
    ; η = η'
    ; μ = μ'
    -- M3
    ; identityˡ = Identityˡ
    -- M2
    ; identityʳ = K2
    -- M1
    ; assoc = assoc'
    ; sym-assoc = sym assoc'
    }
    where
        open RMonad 𝐾 using (unit) renaming (extend to _ᵀ; F₀ to T₀; extend-≈ to ᵀ-≈; identityˡ to K1; identityʳ to K2; assoc to K3)
        open Category 𝒞 renaming (id to idC)
        open HomReasoning
        T : Endofunctor 𝒞
        T = RMonad⇒Functor 𝐾
        open Functor T renaming (F₁ to T₁)
        open Equiv
        -- constructing the natural transformation η from the given family of morphisms 'unit' 
        η' = ntHelper {F = Id} {G = T} record
            { η = λ X → unit
            ; commute = λ {X} {Y} f → sym K2
            }
        -- constructing the natural transformation μ
        μ' = ntHelper {F = T ∘F T} {G = T} record
            { η = λ X → (idC {A = T₀ X})ᵀ
            ; commute = λ {X} {Y} f → begin 
                    ((idC ᵀ) ∘ (unit ∘ (unit ∘ f)ᵀ)ᵀ)       ≈⟨ (sym $ K3) ⟩ 
                    (((idC ᵀ) ∘ unit ∘ ((unit ∘ f) ᵀ)) ᵀ)   ≈⟨ ᵀ-≈ sym-assoc ⟩
                    ((((idC ᵀ) ∘ unit) ∘ ((unit ∘ f) ᵀ)) ᵀ) ≈⟨ ᵀ-≈ (∘-resp-≈ˡ K2) ⟩
                    ((idC ∘ ((unit ∘ f) ᵀ)) ᵀ)              ≈⟨ ᵀ-≈ identityˡ ⟩
                    (((unit ∘ f) ᵀ) ᵀ)                      ≈⟨ ᵀ-≈ (sym identityʳ) ⟩
                    ((((unit ∘ f) ᵀ) ∘ idC) ᵀ)              ≈⟨ K3 ⟩ 
                    (unit ∘ f)ᵀ ∘ (idC ᵀ) ∎
            }
        open NaturalTransformation η' using () renaming (η to η)
        open NaturalTransformation μ' using () renaming (η to μ)
        Identityˡ = λ {X} → begin 
            (μ X ∘ ((η (T₀ X)) ∘ (η X))ᵀ)             ≈⟨ (sym $ K3) ⟩ 
            (((idC ᵀ) ∘ η (T₀ X) ∘ η X) ᵀ)            ≈⟨ ᵀ-≈ sym-assoc ⟩
            ((((idC ᵀ) ∘ η (T₀ X)) ∘ η X) ᵀ)          ≈⟨ ᵀ-≈ (∘-resp-≈ˡ K2) ⟩
            ((idC ∘ η X) ᵀ)                           ≈⟨ ᵀ-≈ identityˡ ⟩
            (η X ᵀ)                                   ≈⟨ K1 ⟩
            idC ∎ 
        assoc' = λ {X} → begin
            idC ᵀ ∘ (η _ ∘ idC ᵀ)ᵀ                    ≈⟨ sym K3 ⟩ 
            (((idC ᵀ) ∘ η (T₀ X) ∘ (idC ᵀ)) ᵀ)        ≈⟨ ᵀ-≈ sym-assoc ⟩
            ((((idC ᵀ) ∘ η (T₀ X)) ∘ (idC ᵀ)) ᵀ)      ≈⟨ ᵀ-≈ (∘-resp-≈ˡ K2) ⟩
            ((idC ∘ (idC ᵀ)) ᵀ)                       ≈⟨ ᵀ-≈ identityˡ ⟩
            ((idC ᵀ) ᵀ)                               ≈⟨ ᵀ-≈ (sym identityʳ) ⟩
            (((idC ᵀ) ∘ idC) ᵀ)                       ≈⟨ K3 ⟩
            idC ᵀ ∘ idC ᵀ ∎

-- '←'
Monad→ExtensionSystem : ∀ {𝒞 : Category o ℓ e} → Monad 𝒞 → ExtensionSystem 𝒞
Monad→ExtensionSystem {𝒞 = 𝒞} 𝑀 = record
    { F₀ = T₀
    ; unit = η _
    ; extend = λ {X} {Y} f → μ Y ∘ T₁ f
    -- K1
    ; identityˡ = M3
    -- K2
    ; identityʳ = λ {X} {Y} {f} → begin 
        (μ Y ∘ T₁ f) ∘ η X                            ≈⟨ assoc ⟩ 
        (μ Y ∘ T₁ f ∘ η X)                            ≈⟨ ∘-resp-≈ʳ (sym (η-commute _)) ⟩
        (μ Y ∘ η (T₀ Y) ∘ f)                          ≈⟨ sym-assoc ⟩
        ((μ Y ∘ η (T₀ Y)) ∘ f)                        ≈⟨ ∘-resp-≈ˡ M2 ⟩
        (idC ∘ f) ≈⟨ identityˡ ⟩
        f ∎
    -- K3
    ; assoc = λ {X} {Y} {Z} {f} {g} → begin 
        μ Z ∘ T₁ ((μ Z ∘ T₁ g) ∘ f)                   ≈⟨ ∘-resp-≈ʳ homomorphism ⟩
        (μ Z ∘ (T₁ (μ Z ∘ T₁ g) ∘ T₁ f))              ≈⟨ ∘-resp-≈ʳ (∘-resp-≈ˡ homomorphism) ⟩ 
        (μ Z ∘ (T₁ (μ Z) ∘ T₁ (T₁ g)) ∘ T₁ f)         ≈⟨ sym-assoc ⟩ 
        ((μ Z ∘ T₁ (μ Z) ∘ T₁ (T₁ g)) ∘ T₁ f)         ≈⟨ ∘-resp-≈ˡ sym-assoc ⟩ 
        (((μ Z ∘ T₁ (μ Z)) ∘ T₁ (T₁ g)) ∘ T₁ f)       ≈⟨ ∘-resp-≈ˡ (∘-resp-≈ˡ M1) ⟩ 
        (((μ Z ∘ μ (T₀ Z)) ∘ T₁ (T₁ g)) ∘ T₁ f)       ≈⟨ ∘-resp-≈ˡ assoc ⟩ 
        ((μ Z ∘ μ (T₀ Z) ∘ T₁ (T₁ g)) ∘ T₁ f)         ≈⟨ ∘-resp-≈ˡ (∘-resp-≈ʳ (μ-commute g)) ⟩ 
        ((μ Z ∘ T₁ g ∘ μ Y) ∘ T₁ f)                   ≈⟨ assoc ⟩ 
        (μ Z ∘ (T₁ g ∘ μ Y) ∘ T₁ f)                   ≈⟨ ∘-resp-≈ʳ assoc ⟩ 
        (μ Z ∘ T₁ g ∘ μ Y ∘ T₁ f)                     ≈⟨ sym-assoc ⟩ 
        (μ Z ∘ T₁ g) ∘ μ Y ∘ T₁ f ∎
    ; extend-≈ = λ fg → ∘-resp-≈ʳ (T-resp-≈ fg) 
    }
    where
        open Category 𝒞 renaming (id to idC)
        open Monad 𝑀 using () renaming (F to T; η to η'; μ to μ'; assoc to M1; identityʳ to M2; identityˡ to M3)
        open Functor T renaming (F₀ to T₀; F₁ to T₁; F-resp-≈ to T-resp-≈)
        open NaturalTransformation η' using (η) renaming (commute to η-commute)
        open NaturalTransformation μ' renaming (η to μ; commute to μ-commute)
        open HomReasoning
        open Equiv

-- proof:
ExtensionSystem↔Monad : ∀ {𝒞 : Category o ℓ e} → (Monad 𝒞 → ExtensionSystem 𝒞) ∧ (ExtensionSystem 𝒞 → Monad 𝒞)
ExtensionSystem↔Monad {𝒞} = (Monad→ExtensionSystem , ExtensionSystem→Monad)