universes u v

def monic {α : Type u} {β : Type v} (f : α → β) :=
  ∀ x y, f x = f y → x = y

section johnstone

open true

variables
  (p : Prop)
  (φ : Prop → Prop)
  (μ : monic φ)

theorem johnstone : φ (φ p) = p :=
  let
    UT := {q // φ q},
    VT := {q // φ q ∧ q},
    UP := ∃ q, φ q,
    VP := ∃ q, φ q ∧ q,

    h₀ (w : φ true) : VP :=
      ⟨true, w, intro⟩,

    h₁ : VP → φ true :=
      λ ⟨_, w₀, w₁⟩,
        eq.rec w₀ $
          propext ⟨(λ _, intro), (λ _, w₁)⟩,
  
    h₂ : φ true = VP :=
      propext ⟨h₀, h₁⟩,
  
    h₃ : ∀ t : UT, t.val → VP :=
      λ ⟨q, w₀⟩ w₁, ⟨q, w₀, w₁⟩,
  
    h₄ : ∀ t : UT, VP → t.val :=
      λ ⟨q₀, w₀⟩ ⟨q₁, w₁, w₂⟩,
        @eq.rec Prop q₁ id w₂ q₀ $
          μ q₁ q₀ $
            propext ⟨(λ _, w₀), (λ _, w₁)⟩,
  
    h₅ (t : UT) : t.val = VP :=
      propext ⟨h₃ t, h₄ t⟩,
  
    h₆ (w : φ VP) : UP :=
      ⟨VP, w⟩,
  
    h₇ : UP → φ VP :=
      λ ⟨q, w⟩,
        eq.rec w $
          h₅ ⟨q, w⟩,
  
    h₈ : φ VP = UP :=
      propext ⟨h₆, h₇⟩,
  
    h₉ : ∀ t : UT, t.val → t.val = UP :=
      λ ⟨q, w₀⟩ w₁,
        propext ⟨(λ _, ⟨q, w₀⟩), (λ _, w₁)⟩,
  
    h₁₀ (w : φ true) : φ UP :=
      eq.rec w $
        h₉ ⟨true, w⟩ intro,
  
    h₁₁ (w : φ UP) : φ true :=
      h₁ ⟨UP, w, UP, w⟩,
  
    h₁₂ : φ UP = φ true :=
      propext ⟨h₁₁, h₁₀⟩,
  
    h₁₃ : UP = true :=
      μ UP true h₁₂,
  
    h₁₄ : φ (φ true) = true :=
      trans (congr (eq.refl φ) h₂) $
        trans h₈ h₁₃,
  
    h₁₅ (w : φ $ φ p) : p :=
      @eq.rec Prop true id true.intro p $
        μ true p $
          μ (φ true) (φ p) $
            trans h₁₄ $
              propext ⟨(λ _, w), (λ _, intro)⟩,
  
    h₁₆ (w : p) : φ $ φ p :=
      @eq.rec Prop true id true.intro (φ $ φ p) $
        trans (symm h₁₄) $
          congr (eq.refl φ) $
            congr (eq.refl φ) $
              propext ⟨(λ _, w), (λ _, intro)⟩
  in
    propext ⟨h₁₅, h₁₆⟩

end johnstone