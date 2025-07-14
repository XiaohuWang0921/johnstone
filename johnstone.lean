def monic (f : α → β) :=
  ∀ x y, f x = f y → x = y

def johnstone (φ : Prop → Prop) (μ : monic φ) (p : Prop) : φ (φ p) = p :=
  let UT := {q // φ q}

  let UP := ∃ q, φ q

  let VP := ∃ q, φ q ∧ q

  have h₀ : φ True → VP :=
    fun w => ⟨True, w, trivial⟩

  have h₁ : VP → φ True :=
    fun ⟨_, w₀, w₁⟩ =>
      (propext ⟨fun _ => trivial, fun _ => w₁⟩).rec w₀

  have h₂ : φ True = VP :=
    propext ⟨h₀, h₁⟩

  have h₃ : ∀ t : UT, t.val → VP :=
    fun ⟨q, w₀⟩ w₁ => ⟨q, w₀, w₁⟩

  have h₄ : ∀ t : UT, VP → t.val :=
    fun ⟨q₀, w₀⟩ ⟨q₁, w₁, w₂⟩ =>
      have l₀ : φ q₁ = φ q₀ := propext ⟨fun _ => w₀, fun _ => w₁⟩
      have l₁ : q₁ = q₀ := μ q₁ q₀ l₀
      @l₁.rec Prop q₁ (fun a _ => a) w₂

  have h₅ : ∀ t : UT, t.val = VP :=
    fun t => propext ⟨h₃ t, h₄ t⟩

  have h₆ : φ VP → UP := fun w => ⟨VP, w⟩

  have h₇ : UP → φ VP :=
    fun ⟨q, w⟩ => (h₅ ⟨q, w⟩).rec w

  have h₈ : φ VP = UP :=
    propext ⟨h₆, h₇⟩

  have h₉ : ∀ t : UT, t.val → t.val = UP :=
      fun ⟨q, w₀⟩ w₁ =>
        propext ⟨fun _ => ⟨q, w₀⟩, fun _ => w₁⟩

  have h₁₀ : φ True → φ UP :=
    fun w => (h₉ ⟨True, w⟩ trivial).rec w

  have h₁₁ : φ UP → φ True :=
    fun w => h₁ ⟨UP, w, UP, w⟩

  have h₁₂ : φ UP = φ True :=
    propext ⟨h₁₁, h₁₀⟩

  have h₁₃ : UP = True :=
    μ UP True h₁₂

  have h₁₄ : φ (φ True) = True :=
    (congr (Eq.refl φ) h₂).trans (h₈.trans h₁₃)

  have h₁₅ : φ (φ p) → p :=
    fun w =>
      have l₀ : True = φ (φ p) := propext ⟨fun _ => w, fun _ => trivial⟩
      have l₁ : φ (φ True) = φ (φ p) := trans h₁₄ l₀
      have l₂ : True = p := μ True p <| μ (φ True) (φ p) l₁
      l₂.rec trivial

  have h₁₆ : p → φ (φ p) :=
    fun w =>
      have l₀ : True = p := propext ⟨fun _ => w, fun _ => trivial⟩
      have l₁ : (φ ∘ φ) True = (φ ∘ φ) p := congr (Eq.refl <| φ ∘ φ) l₀
      have l₂ : True = φ (φ p) := Eq.trans (Eq.symm h₁₄) l₁
      l₂.rec trivial

  propext ⟨h₁₅, h₁₆⟩
