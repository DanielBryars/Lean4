theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
    apply And.intro
    case left => exact hp
    case right =>
      apply And.intro
      case left =>
        exact hq
      case right =>
        exact hp

#print test

/-
Prove: R → P, P→ ¬R ⊨ ¬R
-/

theorem notR (R P : Prop) (h1 : R → P) (h2: P → ¬R) : ¬R := by
  intro r -- assume r
  have p:= h1 r -- modus ponens (P given R)
  have nr:= h2 p -- modus ponens (¬R given P)
  exact nr r -- This is a condradiction

#print notR

--or function mode:
theorem notR_fun (R P : Prop) (h1 : R → P) (h2: P → ¬R) : ¬R :=
  fun r => h2 (h1 r) r

--we define an excluded middle (interesting)
theorem notR_classical
  (R S : Prop)
  (h1 : R → S)
  (h2 : S → ¬R)
  (excluded_middle : S ∨ ¬S) :
  ¬R := by

  cases excluded_middle with
  | inl s =>         -- Case 1: assume S
    exact h2 s       -- use S → ¬R to conclude ¬R

  | inr ns =>        -- Case 2: assume ¬S
    intro r          -- assume R
    have s := h1 r   -- from R → S
    apply ns s       -- contradiction: ¬S applied to S

/-
Okay now lets do
(A∨B)∧C ⊢ (A∧C)∨(B∧C)
-/

--theorem distributional (A B C : Prop) (h1 : (A∧B)∨C) : (A∨C)∧(B∨C) := by
--  cases h1 with
--  | inl hab =>
--    -- hab (A∧B)
--    let ha L= hab.left
theorem distributional (A B C : Prop) (h1 : (A ∧ B) ∨ C) : (A ∨ C) ∧ (B ∨ C) := by
  cases h1 with
  | inl hab =>
    -- hab : A ∧ B
    let ha := hab.left -- We know A is true
    let hb := hab.right -- We know B is true
    apply And.intro
    · exact Or.inl ha  -- A ∨ C
    · exact Or.inl hb  -- B ∨ C
  | inr hc =>
    -- hc : C
    apply And.intro
    · exact Or.inr hc  -- A ∨ C
    · exact Or.inr hc  -- B ∨ C

#print distributional
