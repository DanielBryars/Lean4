| Connective | Rule | Term Mode | Tactic Mode |
|------------|------|------------|--------------|
| → | →-Intro | `theorem imp_intro (P Q : Prop) (h : P → Q) : P → Q := h` | `theorem imp_intro (P Q : Prop) (h : P → Q) : P → Q := by exact h` |
| → | →-Elim (MP) | `theorem mp (P Q : Prop) (hpq : P → Q) (hp : P) : Q := hpq hp` | `theorem mp (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by exact hpq hp` |
| → | Modus Tollens (MT) | `theorem mt (P Q : Prop) (hpq : P → Q) (hnq : ¬Q) : ¬P := fun hp => hnq (hpq hp)` | `theorem mt (P Q : Prop) (hpq : P → Q) (hnq : ¬Q) : ¬P := by intro hp; exact hnq (hpq hp)` |
| ∧ | ∧-Intro | `theorem and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := And.intro hp hq` | `theorem and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by exact And.intro hp hq` |
| ∧ | ∧-Elim Left | `theorem and_elim_left (P Q : Prop) (h : P ∧ Q) : P := h.left` | `theorem and_elim_left (P Q : Prop) (h : P ∧ Q) : P := by exact h.left` |
| ∧ | ∧-Elim Right | `theorem and_elim_right (P Q : Prop) (h : P ∧ Q) : Q := h.right` | `theorem and_elim_right (P Q : Prop) (h : P ∧ Q) : Q := by exact h.right` |
| ∨ | ∨-Intro Left | `theorem or_intro_left (P Q : Prop) (hp : P) : P ∨ Q := Or.inl hp` | `theorem or_intro_left (P Q : Prop) (hp : P) : P ∨ Q := by exact Or.inl hp` |
| ∨ | ∨-Intro Right | `theorem or_intro_right (P Q : Prop) (hq : Q) : P ∨ Q := Or.inr hq` | `theorem or_intro_right (P Q : Prop) (hq : Q) : P ∨ Q := by exact Or.inr hq` |
| ∨ | ∨-Elim | `theorem or_elim (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := Or.elim h hp hq` | `theorem or_elim (P Q R : Prop) (h : P ∨ Q) (hp : P → R) (hq : Q → R) : R := by cases h with | inl hp => exact hp _ | inr hq => exact hq _` |
| ¬ | ¬-Intro | `theorem not_intro (P : Prop) (h : P → False) : ¬P := h` | `theorem not_intro (P : Prop) (h : P → False) : ¬P := by exact h` |
| ¬ | ¬-Elim | `theorem not_elim (P : Prop) (h : ¬P) (hp : P) : False := h hp` | `theorem not_elim (P : Prop) (h : ¬P) (hp : P) : False := by exact h hp` |
| ⊥ | Ex Falso | `theorem ex_falso (P : Prop) (h : False) : P := False.elim h` | `theorem ex_falso (P : Prop) (h : False) : P := by exact False.elim h` |
| ↔ | ↔-Intro | `theorem iff_intro (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := Iff.intro h1 h2` | `theorem iff_intro (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by exact Iff.intro h1 h2` |
| ↔ | ↔-Elim Left | `theorem iff_elim_left (P Q : Prop) (h : P ↔ Q) : P → Q := h.mp` | `theorem iff_elim_left (P Q : Prop) (h : P ↔ Q) : P → Q := by exact h.mp` |
| ↔ | ↔-Elim Right | `theorem iff_elim_right (P Q : Prop) (h : P ↔ Q) : Q → P := h.mpr` | `theorem iff_elim_right (P Q : Prop) (h : P ↔ Q) : Q → P := by exact h.mpr` |
| ∀ | ∀-Intro | `theorem forall_intro (α : Type) (P : α → Prop) (h : ∀ x, P x) : ∀ x, P x := h` | `theorem forall_intro (α : Type) (P : α → Prop) (h : ∀ x, P x) : ∀ x, P x := by exact h` |
| ∀ | ∀-Elim | `theorem forall_elim (α : Type) (P : α → Prop) (h : ∀ x, P x) (a : α) : P a := h a` | `theorem forall_elim (α : Type) (P : α → Prop) (h : ∀ x, P x) (a : α) : P a := by exact h a` |
| ∃ | ∃-Intro | `theorem exists_intro (α : Type) (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := Exists.intro a h` | `theorem exists_intro (α : Type) (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := by exact Exists.intro a h` |
| ∃ | ∃-Elim | `theorem exists_elim (α : Type) (P : α → Prop) (R : Prop) (h : ∃ x, P x) (k : ∀ a, P a → R) : R := Exists.elim h k` | `theorem exists_elim (α : Type) (P : α → Prop) (R : Prop) (h : ∃ x, P x) (k : ∀ a, P a → R) : R := by cases h with | intro x hx => exact k x hx` |
