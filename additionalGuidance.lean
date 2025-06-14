/-
A student qualifies for a grant (g) if:
• They either won a competition (c1) or published a paper (c2).
• A verification is provided either by a supervisor (r1) or a committee (r2).
You are told:
• provable (disj c1 c2)
• provable (disj r1 r2)
• provable c1 → provable g, provable c2 → provable g
• provable r1 → provable g, provable r2 → provable g
The goal is to prove provable g
-/

-- (c1 ∨ c2) ∧ (r1 ∨ r2) → G

variable (C1 C2 R1 R2 G: Prop)

--(corp: C1∨C2)
--(vsvc: R1∨R2)

example
  (h : (C1 ∨ C2) ∧ (R1 ∨ R2))
  (c1 : C1 → G)
  (c2 : C2 → G)
  (r1 : R1 → G)
  (r2 : R2 → G) :
  G :=
    let l := And.left h
    let r := And.right h

    Or.elim l c1 c2


/-
example
  (h: (C1∨C2)∧(R1∨R2))
  (c1: C1→G)
  (c2: C2→G)
  (r1: R1→G)
  (r2: R2→G)
  : G :=
  And.elim h (fun l r => Or.elim l c1 c2)


--very odd we don't need r1 or r2

example
  (corp: C1∨C2)
  (vsvc: R1∨R2)
  (c1: C1→G)
  (c2: C2→G)
  (r1: R1→G)
  (r2: R2→G)
  : G :=
  Or.elim corp c1 c2
-/

--AXIOMS
def provable : Prop → Prop := sorry
def conj : Prop → Prop → Prop := sorry
axiom AxConjElimLeft : ∀ {x y : Prop}, provable (conj x y) → provable x
axiom AxConjElimRight : ∀ {x y : Prop}, provable (conj x y) → provable y
axiom AxConjIntro : ∀ {x y : Prop}, provable x → provable y → provable
(conj x y)
axiom AxNotPrFalse : provable False → False


--provable (conj x False)
--x∨False ?

--Sample Theorem 1
theorem explosion_example : ∀ x y, provable (conj x False) → provable y :=
sorry

--for all x and y, if it's provable that (x AND False) then it's provable that y
-- I would have written this as
-- ∃x ∀y, provable (conj x False) → provable y :=
theorem explosion_example2 : ∃x, provable (conj x False) → ∀y, provable y :=
sorry

theorem explosion_example3 : ∀x, provable (conj x False) → ∀y, provable y :=
sorry

theorem explosion_example4 (h: ∃x, provable (conj x False)) : (∀y, provable y) :=
  Exists.elim h
    (fun x pxandF =>
      let f := @AxConjElimRight x False pxandF
      fun y => False.elim (AxNotPrFalse f)
      )

sorry
