
--Three variables
variable (A B C : Prop)

-- *******************************************
--AND Rules
--introduction ∧I (A ∧ B)
example (a: A) (b: B) : A ∧ B := And.intro a b

--elimination ∧Rl ∧Er
example (c : A∧B) : A := And.left c
example (c : A∧B) : B := And.right c

-- *******************************************
--OR
--introduction
example (a : A) : A∨B := Or.intro_left B a
example (a:A) : A∨B:=Or.inl a --inferred type

example (b : B) : A∨B := Or.intro_right A b
example (b:B) : A∨B:=Or.inr b --inferred type
-- the proposition B→A∨B is the function which takes B and returns A∨B
example: B→A∨B := fun b:B => Or.inr b
--oh wow and so yeah you can do:
example: B→A∨B := Or.inr

--elminination
--so this is (A∨B)->C
example (d:A∨B) (caseA: A->C) (caseB: B->C) : C :=
  Or.elim d caseA caseB

-- *******************************************
-- IMPLIES
--elimination (MP)
example (a:A) (f: A→B) := f a

-- *******************************************
-- NEGATION and FALSE
--in constructive logic you can derive ANYthing from a contradiction
--this is reductio ad absurdium

example (a:A) (notA:¬A) : B := absurd a notA

-- ¬A means False
example(i:False) : A := False.elim i

--Note:
/-
An important feature of constructive logic is that there is
no way to produce a proof of A just from a proof of ¬¬A
for an arbitrary A
. So in Lean you cannot prove the proposition ((A -> False) -> False) -> A
  unless you explicitly say you want to use classical logic.
  We see how to use classical logic in Lean shortly.
-/

--Exercise

--find a particular A such that you can prove
--((A→False)→False)→A for that particular A
--write is as an example
-- A true
example : ((True → False)→ False)→True :=
  fun _ => True.intro

--Non prop proofs in lean
-- cannot prove (A∨¬A) ie a contradiction cannot hold
-- can prove ¬(A∨¬A) ie you can prove that a contradiction cannot be proved

-- (A ∧ (A→False)) → False
--is the same as
-- ¬(A ∧ (¬A))

example : (A ∧ (A→False)) → False ↔ ¬(A ∧ (¬A)) := by exact Iff.refl _

theorem nonContradiction (A: Prop): A ∧ (A→False) → False :=
  fun proofOfAandNotA : A ∧ (A→False) =>
    have proofOfA : A := And.left  proofOfAandNotA
    have proofOfAimpliesFalse: A → False := And.right proofOfAandNotA
    show False from proofOfAimpliesFalse proofOfA

theorem nonContradictionTerm (A : Prop) : A ∧ (A → False) → False :=
  fun h => (h.right) (h.left)

example : (A→False) → ¬A :=
  fun h: A→False => show ¬A from h

example : (A→False) → ¬A :=
  fun arg1 => arg1

example : (A→False) → ¬A :=
  id

example : ((A ∧ (A→False)) → False) → ¬(A ∧ (¬A)) := id

--double negative intro

theorem doubleNegIntro : A → ¬¬A :=
  fun a: A =>
    fun na: ¬A => show False from na a

example : A → ¬¬A := doubleNegIntro A
