/- part 2 -/


/-
Part 2
Outline
In this problem, the individuals in the domain of first-order logic are propositional statements.
They belong to the type Prop in Lean 4. In each case you need to replace the word sorry with an actual proof. After each proof, you must provide an explanation of your logic behind the proof in Lean file.

You need to use the following:
-/

-- These are the "Shape" of our Proporsitions
--Define an function which takes to Props and returns a Prop
opaque conj : Prop -> Prop -> Prop
--Define a function which takes a Prop and returns a Prop
opaque provable : Prop -> Prop

--These axioms constrain what we can do with them, they basially define "AND"
--Now we define an axiom what says for all x y if the output of conj is not False, then y is True (this is the And.elim right rule)
axiom AxConjElimRight : ∀ x y, provable (conj x y) -> provable y

--Now we define an axiom what says for all x y if the output of conj is not False, then x is True (this is the And.elim left rule)
axiom AxConjElimLeft : ∀ x y, provable (conj x y) -> provable x

--This says if x is True and y is True then the output of conj x and y is true.
axiom AxConjIntro : ∀ x y, provable x -> provable y -> provable (conj x y)

--This is how we can introduce True
axiom AxPrTrue   : provable True

-- This says if False can be proved, it always leads to False (if a contradiction can be proved it leads to a contradiction)
axiom AxNotPrFalse : provable False -> False


-- Proofs

--Proving that conjunction with False is not provable; and that proving x does not lead to provable False
theorem ex1 : ∀ x, ¬ provable (conj x False) ∧ (provable x -> ¬ provable False) := sorry
--For all x, it'd (not provable that x AND False) AND (provable x -> it's not provable that it's False)



--From a contradiction (x ∧ False), anything follows (principle of explosion)

theorem ex2 : ∀ x y, provable (conj x False) -> provable y := sorry

--Rearranging nested conjunctions using provability

theorem ex3 : ∀ x y z, provable (conj x (conj y z)) -> provable (conj (conj y x) z) := sorry

--Using negation to infer missing provability

theorem ex4 : ∀ x y : Prop,

 ¬ provable (conj x y) ->

 provable x ->

 ¬ provable y := sorry
