/-
What You Need to Do
• Translate a real-world AI or decision scenario into propositional logic.
• Not every scenario will state a goal explicitly; sometimes, you are expected to extract
the logical conclusion based on what is described. Look for clues in the scenario that
suggest what outcome or condition follows from the given facts or rules.
• Use rules like implication (→), conjunction (∧), and disjunction (∨) etc based on Unit
1 and Unit 2.
• Construct Lean-style reasoning based on natural deduction introduced in Unit 3.
• Include helpful comments that explain your logical thinking. These do not need to be
long, just enough to show what rule or reasoning you’re applying and why.
• You can use either term mode or tactic mode
• Scenarios can sometimes cover provable, and occasionally standard propositional
implication tasks. You should reason through them using logical syntax (→, ∧, ∨, ¬) as
overed in the module.
• While semantic entailment (⊨) is introduced in Unit 2 for better conceptual
understanding, it is not required in Lean or used in Assessment 1. All logical
reasoning in Lean should be expressed using implication (→) and assumptions.
• Use of both “fun” and “λ” is acceptable.
Sample Scenario

A student qualifies for a grant (g) if:
• They either won a competition (c1) or published a paper (c2).
• A verification is provided either by a supervisor (r1) or a committee (r2).
You are told:
• provable (disj c1 c2)
• provable (disj r1 r2)
• provable c1 → provable g, provable c2 → provable g
• provable r1 → provable g, provable r2 → provable g
The goal is to prove provable g

I read:
A student qualifies for a grant (g) if:
• They either won a competition (c1) or published a paper (c2).
• A verification is provided either by a supervisor (r1) or a committee (r2).

As saying
∀e:students((c1 OR c2) AND (r1 OR r2) --> g)


-/


opaque provable : Prop → Prop
opaque disj : Prop → Prop → Prop

variable (c1 c2 r1 r2 g :Prop)

axiom h1 : provable (disj c1 c2)

#print h1
