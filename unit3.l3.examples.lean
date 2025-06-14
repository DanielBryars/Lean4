variable (A B C : Prop)
variable (R S : Prop)

--Example 1

  --assume R, show that this is a contradiction
  --assume ¬R - we have it already

--R→S, S→¬R ⊢¬R
example (pfRimpS :R→S) (pfSimpNotR:S→¬R) : ¬R :=
  fun proofOfR : R =>                         --Assume R
    have pfS : S := pfRimpS proofOfR          --Then we get S
    have pfNotR : ¬R := pfSimpNotR pfS        --From S we get ¬R
    show False from pfNotR proofOfR           --so we have ¬R and R and so R leads to a contradiction, hence ¬R (or asserting R leads to false R->False)


--Example 3 distributive
--(A ∧ B)∨ C) ⊢ (A ∨ C) ∧ (B ∨ C)
--Assume C then
--Introduce OR A ∨ C
--Introduce OR B ∨ C
--Introduce AND

--assume (A ∧ B)
--elim AND l get A
--elim AND r get B
--intro OR (A ∨ C)
--intro OR (B ∨ C)
--Introduce AND
--DONE

theorem dist (pfAandBorC: (A ∧ B)∨ C) : (A ∨ C) ∧ (B ∨ C) :=
    Or.elim pfAandBorC        -- two cases depending on whether
                              -- we've got a proof of A ∧ B or a proof of C
        (fun pfAandB: A ∧ B =>
            And.intro (Or.intro_left C (And.left pfAandB))
                      (Or.intro_left C (And.right pfAandB)))
        (fun pfC : C =>
            And.intro (Or.intro_right A pfC) (Or.intro_right B pfC)   )

--Example 4
--A,¬A ⊢ B
example (a:A) (notA:¬A): B := absurd a notA

--Example 5
-- A∨B, ¬A ⊢ B
-- Yeah so we're saying A or B holds and A doesn't hold so it MUST be B that holds.
-- in a constructive proof let's look at A∨B
-- if we assume A then we can also use ¬A get a contradiction and then claim B
-- if we assume B then well we already have B, happy days.
example (aorb:A∨B) (notA:¬A) : B :=
  Or.elim aorb
    (fun a:A => absurd a notA)
    (fun b:B => b)

--Example 6
-- A→B,¬B ⊢ ¬A
--okay so here is we assume A we get B and !B which leads to a contradiction which means we
--discharge A - it can't be right and so must be ¬A
example (aimpb: A→B) (notB:¬B) : ¬A :=
  fun (a:A) => --assume A
    absurd (aimpb a) notB

example (aTob: A → B) (notB: ¬ B) : ¬ A :=
  fun a: A => notB (aTob a)

--Example 7
-- ¬(A∨B) ⊢ ¬A
-- if we assume A then we get False which is the same as A->False
example (notaorb:¬(A∨B)) : ¬A :=
  fun (a:A) => --assume A
    let aorb := Or.intro_left B a --introduce A∨B
    absurd aorb notaorb

example (neither: ¬(A ∨ B)): ¬ A :=
  fun a: A => neither (Or.intro_left B a)

--Example 8
--¬(A∨B) ⊢ ¬B
example (neither: ¬(A ∨ B)): ¬B :=
  fun b:B =>
    let aorB := Or.intro_right A b
    neither aorB

--Example 9 - ignore needs classical

--Example 10
-- A  ⊢ ¬¬A
-- A holds, so we can assert that "A->False" is itself a contradiction
-- ie A means ¬ (¬A) or (¬A)->False
-- (A->False)->False
example (a:A) : ¬¬A :=
  fun(notA:¬A) => notA a

--AHHH so assuming notA leads to a contradiction, and so notA cannot be correct, it must me not notA

