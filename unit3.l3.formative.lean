variable (A B C : Prop)
--1
--trivial
example : A → A := fun(a:A) => a

--2
--Given B we can derive A->B yeah because it is vacuously true if A is false
theorem const (b : B) : A → B :=
  fun _:A => b

--const
#print const
--∀ (A B : Prop), B → A → B

--3

example  : B → (A → B) := const A B
example (b : B) :  A → B := (const A B) b


--4.1

--  A→B ⊢ ¬B→¬A
--assume ¬A derive B from aTob (this vacuously true)
example (aTob : A → B) : ¬ B → ¬ A :=
  fun(notB:¬B)=> --assume not B
    fun(a:A)=> --assume A
      let b := aTob a --apply a to b to get B
      absurd b notB -- we have a contradiction so A cannot be !A

--5
--(A → B) → A) ⊢ B → A

example (aImpbImpa: (A → B) → A) : B → A :=
  fun(notB:¬B)=> --assume B isn't true
    fun(a:A)=> --assume A is true
      
