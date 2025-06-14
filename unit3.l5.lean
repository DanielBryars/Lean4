
--5.1
def biggerThan : Nat-> Nat -> Prop := fun n l => n > l
def mybiggerThan42 : Nat -> Prop := biggerThan 42
def biggerThan42 : Nat -> Prop := fun n => n > 42

--5.1.1
--∀ (universal) elimination
example
  (P : α → Prop) -- P is a predicate on α
  (pf: ∀ x : α, P x) -- pf, proof that for ALL x of type alpha, P holds
  (a : α) -- a is of type alpha
  : P a --Pa is true
  := pf a -- apply "for all x it's true to a"

-- ∀ (universal) introduction
--example (P : α → Prop) (f : (a: α) → P a) : ∀ x : α, P x := f

inductive Spot where
    | white
    | black

open Spot

def loops ( s1 s2 : Spot) : Prop :=
    match (s1,s2) with
        | (white, white) => True
        | (white, black) => False
        | (black, black) => True
        | (black, white) => False

--changing color is not allowed :)
def reln2 ( s1 s2 : Spot) : Prop :=
        match (s1,s2) with
            | (white, white) => True
            | (white, black) => False
            | (black, black) => False
            | (black, white) => True

--lets prove reflexivenss
example : (∀ s:Spot, loops s s) :=
  fun s:Spot =>
    match s with
     | black => True.intro
     | white => True.intro

/-
example : (∀ s: Spot, reln2 s s) :=
        fun s: Spot =>
            match s with
            | black => True.intro
            | white => True.intro
-/
variable (P Q : α → Prop)

example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
    fun allpORallq: (∀ x, P x) ∨ (∀ x, Q x) =>
        Or.elim allpORallq
            (fun allp: ∀ x, P x => fun xa: α => Or.intro_left (Q xa) (allp xa))
            (fun allq: ∀ x, Q x => fun xa: α => Or.intro_right (P xa) (allq xa))


--5.1.2 Existential Introduction and Elimination
--Given P : α -> Prop
-- prove ∃ x : α, P x

--give an element a : α
-- give a proof that a has property P ie P a
--5.1.2
example (P : α →  Prop) (a : α ) (hpa : P a) : (∃ x : α, P x ) :=
      ⟨a , hpa ⟩

example (P : α →  Prop) (a : α ) (hpa : P a) : (∃ x : α, P x ) :=
      Exists.intro a hpa

example (he : ∃ x, P x) (ha : ∀ y, P y → B) : B :=
    Exists.elim he ha

-- this is rubbish.
example (he : ∃ x, P x ∧ Q x)
        (ha : ∀ y, (P y ∧ Q y) -> (∃ x, Q x ∧ P x)) : ∃ x, Q x ∧ P x :=
            Exists.elim he ha

example (he : ∃ x, P x) (ha : ∀ y, P y → B) : B :=
    Exists.elim he ha

example (he : ∃ x, P x) (ha : ∀ y, P y → B) : B :=
    Exists.elim he (fun y py => ha y py)


/-
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
        (fun w =>
             fun hw : p w ∧ q w =>
                Exists.intro w (And.intro hw.right hw.left))
-/

variable (β: Type) (r: β → β → Prop)

example
  (trans: ∀ x y z, (r x y ∧ r y z) → r x z)
  (backforth: ∃ x y, r x y ∧ r y x)
: ∃ x, r x x :=
Exists.elim backforth
(fun w => fun hw: ∃ y, r w y ∧ r y w =>
    Exists.elim hw
    (fun w2 => fun hw2 : r w w2 ∧ r w2 w =>
    show ∃ x, r x x from Exists.intro w (trans w w2 w hw2) ))
