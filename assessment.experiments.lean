opaque conj : Prop -> Prop -> Prop
opaque provable : Prop -> Prop
axiom AxConjElimRight : ∀ x y, provable (conj x y) -> provable y
axiom AxConjElimLeft : ∀ x y, provable (conj x y) -> provable x
axiom AxConjElimLeft2 : ∀ {x y : Prop}, provable (conj x y) → provable x
axiom AxConjIntro : ∀ x y, provable x -> provable y -> provable (conj x y)
axiom AxPrTrue   : provable True
axiom AxNotPrFalse : provable False -> False

example : provable True :=
  AxPrTrue

example
  (x y : Prop) (hx : provable x) (hy : provable y)
  : provable (conj x y) :=
    AxConjIntro x y hx hy

example (x y : Prop) (h : provable (conj x y)) : provable x :=
  AxConjElimLeft x y h

example (h : provable (conj x y)) : provable x :=
  AxConjElimLeft2 h

example (x y : Prop) (h : provable (conj x y)) : provable y :=
  AxConjElimRight x y h

example (x y : Prop) (h : provable (conj x False)) : provable y :=
  let pfFalse:= AxConjElimRight x False h
  let boom := AxNotPrFalse pfFalse
  False.elim boom

/-
Goal:
Given a proof of provable (conj x (conj y z)),
prove provable (conj (conj y x) z)

My thoughts:
So we're saying given a proof of
x∧(y∧z)
prove that it's the same as
(y∧x)∧z
ie proving and ∧ is commutative (well at least in this example)

Strategy:
pull the left and right using the axioms until we have everything seperated
introduce the conj again using the components in the order we want
-/
example (x y z : Prop) (h : provable (conj x (conj y z))) :
  provable (conj (conj y x) z) :=
  --Decompose to all the components
  let h_x := AxConjElimLeft x (conj y z) h
  let h_conjyz := AxConjElimRight x (conj y z) h
  let h_y := AxConjElimLeft y z h_conjyz
  let h_z := AxConjElimRight y z h_conjyz
  --build up what we want
  let h_conjyx := AxConjIntro y x h_y h_x
  AxConjIntro (conj y x) z h_conjyx h_z
