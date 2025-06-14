variable (α : Type) (P Q : α → Prop)
--alpha is a Type
--P and Q are predicates

--5.4.1 Exercise
--∀x(P (x)→Q(x)) ⊢ ∀x(¬P (x)→¬Q(x))

example  (ipq : ∀ x, (P x → Q x)) : ∀ x, (¬ Q x → ¬ P x) :=
  fun x : α => -- assume a (for all a)
    fun nqa : ¬Q x => -- Q does not hold
      fun pa : P x => -- P does hold
      have qa: Q x := ipq x pa -- apply ipq
      absurd qa nqa -- nqa doesn't hold so it can't be true

--5.4.2 Exercise
--if there ∃x where Px ∧ Qx hold then ∃x an Px that holds
--So I need to use And elim, should be straight forward.

example (h: ∃x, (P x ∧ Q x)) : ∃x, P x :=
  Exists.elim h
  (fun w => fun hw: P w ∧ Q w => Exists.intro w (And.left hw))


example (h: ∃x, (P x ∧ Q x)) : ∃x, P x :=
  Exists.elim h
  (fun x hpxqx => Exists.intro x (And.left hpxqx))

--exercise 5.4.3
-- if for all x either P x does not hold or Q x does not hold (or neither hold)
-- then if there exists an x with P then there exists a y without Q
--
-- so I need to show that we
example (h: ∀ x, (¬ P x ∨ ¬ Q x)) : (∃ x, P x) → (∃ y, ¬ Q y) :=
fun wp: ∃ x, P x =>
    Exists.elim wp
    (fun w => fun hw: P w =>
    have wnpnq: ¬ P w ∨ ¬ Q w := h w
    have nqw : ¬ Q w  :=
        Or.elim wnpnq
        (fun wnp : ¬ P w => absurd hw wnp)
        (fun wnq : ¬ Q w => wnq)
    show (∃ y, ¬ Q y) from Exists.intro w nqw
    )

--That is very tricky.

