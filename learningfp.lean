def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false


def a:Nat := 1

def b := isZero a

#eval b


--#print Or.elim
--example (c:A∨B) (a:A) : A := a
--example (c:¬A) (a:A) : A := a

