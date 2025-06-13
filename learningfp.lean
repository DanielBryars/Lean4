def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false


def a:Nat := 1

def b := isZero a

#eval b
