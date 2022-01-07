example (x y : nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) :=
  calc 
     2 * y = 2 * (x + 7) : congr_arg (nat.mul 2) h

example (a b : nat) (h : nat.succ a = b) : nat.succ( nat.succ(a)) = nat.succ(b) :=
  calc 
    nat.succ( nat.succ(a)) = nat.succ(b)  : congr_arg nat.succ h

example (a : nat) : a + nat.succ(0) = nat.succ(a) :=
  calc 
    a + nat.succ(0) = nat.succ(a) : rfl

example (a : nat) : 0 + a = a :=
  calc 
     0 + a = 0 + a : rfl
     ...   = a + 0 : nat.add_comm 0 a
     ...   = a : rfl