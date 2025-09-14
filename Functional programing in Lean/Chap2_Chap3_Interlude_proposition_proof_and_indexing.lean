-- proof can be done using rfl
example : 2 + 3 = 5 := rfl (a := 2+3)
example : 15 - 8 = 7 := rfl
example : "Hello, ".append "world" = "Hello, world" := rfl
example : 2 * 3 = 6 := by decide

def accessFive (l : List Nat) (ok : l.length >= 5) : Nat :=
  let h : Fin l.length := Fin.mk 4 ok
  l.get h
