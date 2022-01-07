inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

#check @mynat.rec_on

namespace mynat

def add (m n : mynat) : mynat :=
  mynat.rec_on 
    n 
    m 
    (fun (n add_m_n : mynat), mynat.succ add_m_n)

#reduce add (succ zero) (succ (succ zero))

instance : has_zero mynat := has_zero.mk zero
instance : has_add mynat := has_add.mk add

theorem add_zero (m : mynat) : m + 0 = m := 
  rfl

theorem add_succ (m n : mynat) : m + succ n = succ (m + n) := 
  rfl

end mynat



