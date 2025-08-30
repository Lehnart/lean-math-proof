-- definition of max and max3 functions
def max {α : Type} [β : LT α] [DecidableRel (@LT.lt α β)] (a b : α) : α :=
  if a < b  then a else b

def max3 {α : Type} [β : LT α] [DecidableRel (@LT.lt α β)] (a b c : α) : α :=
  max (max a b) c

-- definition of abs function
def abs {α : Type} [Zero α] [Neg α] [LT α] [DecidableRel (@LT.lt α _)] (a : α) : α :=
  if a < 0 then -a else a
