-- let s define a type with only strictly positive numbers
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- Let s overload plus operation. class is used to define a type class
class Plus (α : Type) where
  plus : α → α → α

-- let s define the addition operation for Pos type
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

-- We can then make Pos an instance of the Plus type class
instance : Plus Pos where
  plus := Pos.plus

-- Add is a predefined type class in Lean
instance : Add Pos where
  add := Pos.plus

def seven : Pos := Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
def fourteen : Pos := seven + seven

-- We can also override toString for Pos
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

instance : ToString Pos where
  toString := posToString true

-- Nat can be overloaded
inductive LT4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three

-- Exercise 1
structure Positive where
  succ ::
    pred : Nat

instance : Add Positive where
  add p1 p2 := { pred := p1.pred + p2.pred }

instance : Mul Positive where
  mul p1 p2 := { pred := p1.pred * p2.pred }

instance : OfNat Positive n where
  ofNat := { pred := n }

instance : ToString Positive where
  toString p := s!"Positive {p.pred}"

def p : Positive := { pred := 5 }
#eval p + p * p

-- Exercise 2
inductive Even where
  | zero : Even
  | succ : Even → Even

def Even.plus (a b : Even): Even :=
  match a with
  | Even.zero => b
  | Even.succ n => Even.succ (n.plus b)

def Even.mul (a b : Even) : Even :=
  match a with
  | Even.zero => Even.zero
  | Even.succ n => b.plus (b.plus (n.mul b))

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.succ n => 2 + n.toNat

instance : Add Even where
  add p1 p2 := Even.plus p1 p2

instance : Mul Even where
  mul p1 p2 := Even.mul p1 p2

instance : ToString Even where
  toString p := toString (Even.toNat p)

def zero : Even := Even.zero
def two : Even := Even.succ Even.zero
def four : Even := Even.succ two

#eval zero
#eval two
#eval four
#eval two + two
#eval two + four
#eval two * two
#eval two * four * four

-- when type are not inferable, we can use @ so lean show the signature of the function and don t try to infer them
#check @IO.println
-- [ToString α] means that α must have an instance of ToString
