-- To eval an expression, use `#eval` followed by the expression.
#eval 1 + 2
#eval 1 + 2 * 5

-- To apply function to its arguments, no parentheses are needed.
#eval String.append "Hello, " "World!"

-- When a function argument is the return value of another function, parentheses are needed?
#eval String.append (String.append "Hello" ", ") "World!"

-- there is only conditional expression in Lean, no conditional statements.
#eval String.append "it is " (if 1 > 2 then "yes" else "no")

-- any expression in lean must have a type to be evaluated.
#eval (1 - 2 : Nat)
#eval (1 - 2 : Int)

-- Type of an expression can be checked using `#check`.
#check 1 - 2
#check (1 - 2 : Int)

-- Definition in Lean are done using `def`.
def hello := "Hello, "
def world := "World!"
#eval String.append hello world

-- to define a function, use `def` followed by the function name, argument and return type.
def add1 (x : Nat) : Nat := x + 1
#eval add1 5

-- A function can have several arguments
def add (x : Nat) (y : Nat) : Nat := x + y
#eval add 5 6

-- When #check is used on a function, it shows the function signature. To have its type, we need to pass it in parentheses.
#check add
#check (add)

-- To define a type, you can use the Type type. Type are first class citizens in Lean so it is treated as everything else
def Str : Type := String

-- Structure can be defined using `structure` keyword. There are new types that are a composition of existing types
structure Point where
  x : Float
  y : Float
deriving Repr -- deriving Repr is used to automatically generate a string representation of the structure

-- To create a value from a structure, we can use {} syntax.
def p1 : Point := { x := 1.0, y := 2. }
#check p1
#eval p1

-- To access a element of a structure, we can use the dot notation.
#eval p1.x

-- To copy easily a structure, we can use the with syntax.
def p2 : Point := { p1 with x := 3.0 }
#eval p2

-- A constructor in lean is a function that takes data and assign them to the fields of a structure.
def p3 : Point := Point.mk 4.0 5.0
#eval p3

-- constructor can be overidden with :: syntax
structure Point2 where
  point ::
  x : Float
  y : Float

-- dot operator can be used call a multi argument function
#eval "Hello, ".append "World!" -- this is equivalent to String.append "Hello, " "World!"

-- Pattern matching is used to check which constructor was used to create a value
def isZero (x : Nat) : Bool :=
  match x with
  | Nat.zero => true
  | Nat.succ _ => false
#eval isZero 0
#eval isZero 1

-- Type can takes arguments. This is what we called polymorphism in Lean.
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOriginPoint : PPoint Nat :=  { x := Nat.zero, y := Nat.zero }
def floatOriginPoint : PPoint Float :=  { x := 0., y := 0. }

-- definition can also be polymorphic, meaning that they can take type arguments.
def replaceX (α : Type) (p : PPoint α) (x : α) : PPoint α := { p with x := x }

-- List is a datatype in Lean. A list can be declared with [] syntax.
def myList : List Nat := [1, 2, 3, 4]

-- We can also create a list using the constructors.
def myList2 : List Nat := List.cons 1 (List.cons 2 (List.cons 3 (List.cons 4 List.nil)))

-- Here is an example on a function taking list as argument :
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)
#eval length Nat myList2

-- When defining something, arguments can be given inside curly braces to say that they are implicit.
def implicitReplaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α := { point with x := newX }

-- Option data type can be used to represent a value that may or may not exist.
def optionalHead {α : Type} (l : List α) : Option α :=
  match l with
  | List.nil => none
  | List.cons x _ => some x
#eval optionalHead myList
#eval optionalHead (α := Nat) []

-- Prod can be used to represent a pair of values.
def pair : Prod Nat String := (1, "one")

-- Sum allow the choice between two generic values.
def either : Sum Nat String := Sum.inl 42

-- Unit is a type that has only one value, written as `()`. It is often used to represent a function that does not return anything meaningful.
def doNothing : Unit := ()

-- Empty is a type that has no values. It is used to represent a situation where no value can exist.
-- def empty : Empty := sorry

-- find last entry of a list
def lastEntry {α : Type} (l : List α) : Option α :=
  match l with
  | List.nil => none
  | List.cons x xs =>
      match xs with
      | List.nil => some x
      | _ => lastEntry xs
#eval lastEntry myList

-- find the first entry of a list that satisfies a predicate
def List.findFirst? {α : Type} (l : List α) (predicate : α -> Bool) : Option α :=
  match l with
  | List.nil => none
  | List.cons x xs => (if predicate x then some x else findFirst? xs predicate)

def isEven (n : Nat) : Bool := n % 2 == 0
#eval List.findFirst? myList isEven

-- funtion that switches the order of a pair
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (x, y) => (y, x)

-- function that combines two lists into a list of pairs
 def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | List.nil, _ => List.nil
  | _, List.nil => List.nil
  | List.cons x xs', List.cons y ys' => List.cons (x, y) (zip xs' ys')

-- example of taking n elements from a list
def take {α : Type} (n : Nat) (l : List α) : List α :=
  match n with
  | 0 => List.nil
  | 1 => match l with
        | List.nil => List.nil
        | List.cons x _ => List.cons x List.nil
  | _ => match l with
        | List.nil => List.nil
        | List.cons x xs => List.cons x (take (n - 1) xs)
#eval take 3 ["bolete", "oyster"]
#eval take 2 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]
#eval take 0 ["bolete", "oyster"]

-- Implicit arguments are not always necessary if they are mentioned in the function signature.
def lengthWithImplicit (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)
#eval lengthWithImplicit myList2

-- Function using pattern matching can be defined in a more concise way :
def lengthConcise : List α -> Nat
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (lengthConcise ys)
#eval lengthConcise myList2

-- intermediate result can be defined using `let` keyword
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)

-- anonymous functions can be defined using `fun` keyword
#check fun (x : Nat) => x + 1

-- anonymous functions can be even concise with (.) syntax
#check (. + 1)

-- Namespace can be used to group related definitions together.
namespace MyNamespace
def myTripleFunction (x : Nat) := x * 3
end MyNamespace

-- string interpolation can be used to create strings with variables
def name := "Alice"
def greeting := s!"Hello, {name}!"
#eval greeting
