-- Test stack Overflow with recursive sum
def sum (l : List Nat) : Nat :=
  match l with
  | List.nil => 0
  | List.cons x xs => x + sum xs

#eval sum (List.range 1000) -- stack overflow at 10000

-- Test no stack overflow with tail recursive
def sum_wo_so (initial_value : Nat) (l : List Nat) : Nat :=
  match l with
  | List.nil => initial_value
  | List.cons x xs => sum_wo_so (initial_value + x) xs

#eval sum_wo_so 0 (List.range 10000) -- no stack overflow

-- formulate sum and product as accumulate

def accumulate (f : Nat → Nat → Nat) (initial_value : Nat) (l : List Nat) : Nat :=
  match l with
  | List.nil => initial_value
  | List.cons x xs => accumulate f (f x initial_value) xs

#eval accumulate (· + ·) 0 (List.range 10000)

-- write is prime function
def is_divisor (x y : Nat) : Bool :=
  x % y == 0

def is_prime (x : Nat) : Bool :=
  if x < 2 then false
  else
    List.range' 2 (x-2) |>.all (fun y => not (is_divisor x y))

#eval is_prime 997

-- write is prime with erathostene sieve
def fast_is_prime (x : Nat) : Bool :=
  if x < 2 then false
  else
    let rec sieve (divs : List Nat) : Bool :=
      match divs with
      | List.nil => true
      | List.cons prime ys =>
      if is_divisor x prime then false
      else if prime * prime > x then true
      else sieve (ys.filter (fun next_y => not (is_divisor next_y prime)))
    termination_by sizeOf (List Nat)
    decreasing_by sorry

    sieve (List.range' 2 x)

-- fibonnaci
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n+1) + fib (n)

#eval fib 6 -- will be too long with large values

def fast_fib (n : Nat) : Prod Nat Nat :=
  match n with
  | 0 => (0, 1)
  | 1 => (1, 1)
  | n + 2 =>
    let (fib_n2, fib_n1) := fast_fib (n+1)
    (fib_n1, fib_n1 + fib_n2)

#eval fast_fib 30
