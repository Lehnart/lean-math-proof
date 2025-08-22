import set

universe u 
variable α : Type u
variable β : Type u

/- Une application c'est une fonction, un ensemble de départ et un ensemble de fin -/
structure map (α : Type u) (β : Type u)  :=
  mk :: (A : set α) (B : set β) (f : α → β)

/- Deux fonctions sont égales si chaque image est égale-/
axiom map_eq {α} {β} (A : set α) (B : set β) (f : α → β) (g : α → β): (∀x:α, ( f x = g x ))

/- Application identité -/
def map_id (A : set α) := map.mk A A (fun x:α, x)

/- Application constante -/
def map_const (A : set α) (a : α) := map.mk A A (fun x:α, a) 

/- Application canonique -/
def map_canonic (A1 : set α) (A2 : set α) (h : subset A1 A2) := map.mk A1 A2 (fun x:α, x)

/- Restriction d'une application -/
def map_restriction (A : set α) (m : map α β) (h : subset A m.A) := map.mk A m.B m.f

