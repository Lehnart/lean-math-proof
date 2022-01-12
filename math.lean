universe u 


variable α : Type u

/- axiome d'extensionnalité -/
axiom set_ext (E F : set α) ( x : α ) : (∀x, ( E x ↔ F x )) → E = F

/- La réciproque découle de la définition de l'égalité -/
theorem set_ext_rec (E F : set α) ( x : α ) :  E = F → (∀x, ( E x ↔ F x )) :=
  (fun eq_E_F : (E = F) ,
    (fun x: α,
      iff.intro
        (fun h_x_in_E : E x,
          eq.rec h_x_in_E eq_E_F 
        )
        (fun h_x_in_F : F x,
          eq.rec h_x_in_F (eq.symm eq_E_F) 
        )
    )
  )

/- On peut toujours construire un ensemble vide -/
def empty_set : (set α) :=
  (fun (a:α), false)

/- On peut toujours construire un singleton à partir d'une variable -/
def singl {α}: (α -> set α) :=
  (fun (a:α), 
    (fun (b:α),
      a=b
    )
  )

example (a : α) : singl a a :=
  rfl

/- L'appartenance au singleton se réduit à l'égalité à l'élément du signleton -/
example (a x : α): singl a x -> a = x :=
  (fun h : singl a x,
    h
  )

/- On peut toujours construire un ensemble à partir d'une liste -/
def list_set {α}: (list α -> set α)
| list.nil        := empty_set α 
| (list.cons a l) := (fun x:α, (a=x) ∨ (list_set l x) )

/- 
  Definition de la notion de sous ensemble 
  s1 est un sous ensemble de s2 
-/
def subset {α} (s₁ s₂ : set α) :=
∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

example (E F : set α) : subset E F <-> ∀ ⦃a⦄, a ∈ E → a ∈ F :=
  iff.intro
    (fun h : subset E F, h)
    (fun h : ∀ ⦃a⦄, a ∈ E → a ∈ F, h)


/- Une condition suffisante pour qu'un singleton soit un sous ensemble de E est que l'élément appartienne à E -/
example (a : α) (E : set α) : E a -> (subset (singl a) E) :=
(fun h : E a,
  (fun x : α,
    (fun h_a_x : a = x ,
      eq.rec h h_a_x
    ) 
  )
)


