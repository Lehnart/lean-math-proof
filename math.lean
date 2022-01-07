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

/- On peut toujours construire un singleton -/
def singleton_set : (α -> set α) :=
  (fun (a:α), 
    (fun (b:α),
      a=b
    )
  )

#check 
example 