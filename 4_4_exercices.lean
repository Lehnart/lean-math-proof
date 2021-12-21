open classical

variable (α : Type) 
variables (p q : α → Prop)

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) ↔ (∀ x : α, p x) ∧ (∀ x : α, q x) :=
  iff.intro 
  (fun h : ∀ x : α, p x ∧ q x ,
    and.intro 
      (fun z : α , show p z ,from and.left (h z)) 
      (fun z : α , show q z ,from and.right (h z))
  )
  (fun h : (∀ x : α, p x) ∧ (∀ x : α, q x) ,
    (fun z : α , 
      and.intro ( and.left h z ) ( and.right h z)
    )
  )
  
example : (∀ x: α, p x → q x) → (∀ x: α, p x) → (∀ x: α, q x) := 
  (fun h1 : ∀ x: α, p x → q x , 
    (fun h2 : ∀ x: α, p x ,
      (fun z: α ,  h1 z (h2 z) 
      ) 
    )
  )


example : (∀ x : α, p x) ∨ (∀ x : α, q x) → ∀ x : α, p x ∨ q x := 
  (fun h :(∀ x : α, p x) ∨ (∀ x : α, q x) ,
    or.elim
      h
      (fun h1 : (∀ x : α, p x) , (fun z : α , or.intro_left (q z) (h1 z) ) ) 
      (fun h2 : (∀ x : α, q x) , (fun z : α , or.intro_right (p z) (h2 z) ) )
  )

variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry