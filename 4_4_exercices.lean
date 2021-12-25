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

example : α → ( (∀ x : α, r) ↔ r) :=
  (fun a : α ,
    show (∀ x : α, r) ↔ r, from
    iff.intro
        (fun h1 : (∀ x : α, r),
            show r, from
            h1 a
        )
        (fun h2 : r,
            show (∀ x : α, r), from
            (fun b : α, h2)
        )
  )

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (fun h : (∀ x, p x ∨ r),
      or.elim 
        (em r)
        (fun hr : r,
          or.intro_right (∀ x, p x) hr
        )
        (fun hnr : ¬r,
          have h2 : (∀ z, p z) :=
            (fun z : α, 
            have h1 : (p z ∨ r) := (h z),
            or.elim 
              h1
              (fun hpz : (p z), hpz)
              (fun hr : r, absurd hr hnr)
            ),
          or.intro_left r h2
        )
    )
    (fun h : (∀ x, p x) ∨ r,
        (fun z : α,
          or.elim 
            h
            (fun hl : (∀ x, p x), or.intro_left r (hl z))
            (fun hr : r, or.intro_right (p z) hr)
        )
    )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  iff.intro
      (fun h : (∀ x, r → p x),
        (fun hr : r, 
          (fun z : α,
            (h z) hr
          )
        )
      )
      (fun h : r → ∀ x, p x,
        (fun z : α,
          (fun hr : r, 
            h hr z
          )
        )
      )
    
example : (∃ x : α, r) → r := 
  (fun h : (∃ x : α, r),
    exists.elim 
      h
      (fun w : α,
        (fun hr : r,
          hr 
        )
      )
  )
  
variable a : α
variable w : α

example : r → (∃ x : α, r) := 
  (fun hr : r,
    exists.intro a hr
  )

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  iff.intro
    (fun h :(∃ x, p x ∧ r),
      exists.elim
        h
        (fun w, 
          (fun hw : (p w ∧ r),
            have hr : r :=  and.right hw,
            have hl : (∃ x, p x) := exists.intro w (and.left hw),
            and.intro hl hr
          )
        )
    )
    (fun h : ((∃ x, p x) ∧ r),
      exists.elim 
        (and.left h)
        (fun w,
          (fun hw: (p w),
            exists.intro w (and.intro hw (and.right h))
          )
        )
    )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry