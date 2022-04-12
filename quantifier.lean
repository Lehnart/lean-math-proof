open classical

variable (r : Prop)
variable (α : Type) 
variables (p q : α → Prop)
variable a : α
variable w : α

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

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  iff.intro
    (fun h : (∃ x, p x ∨ q x),
      exists.elim
        h
        (fun w,
          (fun hw : (p w ∨ q w),
            or.elim
              hw
              (fun hpw : (p w),
                have hepx : (∃ x, p x) := exists.intro w hpw,
                or.intro_left (∃ x, q x) hepx 
              )
              (fun hqw : (q w),
                have heqx : (∃ x, q x) := exists.intro w hqw,
                or.intro_right (∃ x, p x) heqx 
              )
          ) 
        )
    )
    (fun h : (∃ x, p x) ∨ (∃ x, q x),
      or.elim
        h 
        (fun hpx : (∃ x, p x),
          exists.elim 
            hpx 
            (fun w,
              (fun hw : p w,
                have h_pw_or_qw : (p w) ∨ (q w) := or.intro_left (q w) hw,
                exists.intro 
                  w
                  h_pw_or_qw
              )
            )
        )    
        (fun hqx : (∃ x, q x),
          exists.elim 
            hqx 
            (fun w,
              (fun hw : q w,
                have h_pw_or_qw : (p w) ∨ (q w) := or.intro_right (p w) hw,
                exists.intro 
                  w
                  h_pw_or_qw
              )
            )
        )    
    )


theorem forall_px_eq_not_exist_not_px  {α : Type} {p : α → Prop} : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  iff.intro
    (fun h : (∀ x, p x),
      ( fun hx : (∃ x, ¬ p x),
        exists.elim
          hx
          (fun w,
            have hpw : p w := h w,
            (fun hw :  ¬ (p w),
              absurd hpw hw
            )
          )
      )
    )
    (fun h : ¬ (∃ x, ¬ p x),
      (fun z : α,
        by_contradiction
          (fun hnpz : ¬ p z,
            absurd 
              (exists.intro z hnpz)
              h
          )
      )
    )

theorem not_exists_p_x_imp_forall_not_p_x {α : Type} {p : α → Prop} :  ¬ (∃ x, p x) -> (∀ x, ¬ p x) := 
  (fun h : ¬ (∃ x, p x),
    (fun z,
      (fun hpz : p z,
        have h3 :  (∃ x, p x) := 
          exists.intro 
            z
            hpz,
        h h3 
      )
    )
  )

theorem dne {p : Prop} (h : ¬¬p) : p :=
  by_cases
    (fun h1 : p , h1)
    (fun h1 : ¬p , absurd h1 h)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  iff.intro
  (fun h: (∃ x, p x) ,
      by_contradiction
        (fun h2 : ¬¬ (∀ x, ¬ p x),
          have h1 : (∀ x, ¬ p x) := dne h2,
          exists.elim
            h
            (fun w,
              (fun hw : (p w),
                absurd hw (h1 w)
              )
            )
        )
  )
  (fun h : ¬ (∀ x, ¬ p x),
    by_contradiction
      (fun h1:  ¬ (∃ x, p x),
        have h2 : (∀ x, ¬ p x) := not_exists_p_x_imp_forall_not_p_x h1, 
        absurd h2 h
      )
  )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (fun h : ¬ ∃ x, p x,
        not_exists_p_x_imp_forall_not_p_x h
    )
    (fun h : ∀ x, ¬ p x,
        (fun h2 : ∃ x, p x,
          exists.elim
            h2
            (fun w,
              (fun hw: p w,
                absurd hw (h w)
              )
            )
        )
    )

theorem not_forall_iff_not_exists {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (fun h : ¬ ∀ x, p x,
      by_contradiction
        (fun h_tofalsify : ¬ (∃ x, ¬ p x),
          have h2 : ∀ x, p x := (iff.elim_right forall_px_eq_not_exist_not_px) h_tofalsify,
          absurd h2 h
        )
      )
    (fun h : ∃ x, ¬ p x,
        exists.elim
          h 
          (fun w ,
            (fun hnw :  ¬ p w,
              (fun  hallp : ∀ x, p x,
                absurd (hallp w) hnw
              )
            )
          )
    )


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    (fun h : (∀ x, p x → r),
      (fun h2 : ∃ x, p x,
        exists.elim 
          h2 
          (fun w,
            (fun hw: p w,
              (h w) hw
            )
          )
      )
    )
    (fun h : (∃ x, p x) → r,
      (fun z : α,
        (fun hpz : p z,
          h(
            exists.intro 
            z 
            hpz 
          )
        )
      )
    )

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (fun h : ∃ x, p x → r,
        exists.elim
          h 
          (fun w ,
            (fun hw : p w → r,
              (fun h2 : ∀ x, p x,
                hw (h2 w)
              ) 
            )
          )
    )
    (fun h : (∀ x, p x) → r,
      by_cases
        (fun h1 : (∀ x, p x),
          have hr : r := h h1,
          exists.intro
            a
            (fun hp : p a,
              hr
            )
        )
        (fun hn1 : ¬ (∀ x, p x),
          have h3 : (∃ x, ¬ p x) := (iff.elim_left not_forall_iff_not_exists) hn1,
          exists.elim 
            h3 
            (fun w ,
              (fun hw : ¬ p w,
                exists.intro
                  w 
                  (fun hpw : p w,
                    absurd hpw hw
                  )
              )
            )
        )
    )


example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (fun h : (∃ x, r → p x),
        exists.elim
          h 
          (fun w,
            (fun hw : r -> p w ,
              (fun hr : r,
                exists.intro
                  w
                  (hw hr)
              )
            )
          )
    )
    (fun h : (r → ∃ x, p x),
      by_cases
        (fun hr : r,
          have h2 : ∃ x, p x := h hr,
          exists.elim 
            h2
            (fun w,
              (fun hw : p w,
                exists.intro
                  w
                  (fun hr : r, hw)
              )
            )
        )
        (fun hnr : ¬ r,
          exists.intro
            a
            (fun hr : r,
              absurd hr hnr
            )
        )
    )        