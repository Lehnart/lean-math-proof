variables (p q r : Prop)

-- commutativity of ∧ and ∨

example : p ∧ q ↔ q ∧ p := 
  iff.intro 
    (fun (h1 : p /\ q),
      have hp : p := and.left h1,
      have hq : q := and.right h1,
      show q /\ p ,from and.intro hq hp
    )

    (fun (h2 : q /\ p), 
      have hp : p := and.right h2,
      have hq : q := and.left h2,
      show p /\ q ,from and.intro hp hq
    )

variable (p_or_q : p ∨ q)
variable (q_or_p : q ∨ p)

example : p ∨ q ↔ q ∨ p := 
  iff.intro 
    (show p ∨ q -> q ∨ p ,from 
      fun h1 : p ∨ q ,
        or.elim
          p_or_q
          (fun hp : p ,show q ∨ p ,from or.intro_right q hp)
          (fun hq : q ,show q ∨ p ,from or.intro_left p hq)
    )
    (show q ∨ p -> p ∨ q ,from 
      fun h2 : q ∨ p ,
        or.elim 
          q_or_p
          (fun hq : q ,show p ∨ q ,from or.intro_right p hq)
          (fun hp : p ,show p ∨ q ,from or.intro_left q hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  iff.intro
    (show (p ∧ q) ∧ r -> p ∧ (q ∧ r) ,from 
      fun h1 : (p ∧ q) ∧ r ,
        have hp : p := and.left (and.left h1),
        have hq : q := and.right (and.left h1),
        have hr : r := and.right h1,
        and.intro hp (and.intro hq hr)
    )
    (show p ∧ (q ∧ r) -> (p ∧ q) ∧ r ,from 
      fun h1 : p ∧ (q ∧ r),
        have hp : p := and.left h1,
        have hq : q := and.left (and.right h1),
        have hr : r := and.right (and.right h1),
        and.intro (and.intro hp hq) hr
    )
    

variable (p_or_q_or_r : (p ∨ q) ∨ r)
variable (p_or_q_or_r2 : p ∨ (q ∨ r))
variable (q_or_r : q ∨ r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (show (p ∨ q) ∨ r -> p ∨ (q ∨ r) ,from 
      fun h1 : (p ∨ q) ∨ r ,
        or.elim
          p_or_q_or_r
          (fun h : (p ∨ q) , 
            or.elim
              p_or_q
              (fun hp : p , or.intro_left (q ∨ r) hp)
              (fun hq : q , or.intro_right p (or.intro_left r hq))
          )
          (fun hr : r , or.intro_right p (or.intro_right q hr) )
    )
    (show p ∨ (q ∨ r) -> (p ∨ q) ∨ r ,from 
      fun h1 : p ∨ (q ∨ r) ,
        or.elim
          p_or_q_or_r2
          (fun hp : p , or.intro_left r (or.intro_left q hp) )
          (fun h : (q ∨ r) , 
            or.elim
              q_or_r
              (fun hq : q , or.intro_left r (or.intro_right p hq))
              (fun hr : r , or.intro_right (p ∨ q) hr)
          )
    )
    

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  iff.intro
    (show p ∧ (q ∨ r) -> (p ∧ q) ∨ (p ∧ r) ,from
      (fun h : p ∧ (q ∨ r) , 
        have hp : p := and.left h,
        have hq_or_r : (q ∨ r) := and.right h,
        or.elim
          hq_or_r
          (fun hq : q , or.intro_left  (p /\ r) ( and.intro hp hq ) )
          (fun hr : r , or.intro_right (p /\ q) ( and.intro hp hr ) )
      )
    )
    (show (p ∧ q) ∨ (p ∧ r) -> p ∧ (q ∨ r) ,from
      (fun h : (p ∧ q) ∨ (p ∧ r) , 
        have hp : p := 
          or.elim
            h
            (fun h1 : (p ∧ q) , and.left h1)
            (fun h1 : (p ∧ r) , and.left h1),  
        have hq_or_r : q ∨ r := 
          or.elim 
            h 
            (fun h1: (p ∧ q) , or.intro_left r (and.right h1) )
            (fun h1: (p ∧ r) , or.intro_right q (and.right h1) ),
        and.intro hp hq_or_r
      )
    )
    
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  iff.intro 
  (show  p ∨ (q ∧ r) -> (p ∨ q) ∧ (p ∨ r) ,from 
    (fun h: p ∨ (q ∧ r) , 
      or.elim
        h 
        (fun hp : p , and.intro (or.intro_left q hp) (or.intro_left r hp) )
        (fun hq_and_r : q /\ r , and.intro (or.intro_right p (and.left hq_and_r) ) (or.intro_right p (and.right hq_and_r) ))
    )
  )
  (show  (p ∨ q) ∧ (p ∨ r) -> p ∨ (q ∧ r) ,from 
    (fun h : (p ∨ q) ∧ (p ∨ r) ,
      have hp_or_q : p ∨ q := h.left,
      have hp_or_r : p ∨ r := h.right,
      or.elim 
        hp_or_q
        (fun hp: p , or.intro_left (q /\ r) hp)
        (fun hq: q , 
          or.elim
            hp_or_r
            (fun hp: p , or.intro_left (q /\ r) hp)
            (fun hr: r , or.intro_right p (and.intro hq hr))
        )
    )
  )


-- other properties

example : (p → (q → r)) ↔ (p ∧ q → r) := 
  iff.intro
  (show (p → (q → r)) -> (p ∧ q → r) ,from
    (fun h : (p → (q → r)) , 
      (fun hp_and_q : p ∧ q , 
        have hp : p := and.left hp_and_q,
        have hq : q := and.right hp_and_q,
        h hp hq 
      )
    )
  )
  (show (p ∧ q → r) -> (p → (q → r)) ,from
    (fun h : (p ∧ q → r) , 
      (fun hp : p , 
        (fun hq : q ,
          have hp_and_q : p /\ q := and.intro hp hq,
          h hp_and_q
        ) 
      )
    )
  )
  
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  iff.intro
  (show ((p ∨ q) → r) -> (p → r) ∧ (q → r) ,from
    (fun h : ((p ∨ q) → r) ,
      and.intro 
        (fun hp : p , h (or.intro_left q hp) )
        (fun hq : q , h (or.intro_right p hq) )
    )
  )
  (show (p → r) ∧ (q → r) -> ((p ∨ q) → r) ,from
    (fun h : (p → r) ∧ (q → r) ,
      (fun hp_or_q : (p ∨ q) , 
        or.elim
          hp_or_q
          (fun hp : p , (and.left h) hp )
          (fun hq : q , (and.right h) hq )
      )
    )
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  iff.intro 
  (show ¬(p ∨ q)  -> ¬p ∧ ¬q ,from
    (fun h : ¬(p ∨ q) , 
      and.intro 
      (fun hp : p , show false ,from h (or.intro_left q hp) )
      (fun hq : q , show false ,from h (or.intro_right p hq) ) 
    )
  )
  (show ¬p ∧ ¬q -> ¬(p ∨ q)  ,from
    (fun h : ¬p ∧ ¬q , 
      (fun hp_or_q : (p ∨ q) , show false ,from   
        or.elim 
          hp_or_q
          (fun hp : p , (and.left h) hp )
          (fun hq : q , (and.right h) hq )
      )
    )
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  (fun h : ¬p ∨ ¬q , 
    (fun hp_and_q : (p ∧ q) , show false ,from 
      or.elim
        h
        (fun hnp : ¬p , hnp (and.left hp_and_q) )
        (fun hnq : ¬q , hnq (and.right hp_and_q) )
    )
  )

example : ¬(p ∧ ¬p) := 
  (fun hp_and_not_p : (p ∧ ¬p) ,
    absurd (and.left hp_and_not_p)  (and.right hp_and_not_p)
  )

example : p ∧ ¬q → ¬(p → q) := 
  (fun hp_and_notq : (p ∧ ¬q) ,
      (fun( hp_give_q : p → q ) ,  
          show false ,from absurd (hp_give_q (and.left hp_and_notq)) (and.right hp_and_notq)
      )
  )

example : ¬p → (p → q) := 
  (fun hnotp : (¬p) , 
    (fun hp : p , 
      absurd hp hnotp
    )
  )

theorem not_disj_to_impl : (¬p ∨ q) → (p → q) := 
  (fun hnotp_or_q : (¬p ∨ q) , 
    (fun hp : p , 
      or.elim
        hnotp_or_q
        (fun hnp : ¬p  , absurd hp hnp  )
        (fun hq : q , hq )
    )
  )

example : p ∨ false ↔ p := 
  iff.intro
  (show p ∨ false -> p ,from
    (fun hp_or_false :  p ∨ false , 
      or.elim 
        hp_or_false
        (fun hp : p , hp )
        false.elim
    )
  )
  (show p -> p ∨ false ,from
    (fun hp : p , 
      or.intro_left false hp 
    )
  )

example : p ∧ false ↔ false := 
  iff.intro
  (show p ∧ false -> false ,from
    (fun hp_and_false : p /\ false , and.right hp_and_false )
  )
  (show false -> p ∧ false , from false.elim )

open classical

example : (p → q) → (¬q → ¬p) := 
  (fun h : p -> q , 
    (fun hnq : ¬q , 
      or.elim
      (em p)
      (fun hp : p , absurd (h hp) (hnq) )
      (fun hnp : ¬ p , hnp )
    )
  )


theorem dne {p : Prop} (h : ¬¬p) : p :=
  by_cases
    (fun h1 : p , h1)
    (fun h1 : ¬p , absurd h1 h)

theorem dist_neg_over_or {p q :Prop} : ¬(p ∨ q) -> ( ¬p /\ ¬q ) := 
  ( fun h : ¬(p ∨ q) , 
    have hnp : ¬p := 
      or.elim 
        (em p)
        (fun hp : p , absurd (or.intro_left q hp) h) 
        (fun hnp :¬p , hnp ),
    have hnq : ¬q := 
      or.elim 
        (em q)
        (fun hq : q , absurd (or.intro_right p hq) h) 
        (fun hnq :¬q , hnq ),
    and.intro hnp hnq
  )

theorem dist_neg_over_and {p q :Prop} : ¬(p /\ q) -> ( ¬p ∨ ¬q ) := 
  ( fun h : ¬(p /\ q) , 
    or.elim 
    (em ( ¬p ∨ ¬q ))
    (fun h1 : ( ¬p ∨ ¬q ) , h1)
    (fun h2 : ¬( ¬p ∨ ¬q ) , 
      have h3 : ¬¬p /\ ¬¬q := dist_neg_over_or h2,
      have hp : p := dne h3.left,
      have hq : q := dne h3.right, 
      absurd (and.intro hp hq) h
    )
  )


example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  (fun h : ¬(p ∧ q) , 
    or.elim 
      (em (¬p ∨ ¬q) )
      (fun h1 :(¬p ∨ ¬q) , h1 )
      (fun h2 :¬(¬p ∨ ¬q) , 
        have h3 : ¬¬p /\ ¬¬q := dist_neg_over_or h2, 
        have hp : p := dne (and.left h3 ),
        have hq : q := dne (and.right h3),
        have hpandq : p /\ q := and.intro hp hq,
        absurd hpandq h
      ) 
  )


theorem not_cunj_to_impl {p q : Prop} : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) ,
  fun hp : p ,
  show q ,from
    or.elim (em q)
      (fun hq : q , hq)
      (fun hnq : ¬q , absurd (and.intro hp hnq) h)

theorem not_impl_to_cunj {p q : Prop} : ¬(p → q) → p ∧ ¬q := 
  (fun h: ¬(p → q) , 
    or.elim 
      (em (p ∧ ¬q))
      (fun h1: (p ∧ ¬q) , h1)
      (fun h2: ¬(p ∧ ¬q) , 
        absurd (not_cunj_to_impl h2) h
      )
  )

example : (p → q) → (¬p ∨ q) := 
  (fun h : p → q , 
    or.elim 
      (em (¬p ∨ q))
      (fun h1 : (¬p ∨ q) , h1 )
      (fun h2 : ¬(¬p ∨ q) , 
        have hp : p := dne (and.left (dist_neg_over_or h2)),
        have hnq : ¬q := and.right (dist_neg_over_or h2),
        absurd (h hp) hnq 
      )
  )

example : (¬q → ¬p) → (p → q) := 
  (fun h : (¬q → ¬p) , 
    (fun hp : p ,
      or.elim 
        (em q)
        (fun hq : q , hq)
        (fun hnq : ¬q , absurd hp (h hnq))
    )
  )


example : p ∨ ¬p := 
  or.elim 
    (em  (p ∨ ¬p))
    (fun h : p ∨ ¬p , h )
    (fun h1 :  ¬(p ∨ ¬p) , 
      
      have hp : p := dne ( and.right (dist_neg_over_or h1)  ),
      have hnp : ¬p :=  and.left (dist_neg_over_or h1),
      absurd hp hnp 
    ) 

theorem fact_neg_over_and {p q :Prop} :  ( ¬p /\ ¬q ) -> ¬(p ∨ q) := 
  (fun h1 : ( ¬p /\ ¬q ) , 
    or.elim 
      (em (p ∨ q) )
      (fun h : (p ∨ q) , 
        or.elim
          h 
          (fun hp : p , absurd hp (and.left h1))
          (fun hq : q , absurd hq (and.right h1)) 
      )
      (fun h : ¬(p ∨ q) , h)
  )

variable s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h : (p → r ∨ s) , 
    or.elim
      (em ((p → r) ∨ (p → s)))
      (fun h1: ((p → r) ∨ (p → s)) , h1)
      (fun h2: ¬((p → r) ∨ (p → s)) , 
        have h3 :  ¬(p → r) /\ ¬(p → s) := (dist_neg_over_or h2),
        have h4 : p /\ ¬r := not_impl_to_cunj (and.left h3),
        have hp : p := and.left h4,
        have hnr : ¬r := and.right h4,
        have hns : ¬s := and.right (not_impl_to_cunj (and.right h3)),
        have hnr_and_ns : ¬r /\ ¬s := and.intro hnr hns,
        have hn_r_or_s : ¬(r ∨ s)  := fact_neg_over_and hnr_and_ns,
        absurd (h hp) hn_r_or_s
      )
