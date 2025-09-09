example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun hx : ∀(x : α), p x ∧ q x =>  fun hy : α => (hx hy).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x => fun z : α => (h z).left

variable (α : Type) (r : α → α → Prop)
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

#check Eq.refl
#check Eq.symm
#check Eq.trans

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl (f a)

example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : 1 * a = a := Nat.one_mul a
example : a * 1 = a := Nat.mul_one a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

#check Nat.mul

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 := Nat.mul_add (x+y) x y
  have h2 := (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

variable (a b c d e : Nat)

theorem T (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d) : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e := Eq.symm h4

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, x > y :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w : α => fun hw : p w ∧ q w =>
     Exists.intro w ⟨ hw.right, hw.left ⟩
    )

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) : IsEven (a + b) :=
  Exists.elim
    h1
    (fun w1 (hw1 : a = 2 * w1) =>
      Exists.elim
        h2
        (fun w2 (hw2 : b = 2 * w2) =>
          Exists.intro
            (w1 + w2)
            (calc
              a+b = a + b := rfl
              _ = 2 * w1 + b := congrArg (. + b) hw1
              _ = 2 * w1 + 2 * w2 := congrArg (2*w1 + .) hw2
              _ = 2 * (w1 + w2) := (Nat.mul_add 2 w1 w2).symm
            )
        )
    )

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := fun h => Exists.elim h (fun _ : α => id)
example (a : α) : r → (∃ _ : α, r) := (fun hr => Exists.intro a hr)
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h => Exists.elim h (fun h_α : α =>  fun hp => And.intro (Exists.intro h_α hp.left) (hp.right)) )
    (fun h => Exists.elim h.left (fun h_α : α =>  fun hp => Exists.intro h_α ⟨hp, h.right⟩ ))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    ( fun h => Exists.elim h
      ( fun hα => fun hprop =>
          Or.elim
          hprop
          (fun hpa  : p hα => Or.intro_left  (∃ x, q x) (Exists.intro hα hpa))
          (fun hqa : q hα => Or.intro_right (∃ x, p x) (Exists.intro hα hqa))
      )
    )
    ( fun h =>
        Or.elim
          h
          (fun hp => Exists.elim hp (fun hα => fun hprop => Exists.intro hα (Or.intro_left  (q hα) hprop )))
          (fun hq => Exists.elim hq (fun hα => fun hprop => Exists.intro hα (Or.intro_right (p hα) hprop )))
    )

theorem myt1 {α : Type} {p : α → Prop }: (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    ( fun h => fun henp => Exists.elim henp (fun hα => fun hnp => hnp (h hα) ) )
    ( fun h => fun hα => byContradiction (fun hnp => h (Exists.intro hα hnp)) )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    ( fun h => fun hnp => Exists.elim h (fun hα => fun hp => (hnp hα) hp) )
    ( fun h => byContradiction (fun hn : ¬∃ x, p x => h (fun hα => fun hp : p hα => hn (Exists.intro hα hp))) )

theorem myth2 {α : Type} {p : α → Prop} : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    ( fun h => fun hα => (fun hnp => h ( Exists.intro hα hnp ) ) )
    ( fun h => fun hp => Exists.elim hp (fun hα => fun hphα => (h hα) hphα ) )

theorem myth3 {α : Type} {p : α → Prop} : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    ( fun h => byContradiction (fun henp => h (myt1.mpr henp) ) )
    ( fun h => fun hp => Exists.elim h (fun hα => fun hnpα => hnpα (hp hα) ))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h => (fun he => he.elim (fun hα => h hα )) )
    (fun h => (fun hα => fun hp : p hα => h (Exists.intro hα hp) ) )

theorem myth4 {α : Type} {r : Prop} {p : α → Prop} : ¬(∃ x, p x → r) → (∀x, p x) :=
  (fun hnex : ¬ ∃ x, p x → r =>
    have hap : ∀ x, p x := ( fun x => byContradiction (fun hnp : ¬ p x => hnex ⟨x, (fun hp => absurd hp hnp)⟩) )
    hap
  )

example (ha : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun h => fun hp => h.elim (fun hα => fun hpr => hpr (hp hα) ) )
    (fun h => byCases
      (fun hp : ∀ x, p x => Exists.intro ha (fun _ => h hp) )
      (fun hnp : ¬ (∀ x, p x) => byContradiction
        (fun hnex : ¬ ∃ x, p x → r => hnp (myth4 hnex))
      )
    )

theorem th5 {p q : Prop} : (p → q) → (¬p ∨ q) :=
  (fun hpq =>
    byCases
      ((.inr ∘ hpq) .)
      (.inl)
  )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun h => fun hr => h.elim (fun hα => fun hrp => Exists.intro hα (hrp hr) ) )
    (fun h => let h1 := th5 h;
      Or.elim h1
        (fun hor1 => Exists.intro a (fun hr => absurd hr hor1))
        (fun hor2 => Exists.intro hor2.choose (fun _ => hor2.choose_spec))
    )


variable (α : Type) (hx : α )(p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h => And.intro (fun hx => (h hx).left) (fun hx => (h hx).right))
    (fun h => And.elim (fun hpx => fun hqx => fun hx => And.intro (hpx hx) (hqx hx)) h)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  ( fun hpq : (∀ x, p x → q x) => fun hp :  (∀ x, p x) => fun hx : α => hpq hx (hp hx)  )

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun h => Or.elim
     h
    (fun hp => fun hx => Or.intro_left (q hx) (hp hx) )
    (fun hq => fun hx => Or.intro_right (p hx) (hq hx))
   )

example : α → ((∀ _ : α, r) ↔ r) :=
  (fun hα =>
    Iff.intro
      (fun h => h hα)
      (fun hr => (fun _ => hr))
  )

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h => byCases
    (fun hr : r => Or.inr hr )
    (fun hnr : ¬ r => Or.inl (fun hx => (h hx).elim (fun hpx => hpx) (fun hr => absurd hr hnr)))
  )
  (fun h => fun hx => Or.elim h (fun h1 => Or.intro_left r (h1 hx)) (fun h2 => Or.intro_right (p hx) (h2)) )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h => fun hr : r => fun hx => h hx hr)
    (fun h => fun hx => fun hr => h hr hx)
