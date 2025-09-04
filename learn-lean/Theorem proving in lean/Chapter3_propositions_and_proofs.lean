variable (p q : Prop)

example (h : p ∧ q) : q ∧ p := ⟨ h.right, h.left ⟩

example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
example (h : p ∨ q) : q ∨ p := h.elim (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq)

example (hpq : p → q) (hnq : ¬q) : ¬p := fun hp : p => hnq (hpq hp)
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp : q → p) : r := absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun hpq : p ∧ q => ⟨ hpq.right, hpq.left ⟩)
    (fun hqp : q ∧ p => ⟨ hqp.right, hqp.left ⟩)

variable (h : p ∧ q)
example : q ∧ p := (and_swap p q).mp h

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  And.intro hq hp

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

theorem em : (p ∨ ¬ p) :=
  let hpp : ¬¬(p ∨ ¬ p) :=
    (fun hp : ¬(p ∨ ¬ p) =>
      have not_p : ¬p := fun x: p => hp (Or.intro_left (¬p) x)
      have not_not_p  := fun x: ¬p => hp (Or.intro_right p x)
      not_not_p not_p
    )
  dne hpp

theorem not_p_and_not_p: ¬(p ∧ ¬p) := fun h : p ∧ ¬p => h.right h.left

theorem comm_and : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)

theorem comm_or : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq))
    (fun h : q ∨ p => Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))

theorem dist_and : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    ( fun h : p ∧ ( q ∨ r ) =>
      have hp : p := h.left
      have hqr : q ∨ r := h.right
      Or.elim hqr
        (fun hq : q => And.intro hp hq |> Or.inl)
        (fun hr : r => And.intro hp hr |> Or.inr)
    )
    ( fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
      (fun hpq : p ∧ q => And.intro hpq.left (Or.intro_left r hpq.right))
      (fun hpr : p ∧ r => And.intro hpr.left (Or.intro_right q hpr.right))
    )

theorem dist_or : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr : p ∨ (q ∧ r) =>
      have hpq : p ∨ q :=
        Or.elim
          hpqr
          (fun hp : p => Or.intro_left q hp)
          (fun hqr : q ∧ r => Or.intro_right p hqr.left)
      have hpr : p ∨ r :=
        Or.elim
          hpqr
          (fun hp : p => Or.intro_left r hp)
          (fun hqr : q ∧ r => Or.intro_right p hqr.right)
      And.intro hpq hpr
    )
    (fun hpqpr : (p ∨ q) ∧ (p ∨ r) =>
      And.elim
        (fun hpq : p ∨ q => fun hpr : p ∨ r =>
          Or.elim
            hpq
            (fun hp : p => Or.intro_left (q ∧ r) hp)
            (fun hq : q =>
              Or.elim
                hpr
                (fun hp : p => Or.intro_left (q ∧ r) hp)
                (fun hr : r => Or.intro_right p (And.intro hq hr))
            )
        )
        hpqpr
    )
