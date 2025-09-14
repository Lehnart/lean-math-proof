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
    (fun ⟨hpq, hpr⟩ =>
        Or.elim
          hpq
          (Or.intro_left (q ∧ r) .)
          (fun hq : q =>
            Or.elim
              hpr
              (fun hp : p => Or.intro_left (q ∧ r) hp)
              (fun hr : r => Or.intro_right p (And.intro hq hr))
          )
    )

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr : p → (q → r) =>
      (fun hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        hpqr hp hq
      )
    )
    (fun hprq : (p ∧ q → r) =>
      (fun hp : p =>
        (fun hq : q =>
          hprq (And.intro hp hq)
        )
      )
    )

theorem t1 : (p ∨ q → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpq : (p ∨ q) → r =>
      And.intro
        (fun hp : p => hpq (Or.intro_left q hp))
        (fun hq : q => hpq (Or.intro_right p hq))
    )
    (fun hprqr : (p → r) ∧ (q → r) =>
      (fun hpq : p ∨ q =>
        Or.elim
          hpq
          (fun hp :p => hprqr.left hp)
          (fun hq :q => hprqr.right hq)
      )
    )

theorem not_over_or {p q : Prop}: ¬(p ∨ q) ↔ ¬p ∧ ¬q := t1

example : ¬p ∨ ¬q → ¬(p ∧ q) := (fun hnpnq => (fun ⟨hp, hq⟩ => Or.elim hnpnq (. hp) (. hq)))

example : ¬(p ∧ ¬p) := (fun ⟨hp, hnp⟩ => hnp hp)

example : p ∧ ¬q → ¬(p → q) := (fun ⟨hp, hnq⟩ => (fun hpq => (hnq ∘ hpq) hp) )

theorem not_p {q: Prop} : ¬p → (p → q) := (fun hnp => (fun hp => absurd hp hnp))

example : (¬p ∨ q) → (p → q) := ( fun hnpq => (fun hp => Or.elim hnpq (absurd hp .) (.) ))

example : p ∨ False ↔ p := Iff.intro (Or.elim . (.) False.elim) (Or.intro_left False .)

example : p ∧ False ↔ False := Iff.intro ( (And.right .) ) False.elim

example : ¬(p ↔ ¬p) := (fun h => let not_p (hp : p) := (h.mp hp) hp; not_p (h.mpr not_p))

theorem revert_imp : (p → q) → (¬q → ¬p) := (fun hpq => ( ((. ∘ hpq) .)) )

open Classical

theorem my_not_imp : ¬(a → b) →  a ∧ ¬b :=
  (fun hn_a_b =>
    let ha : a :=
      byContradiction
        (fun hn_a : ¬a =>
          let ha_b := not_p hn_a
          hn_a_b ha_b
        )
    let hnb : ¬b :=
      byContradiction
        (fun hnnb : ¬¬b =>
          let hb : b := dne hnnb
          let ha_b (_ : a) := hb
          hn_a_b ha_b
        )
    And.intro ha hnb
  )

example (p : Prop) : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  (fun hprs : p → r ∨ s =>
    byContradiction
      (fun hn_pr_or_ps : ¬((p → r) ∨ (p → s)) =>
        let hnpr_and_nps := not_over_or.mp hn_pr_or_ps
        And.elim
          (fun hnp : ¬(p → r) => fun hns : ¬(p → s) =>
            let hp_and_nr := my_not_imp hnp
            let hp_and_ns := my_not_imp hns
            let hp := hp_and_nr.left
            let hnr_and_ns := And.intro hp_and_nr.right hp_and_ns.right
            let hn_r_or_s := not_over_or.mpr hnr_and_ns
            let hr_or_s := hprs hp
            hn_r_or_s hr_or_s
          )
          hnpr_and_nps
      )
  )

theorem not_over_and : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun hn_p_and_q =>
    byContradiction
      (fun h : ¬(¬p ∨ ¬q) =>
        have ⟨ hnnp, hnnq ⟩ := not_or.mp h
        hn_p_and_q ⟨ (dne hnnp), (dne hnnq) ⟩
      )
  )

example : (p → q) → (¬p ∨ q) :=
  (fun hpq =>
    byCases
      ((.inr ∘ hpq) .)
      (.inl)
  )

example : (¬q → ¬p) → (p → q) :=
  (fun hnq_np =>
    byCases
      (fun hq : q => (fun _:p => hq))
      (fun hnq : ¬q => not_p (hnq_np hnq))
  )

example : (((p → q) → p) → p) :=
  (fun hpqp : (p → q) → p =>
    byCases
      (fun hpq => hpqp hpq)
      (fun hnpq => (And.left ∘ not_imp.mp) hnpq)
  )
