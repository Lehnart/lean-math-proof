import logic

universe u 
variable α : Type u
variable β : Type u

/- axiome d'extensionnalité -/
axiom set_ext {α} (E F : set α) : (∀x:α, ( E x ↔ F x )) → E = F

/- La réciproque découle de la définition de l'égalité -/
theorem set_ext_rec {α} (E F : set α) :  E = F → (∀x, ( E x ↔ F x )) :=
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

/- Axiome de séparation : l'ensemble des éléments d'un ensemble vérifiant une propriété existe -/
def sep (p : α → Prop) (s : set α) : set α :=
  (fun a : α,
    (s a) ∧ (p a)
  )

/- On peut toujours construire un ensemble vide -/
def empty_set {α} : (set α) :=
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
| list.nil        := empty_set 
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

/- Une condition suffisante pour qu'un singleton soit un sous ensemble d'un singleton est que les 2 éléments soient égaux -/
example (a b : α) : a = b -> (subset (singl a) (singl b)) :=
(fun h : a = b,
  (fun x : α,
    (fun h_a_x : a = x ,
      eq.symm (eq.rec h h_a_x)
    ) 
  )
)

/- Définition de l'U entre sous ensembles -/
def U {α} (s1 s2 : set α) : set α :=
  (fun a: α,
    s1 a ∨ s2 a
  )

theorem U_assoc (a b c : set α) : (U a (U b c)) = (U (U a b) c):= 
  set_ext  
    (U a (U b c))
    (U (U a b) c)
    (fun x : α,
      iff.intro 
        (fun h: (U a (U b c)) x,
           have h2 : a x ∨ b x ∨ c x := h,
           or.assoc.mpr h2 
        )
        (fun h: (U (U a b) c) x,
           have h2 : (a x ∨ b x) ∨ c x := h,
           or.assoc.mp h2 
        )
    )

theorem U_com (a b : set α) : U a b = U b a:= 
  set_ext  
    (U a b)
    (U b a)
    (fun x : α,
      iff.intro 
        (fun h: U a b x,
           have h2 : a x ∨ b x := h,
           or.comm.mp h2 
        )
        (fun h: U b a x,
           have h2 : b x ∨ a x := h,
           or.comm.mp h2 
        )
    )


theorem U_id (a b : set α) : (U a a) = a:= 
  set_ext  
    (U a a)
    (a)
    (fun x : α,
      iff.intro 
        (fun h: U a a x,
          have h2 : a x ∨ a x := h,
          or.elim
            h2
            id
            id
        )
        (fun h: a x,
           have h2 : a x := h,
           or.intro_left (a x) h2 
        )
    )


theorem U_empty (a b : set α) : (U a empty_set) = a:= 
  set_ext  
    (U a empty_set)
    (a)
    (fun x : α,
      iff.intro 
        (fun h: U a empty_set x,
          have h2 : a x ∨ false := h,
          or.elim
            h2
            id
            false.elim 
        )
        (fun h: a x,
           have h2 : a x := h,
           or.intro_left (false) h2 
        )
    )

/- Définition de l'intersection entre sous ensembles -/
def I {α} (s1 s2 : set α) : set α :=
  (fun a : α,
    (s1 a) ∧ (s2 a)
  )

theorem I_assoc (a b c : set α) : (I a (I b c)) = (I (I a b) c):= 
  set_ext  
    (I a (I b c))
    (I (I a b) c)
    (fun x : α,
      iff.intro 
        (fun h: (I a (I b c)) x,
          have h2 : a x ∧ b x ∧ c x := h,
          and.assoc.mpr h2 
        )
        (fun h: (I (I a b) c) x,
          have h2 : (a x ∧ b x) ∧ c x := h,
          and.assoc.mp h2 
        )
    )

theorem I_com (a b : set α) : I a b = I b a:= 
  set_ext  
    (I a b)
    (I b a)
    (fun x : α,
      iff.intro 
        (fun h: I a b x,
           have h2 : a x ∧ b x := h,
           and.comm.mp h2 
        )
        (fun h: I b a x,
           have h2 : b x ∧ a x := h,
           and.comm.mp h2 
        )
    )


theorem I_id (a b : set α) : (I a a) = a:= 
  set_ext  
    (I a a)
    (a)
    (fun x : α,
      iff.intro 
        (fun h: I a a x,
          have h2 : a x ∧ a x := h,
          and.left h2
        )
        (fun h: a x,
           have h2 : a x := h,
           and.intro h2 h2 
        )
    )


theorem I_empty (a b : set α) : (I a empty_set) = empty_set:= 
  set_ext  
    (I a empty_set)
    (empty_set)
    (fun x : α,
      iff.intro 
        (fun h: I a empty_set x,
          have h2 : a x ∧ false := h,
          and.right h2 
        )
        false.elim 
    )

theorem I_dist_over_U (a b c : set α) : (I a (U b c)) = (U (I a b) (I a c)):= 
  set_ext  
    (I a (U b c))
    (U (I a b) (I a c))
    (fun x : α,
      iff.intro 
        (fun h: (I a (U b c)) x,
          have h2 : a x ∧ (b x ∨ c x) := h,
          dist_and_over_or.mp h2
        )
        (fun h: (U (I a b) (I a c)) x,
          have h2 : a x ∧ b x ∨ a x ∧ c x := h,
          dist_and_over_or.mpr h2 
        )
    )

theorem U_dist_over_I (a b c : set α) : (U a (I b c)) = (I (U a b) (U a c)):= 
  set_ext  
    (U a (I b c))
    (I (U a b) (U a c))
    (fun x : α,
      iff.intro 
        (fun h: (U a (I b c)) x,
          have h2 : a x ∨ (b x ∧ c x) := h,
          dist_or_over_and.mp h2
        )
        (fun h: (I (U a b) (U a c)) x,
          have h2 : (a x ∨ b x) ∧ (a x ∨ c x) := h,
          dist_or_over_and.mpr h2 
        )
    )

example (a b : set α) : (subset a b) ↔ (I a b) = a :=
  iff.intro
    (fun h : subset a b,
      set_ext
        (I a b)
        a
        (fun x : α,
          iff.intro 
            (fun h_Iab : I a b x, 
              have h : a x ∧ b x := h_Iab,
              and.left h 
            )
            (fun h_a : a x, 
              have h_b : b x := h h_a,
              and.intro h_a h_b 
            )
        )
    )
    (fun h : (I a b) = a,
      (fun x : α,
        (fun ha : a x,
          have h_Iab_eq_a : (∀x, ( (I a b) x ↔ a x )) :=
            set_ext_rec
              (I a b)
              a 
              h
            ,
          have h_Iab_eq_a_x : (I a b) x ↔ a x := h_Iab_eq_a x,
          have h_Iab : a x ∧ b x := h_Iab_eq_a_x.mpr ha,
          and.right h_Iab
        )
      )
    )

example (a b : set α) : (subset a b) ↔ (U a b) = b :=
  iff.intro
    (fun h : subset a b,
      set_ext
        (U a b)
        b
        (fun x : α,
          iff.intro 
            (fun h_Uab : U a b x, 
              have h1 : a x ∨ b x := h_Uab,
              or.elim
                h1
                (fun ha: a x, h ha)
                id
            )
            (fun h_b : b x, 
              or.intro_right (a x) h_b  
            )
        )
    )
    (fun h : (U a b) = b,
      (fun x : α,
        (fun ha : a x,
          have h_Uab_eq_b : (∀x, ( (U a b) x ↔ b x )) :=
            set_ext_rec
              (U a b)
              b 
              h
            ,
          have h_Uab_eq_b_x : (U a b) x ↔ b x := h_Uab_eq_b x,
          have h_Uab : a x ∨ b x := or.intro_left (b x) ha,
          h_Uab_eq_b_x.mp h_Uab
        )
      )
    )

example (a b : set α) : a = b -> (U a b) = (I a b) :=
  (fun h : a = b ,
    set_ext 
      (U a b)
      (I a b)
      (fun x : α,
        iff.intro
          (fun h_uab : (U a b) x,
            have h2 : a x ∨ b x := h_uab,
            or.elim
              h2 
              (fun h_ax : a x, 
                have h_bx : b x := eq.rec h_ax h,
                and.intro h_ax h_bx 
              )
              (fun h_bx : b x, 
                have h_ax : a x := eq.rec h_bx (eq.symm h),
                and.intro h_ax h_bx 
              )
          )
          (fun h_iab : (I a b) x,
            have h2 : a x ∧ b x := h_iab,
            or.intro_left (b x) (and.left h2) 
          )
      )
  )

/- Définition de la différence entre sous ensembles -/
def diff (s t : set α) : set α :=
  (fun a : α,
    (s a) ∧ (¬ (t a) )
  )


/- Définition de l'ensemble des sous ensembles -/
def powerset (s : set α) : set (set α) :=
  (fun t : set α, 
    subset t s
  )


/- Définition du complémentaire -/
def C {α} (s1 s2 : set α) : set α :=
  (fun a: α,
    (¬ (s1 a)) ∧ s2 a
  )

/- Le complémentaire du complémentaire d'un ensemble est lui même -/
example (a b : set α) : subset a b -> C (C a b) b = a :=
  (fun h_sab : subset a b,
    set_ext
      (C (C a b) b)
      a 
      (fun x : α, 
        iff.intro
          (fun h_CCa : C (C a b) b x,
            have h_CCa_x : ((a x → false) ∧ b x → false) ∧ b x := h_CCa,
            have h1 : (a x → false) ∧ b x → false := and.left h_CCa,
            show a x, from
              classical.by_contradiction 
                (fun hna : ¬ (a x) ,
                  h1 ( and.intro hna (and.right h_CCa_x) )
                )
          )
          (fun ha : a x,
            have hb : b x := h_sab ha,
            have hnna : ¬ (¬ a x) := dne.mpr ha,
            and.intro (dne_intro (b x) hnna) hb  
          )
      )
  )

/- 1ere loi de morgan -/
example (e a b : set α) : subset a e -> subset b e -> C (U a b) e = I (C a e)(C b e) :=
  (fun hae : subset a e,
    (fun hbe : subset b e,
      set_ext 
        (C (U a b) e)
        (I (C a e)(C b e))
        (fun x : α, 
          iff.intro
            (fun h_CUabe : C (U a b) e x,
              have hex : e x := and.right h_CUabe,
              have hnbx : ¬ b x := and.right (dist_neg_over_or.mp (and.left h_CUabe)),
              have hnax : ¬ a x  := and.left (dist_neg_over_or.mp (and.left h_CUabe)),
              and.intro (and.intro hnax hex) (and.intro hnbx hex)
            )
            (fun hI_Cae_Cbe : I (C a e)(C b e) x,
              have hex : e x := and.right (and.right hI_Cae_Cbe),
              have hnax : ¬ (a x)  := and.left(and.left hI_Cae_Cbe),
              have hnbx : ¬ (b x)  := and.left (and.right hI_Cae_Cbe),
              have hnabx : ¬ (a x ∨ b x) := dist_neg_over_or.mpr (and.intro hnax hnbx),
              and.intro hnabx hex
            )
        )
    )
  ) 

/- 2eme loi de morgan -/
example (e a b : set α) : subset a e -> subset b e -> C (I a b) e = U (C a e)(C b e) :=
  (fun hae : subset a e,
    (fun hbe : subset b e,
      set_ext 
        (C (I a b) e)
        (U (C a e)(C b e))
        (fun x : α, 
          iff.intro
            (fun h_CIabe : C (I a b) e x,
              have hex : e x := and.right h_CIabe,
              have hna_or_nbx : ¬ a x ∨ ¬ b x := (dist_neg_over_and (and.left h_CIabe)),
              or.elim 
                hna_or_nbx
                (fun hnax : ¬ a x ,
                  or.intro_left  ((b x → false) ∧ e x) (and.intro hnax hex) 
                )
                (fun hnbx : ¬ b x ,
                  or.intro_right  ((a x → false) ∧ e x) (and.intro hnbx hex) 
                )
            )
            (fun hU_Cae_Cbe : U (C a e)(C b e) x,
              or.elim 
                hU_Cae_Cbe
                (fun h_Cae : (a x → false) ∧ e x,
                  and.intro 
                    (dne_intro (b x) (and.left h_Cae)) 
                    (and.right h_Cae) 
                )
                (fun h_Cbe : (b x → false) ∧ e x,
                  and.intro 
                    (dne_lintro (a x) (and.left h_Cbe)) 
                    (and.right h_Cbe) 
                )
            )
        )
    )
  ) 

/- une structure de paire qui va être la base des produits cartésiens-/
structure pair (α : Type u) :=
  intro :: (first : α) (second : α)

def pair_eq {α} (a b : pair α) : Prop :=
  (a.first = b.first) ∧ (a.second = b.second)

example ( a b c d : α ) :  pair_eq (pair.intro a b) (pair.intro c d) ↔ (a=c) ∧ (b=d):=
  iff.intro
  (fun heq : pair_eq (pair.intro a b) (pair.intro c d),
    heq
  )
  (fun ha_ac_and_bd : (a=c) ∧ (b=d),
    ha_ac_and_bd
  )

/- Un ensemble construit à partir de deux ensembles : le produit cartésien -/
def pair_set (a b : set α) : set (pair α) :=
  (fun hp : pair α,
    (a hp.first) ∧ (b hp.second)
  )

