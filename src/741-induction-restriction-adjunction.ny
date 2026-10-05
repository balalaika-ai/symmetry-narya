export "740-abstract-restriction-induction"

{` Chapter 7 (absgroup.tex), sec:phi-functors: the adjunction φ_! ⊣ φ^*
   of xca:phi_!-|phi^*, Hom_H(φ_!X, Y) ≃ Hom_G(X, φ^*Y), for an abstract
   homomorphism φ : G → H, a G-set X and an H-set Y. Maps of G-sets are
   those of def:Hom-absG (AbstractGSetHom, equations of functions). The
   equivalence sends F to x ↦ F[e, x]; its inverse sends f to the map
   [t, x] ↦ t ·_Y f(x) induced on the quotient. `}

{` Maps of G-sets are determined by their underlying maps. `}
def agset_hom_path (G : AbstractGroup) (X Y : AbstractGSet G) (f g : AbstractGSetHom G X Y)
  (h : (x : agset_carrier G X) → Id (agset_carrier G Y) (f .fst x) (g .fst x))
  : Id (AbstractGSetHom G X Y) f g
  ≔ let A ≔ agset_carrier G X in let B ≔ agset_carrier G Y in
    subtype_equal (A → B)
      (k ↦ (s : G .carrier) → Id (A → B) (x ↦ k (agset_act G X s x)) (x ↦ agset_act G Y s (k x)))
      (k ↦ pi_prop (G .carrier) (s ↦ Id (A → B) (x ↦ k (agset_act G X s x)) (x ↦ agset_act G Y s (k x)))
        (s ↦ pi_set A (_ ↦ B) (_ ↦ agset_carrier_set G Y) (x ↦ k (agset_act G X s x)) (x ↦ agset_act G Y s (k x))))
      f g (funext A (_ ↦ B) (f .fst) (g .fst) h)

{` A map of G-sets from a pointwise equivariant map, and conversely. `}
def agset_hom_mk (G : AbstractGroup) (X Y : AbstractGSet G) (f : agset_carrier G X → agset_carrier G Y)
  (e : AgsetEquivariant G X Y f) : AbstractGSetHom G X Y
  ≔ (f, s ↦ funext (agset_carrier G X) (_ ↦ agset_carrier G Y) (x ↦ f (agset_act G X s x)) (x ↦ agset_act G Y s (f x)) (e s))

def agset_hom_equivariant (G : AbstractGroup) (X Y : AbstractGSet G) (f : AbstractGSetHom G X Y)
  : AgsetEquivariant G X Y (f .fst)
  ≔ s x ↦ happly (agset_carrier G X) (_ ↦ agset_carrier G Y) (x ↦ f .fst (agset_act G X s x))
      (x ↦ agset_act G Y s (f .fst x)) (f .snd s) x

{` F ↦ (x ↦ F[e, x]). Equivariance: [e, s·x] = [φ(s), x] = φ(s)·[e, x]. `}
def induce_restrict_left (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (F : AbstractGSetHom H (agset_induce G H φ X) Y) : AbstractGSetHom G X (agset_restrict G H φ Y)
  ≔ let T ≔ H .carrier in let C ≔ AgsetInduceCarrier G H φ X in
    let cls : T → agset_carrier G X → C ≔ t x ↦ agset_induce_class G H φ X t x in
    agset_hom_mk G X (agset_restrict G H φ Y) (x ↦ F .fst (cls (H .unit) x))
      (s x ↦ calc
         F .fst (cls (H .unit) (agset_act G X s x)) = F .fst (cls (φ .fst s) x)
           by refl (F .fst) (agset_induce_class_path G H φ X (H .unit, agset_act G X s x) (φ .fst s, x)
             (s, (H .laws .unit_left (φ .fst s), refl (agset_act G X s x))))
         = F .fst (cls (H .mul (φ .fst s) (H .unit)) x)
           by refl (F .fst) (refl ((t ↦ cls t x) : T → C)
             (inverse T (H .mul (φ .fst s) (H .unit)) (φ .fst s) (H .laws .unit_right (φ .fst s))))
         = agset_act H Y (φ .fst s) (F .fst (cls (H .unit) x))
           by agset_hom_equivariant H (agset_induce G H φ X) Y F (φ .fst s) (cls (H .unit) x) ∎)

{` f ↦ ([t, x] ↦ t ·_Y f(x)). `}
def induce_restrict_right_map (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (f : AbstractGSetHom G X (agset_restrict G H φ Y)) (z : AgsetInduceCarrier G H φ X) : agset_carrier H Y
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in let B ≔ agset_carrier H Y in
    let W ≔ AgsetInduceWitness G H φ X in
    let fe ≔ agset_hom_equivariant G X (agset_restrict G H φ Y) f in
    quotient_rec (Product T A) B (agset_induce_relation G H φ X) (agset_carrier_set H Y)
      (u ↦ agset_act H Y (u .fst) (f .fst (u .snd)))
      (u v r ↦ mere_rec (W u v) (Id B (agset_act H Y (u .fst) (f .fst (u .snd))) (agset_act H Y (v .fst) (f .fst (v .snd))))
        (agset_carrier_set H Y (agset_act H Y (u .fst) (f .fst (u .snd))) (agset_act H Y (v .fst) (f .fst (v .snd))))
        (w ↦ let g ≔ w .fst in
          calc
            agset_act H Y (u .fst) (f .fst (u .snd)) = agset_act H Y (u .fst) (f .fst (agset_act G X g (v .snd)))
              by refl ((x ↦ agset_act H Y (u .fst) (f .fst x)) : A → B) (w .snd .snd)
            = agset_act H Y (u .fst) (agset_act H Y (φ .fst g) (f .fst (v .snd)))
              by refl (agset_act H Y (u .fst)) (fe g (v .snd))
            = agset_act H Y (H .mul (u .fst) (φ .fst g)) (f .fst (v .snd))
              by inverse B (agset_act H Y (H .mul (u .fst) (φ .fst g)) (f .fst (v .snd)))
                (agset_act H Y (u .fst) (agset_act H Y (φ .fst g) (f .fst (v .snd))))
                (agset_act_mul H Y (u .fst) (φ .fst g) (f .fst (v .snd)))
            = agset_act H Y (v .fst) (f .fst (v .snd))
              by refl ((t ↦ agset_act H Y t (f .fst (v .snd))) : T → B) (w .snd .fst) ∎)
        r)
      z

def induce_restrict_right (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  (f : AbstractGSetHom G X (agset_restrict G H φ Y)) : AbstractGSetHom H (agset_induce G H φ X) Y
  ≔ let T ≔ H .carrier in let I ≔ agset_induce G H φ X in
    let m ≔ induce_restrict_right_map G H φ X Y f in
    agset_hom_mk H I Y m
      (h z ↦ quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
        (z ↦ Id (agset_carrier H Y) (m (agset_act H I h z)) (agset_act H Y h (m z)))
        (z ↦ agset_carrier_set H Y (m (agset_act H I h z)) (agset_act H Y h (m z)))
        (u ↦ agset_act_mul H Y h (u .fst) (f .fst (u .snd)))
        z)

{` xca:phi_!-|phi^*: Hom_H(φ_!X, Y) ≃ Hom_G(X, φ^*Y). `}
def induce_restrict_abstract_adjunction (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (Y : AbstractGSet H)
  : Equiv (AbstractGSetHom H (agset_induce G H φ X) Y) (AbstractGSetHom G X (agset_restrict G H φ Y))
  ≔ let T ≔ H .carrier in let I ≔ agset_induce G H φ X in let R ≔ agset_restrict G H φ Y in
    let C ≔ AgsetInduceCarrier G H φ X in
    let L ≔ induce_restrict_left G H φ X Y in let Rt ≔ induce_restrict_right G H φ X Y in
    quasi_inverse_equiv (AbstractGSetHom H I Y) (AbstractGSetHom G X R) L Rt
      (F ↦ agset_hom_path H I Y (Rt (L F)) F
        (z ↦ quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
          (z ↦ Id (agset_carrier H Y) (Rt (L F) .fst z) (F .fst z))
          (z ↦ agset_carrier_set H Y (Rt (L F) .fst z) (F .fst z))
          (u ↦ calc
             agset_act H Y (u .fst) (F .fst (agset_induce_class G H φ X (H .unit) (u .snd)))
               = F .fst (agset_induce_class G H φ X (H .mul (u .fst) (H .unit)) (u .snd))
               by inverse (agset_carrier H Y) (F .fst (agset_induce_class G H φ X (H .mul (u .fst) (H .unit)) (u .snd)))
                 (agset_act H Y (u .fst) (F .fst (agset_induce_class G H φ X (H .unit) (u .snd))))
                 (agset_hom_equivariant H I Y F (u .fst) (agset_induce_class G H φ X (H .unit) (u .snd)))
             = F .fst (agset_induce_class G H φ X (u .fst) (u .snd))
               by refl (F .fst) (refl ((t ↦ agset_induce_class G H φ X t (u .snd)) : T → C) (H .laws .unit_right (u .fst))) ∎)
          z))
      (f ↦ agset_hom_path G X R (L (Rt f)) f (x ↦ agset_act_unit H Y (f .fst x)))

def induce_restrict_abstract_adjunction_map (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (Y : AbstractGSet H) (F : AbstractGSetHom H (agset_induce G H φ X) Y) (x : agset_carrier G X)
  : Id (agset_carrier H Y) (induce_restrict_abstract_adjunction G H φ X Y .map F .fst x)
      (F .fst (agset_induce_class G H φ X (H .unit) x))
  ≔ refl (F .fst (agset_induce_class G H φ X (H .unit) x))

{` Litmus: the adjunct of the isomorphism φ_!(P_G) ≅ P_H of
   xca:Bconcr-OK (1) is φ itself (as a map P_G → φ^*P_H). `}
def induce_principal_adjunct (G H : AbstractGroup) (φ : AbstractHom G H) (x : G .carrier)
  : Id (H .carrier)
      (induce_restrict_abstract_adjunction G H φ (agset_principal G) (agset_principal H) .map
        (agset_iso_hom H (agset_induce G H φ (agset_principal G)) (agset_principal H) (induce_principal_iso G H φ)) .fst x)
      (φ .fst x)
  ≔ H .laws .unit_left (φ .fst x)
