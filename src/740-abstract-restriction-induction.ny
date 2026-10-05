export "706-abstract-gset-identity"
export "142-quotient-cycles"

{` Chapter 7 (absgroup.tex), sec:phi-functors: restriction φ^* (def:phi^*)
   and induction φ_! (def:phi_!, xca:phi_!-OK) along an abstract
   homomorphism φ : G → H, the isomorphism φ_!(P_G) ≅ P_H of
   xca:Bconcr-OK (1), and the action of φ_! on isomorphisms and
   identifications of G-sets. φ_!(X) is the set quotient (T × X)/∼ with
   (t, x) ∼ (u, y) ≔ ∃_{g : S} (t φ(g) = u) × (x = g ·_X y), constructed as
   Quotient (module 41); the action of h is induced by (t, x) ↦ (h t, x). `}

{` def:phi^*. φ^*(S, ψ) ≔ (S, ψ ∘ φ). `}
def agset_restrict (G H : AbstractGroup) (φ : AbstractHom G H) (Y : AbstractGSet H) : AbstractGSet G
  ≔ (Y .fst, abstract_hom_compose G H (abstr (permutation_group (Y .fst))) φ (Y .snd))

def agset_restrict_act (G H : AbstractGroup) (φ : AbstractHom G H) (Y : AbstractGSet H) (s : G .carrier)
  (y : agset_carrier H Y)
  : Id (agset_carrier H Y) (agset_act G (agset_restrict G H φ Y) s y) (agset_act H Y (φ .fst s) y)
  ≔ refl (agset_act H Y (φ .fst s) y)

{` The inverse of an isomorphism of G-sets. `}
def agset_iso_inverse (G : AbstractGroup) (X Y : AbstractGSet G) (f : AbstractGSetIso G X Y) : AbstractGSetIso G Y X
  ≔ let A ≔ agset_carrier G X in let B ≔ agset_carrier G Y in
    let g ≔ equiv_inverse_map A B (f .fst) in
    (canonical_inverse_equiv A B (f .fst),
     s y ↦ equivalence_injective A B (f .fst) (g (agset_act G Y s y)) (agset_act G X s (g y))
       (calc
          f .fst .map (g (agset_act G Y s y)) = agset_act G Y s y by equiv_counit A B (f .fst) (agset_act G Y s y)
          = agset_act G Y s (f .fst .map (g y))
            by inverse B (agset_act G Y s (f .fst .map (g y))) (agset_act G Y s y)
              (refl (agset_act G Y s) (equiv_counit A B (f .fst) y))
          = f .fst .map (agset_act G X s (g y))
            by inverse B (f .fst .map (agset_act G X s (g y))) (agset_act G Y s (f .fst .map (g y))) (f .snd s (g y)) ∎))

{` def:phi_!: the relation and its witnesses. `}
def AgsetInduceWitness (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (u v : Product (H .carrier) (agset_carrier G X)) : Type
  ≔ Σ (G .carrier) (g ↦ Product (Id (H .carrier) (H .mul (u .fst) (φ .fst g)) (v .fst))
      (Id (agset_carrier G X) (u .snd) (agset_act G X g (v .snd))))

def agset_induce_witness_refl (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (u : Product (H .carrier) (agset_carrier G X)) : AgsetInduceWitness G H φ X u u
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    (G .unit,
     (concat T (H .mul (u .fst) (φ .fst (G .unit))) (H .mul (u .fst) (H .unit)) (u .fst)
        (refl (H .mul (u .fst)) (abstract_hom_preserves_unit G H (φ .fst) (φ .snd)))
        (H .laws .unit_right (u .fst)),
      inverse A (agset_act G X (G .unit) (u .snd)) (u .snd) (agset_act_unit G X (u .snd))))

def agset_induce_witness_symm (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (u v : Product (H .carrier) (agset_carrier G X)) (w : AgsetInduceWitness G H φ X u v) : AgsetInduceWitness G H φ X v u
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    let g ≔ w .fst in let ig ≔ G .inv g in let fg ≔ φ .fst g in
    (ig,
     (calc
        H .mul (v .fst) (φ .fst ig) = H .mul (v .fst) (H .inv fg)
          by refl (H .mul (v .fst)) (abstract_hom_preserves_inv G H (φ .fst) (φ .snd) g)
        = H .mul (H .mul (u .fst) fg) (H .inv fg)
          by refl ((t ↦ H .mul t (H .inv fg)) : T → T) (inverse T (H .mul (u .fst) fg) (v .fst) (w .snd .fst))
        = u .fst by ag_mul_inv_cancel_right H (u .fst) fg ∎,
      calc
        v .snd = agset_act G X (G .unit) (v .snd)
          by inverse A (agset_act G X (G .unit) (v .snd)) (v .snd) (agset_act_unit G X (v .snd))
        = agset_act G X (G .mul ig g) (v .snd)
          by refl ((s ↦ agset_act G X s (v .snd)) : G .carrier → A)
            (inverse (G .carrier) (G .mul ig g) (G .unit) (ag_inv_left G g))
        = agset_act G X ig (agset_act G X g (v .snd)) by agset_act_mul G X ig g (v .snd)
        = agset_act G X ig (u .snd)
          by refl (agset_act G X ig) (inverse A (u .snd) (agset_act G X g (v .snd)) (w .snd .snd)) ∎))

def agset_induce_witness_trans (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (u v z : Product (H .carrier) (agset_carrier G X))
  (w1 : AgsetInduceWitness G H φ X u v) (w2 : AgsetInduceWitness G H φ X v z) : AgsetInduceWitness G H φ X u z
  ≔ let T ≔ H .carrier in let A ≔ agset_carrier G X in
    let g1 ≔ w1 .fst in let g2 ≔ w2 .fst in
    (G .mul g1 g2,
     (calc
        H .mul (u .fst) (φ .fst (G .mul g1 g2)) = H .mul (u .fst) (H .mul (φ .fst g1) (φ .fst g2))
          by refl (H .mul (u .fst)) (φ .snd g1 g2)
        = H .mul (H .mul (u .fst) (φ .fst g1)) (φ .fst g2) by H .laws .assoc (u .fst) (φ .fst g1) (φ .fst g2)
        = H .mul (v .fst) (φ .fst g2) by refl ((t ↦ H .mul t (φ .fst g2)) : T → T) (w1 .snd .fst)
        = z .fst by w2 .snd .fst ∎,
      calc
        u .snd = agset_act G X g1 (v .snd) by w1 .snd .snd
        = agset_act G X g1 (agset_act G X g2 (z .snd)) by refl (agset_act G X g1) (w2 .snd .snd)
        = agset_act G X (G .mul g1 g2) (z .snd)
          by inverse A (agset_act G X (G .mul g1 g2) (z .snd)) (agset_act G X g1 (agset_act G X g2 (z .snd)))
            (agset_act_mul G X g1 g2 (z .snd)) ∎))

{` xca:phi_!-OK (1): ∼ is an equivalence relation. `}
def agset_induce_relation (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  : EquivalenceRelation (Product (H .carrier) (agset_carrier G X))
  ≔ let W ≔ AgsetInduceWitness G H φ X in
    (predicate ≔ u v ↦ (Mere (W u v), mere_isprop (W u v)),
     reflexive ≔ u ↦ mere (W u u) (agset_induce_witness_refl G H φ X u),
     symmetric ≔ u v r ↦ mere_rec (W u v) (Mere (W v u)) (mere_isprop (W v u))
       (w ↦ mere (W v u) (agset_induce_witness_symm G H φ X u v w)) r,
     transitive ≔ u v z r1 r2 ↦ mere_rec (W u v) (Mere (W u z)) (mere_isprop (W u z))
       (w1 ↦ mere_rec (W v z) (Mere (W u z)) (mere_isprop (W u z))
         (w2 ↦ mere (W u z) (agset_induce_witness_trans G H φ X u v z w1 w2)) r2) r1)

def AgsetInduceCarrier (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) : Type
  ≔ Quotient (Product (H .carrier) (agset_carrier G X)) (agset_induce_relation G H φ X)

def agset_induce_class (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (t : H .carrier) (x : agset_carrier G X) : AgsetInduceCarrier G H φ X
  ≔ quotient_class (Product (H .carrier) (agset_carrier G X)) (agset_induce_relation G H φ X) (t, x)

def agset_induce_carrier_set (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  : isSet (AgsetInduceCarrier G H φ X)
  ≔ quotient_set (Product (H .carrier) (agset_carrier G X)) (agset_induce_relation G H φ X)

{` Related representatives give the same class. `}
def agset_induce_class_path (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (u v : Product (H .carrier) (agset_carrier G X)) (w : AgsetInduceWitness G H φ X u v)
  : Id (AgsetInduceCarrier G H φ X) (agset_induce_class G H φ X (u .fst) (u .snd)) (agset_induce_class G H φ X (v .fst) (v .snd))
  ≔ quotient_encode (Product (H .carrier) (agset_carrier G X)) (agset_induce_relation G H φ X) u v
      (mere (AgsetInduceWitness G H φ X u v) w)

{` xca:phi_!-OK (2): (t, x) ↦ (h t, x) respects ∼. `}
def agset_induce_shift_witness (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h : H .carrier)
  (u v : Product (H .carrier) (agset_carrier G X)) (w : AgsetInduceWitness G H φ X u v)
  : AgsetInduceWitness G H φ X (H .mul h (u .fst), u .snd) (H .mul h (v .fst), v .snd)
  ≔ let T ≔ H .carrier in let fg ≔ φ .fst (w .fst) in
    (w .fst,
     (concat T (H .mul (H .mul h (u .fst)) fg) (H .mul h (H .mul (u .fst) fg)) (H .mul h (v .fst))
        (inverse T (H .mul h (H .mul (u .fst) fg)) (H .mul (H .mul h (u .fst)) fg) (H .laws .assoc h (u .fst) fg))
        (refl (H .mul h) (w .snd .fst)),
      w .snd .snd))

def agset_induce_shift_respects (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h : H .carrier)
  : Respects (Product (H .carrier) (agset_carrier G X)) (AgsetInduceCarrier G H φ X) (agset_induce_relation G H φ X)
      (u ↦ agset_induce_class G H φ X (H .mul h (u .fst)) (u .snd))
  ≔ let W ≔ AgsetInduceWitness G H φ X in
    u v r ↦ quotient_encode (Product (H .carrier) (agset_carrier G X)) (agset_induce_relation G H φ X)
      (H .mul h (u .fst), u .snd) (H .mul h (v .fst), v .snd)
      (mere_rec (W u v) (Mere (W (H .mul h (u .fst), u .snd) (H .mul h (v .fst), v .snd)))
        (mere_isprop (W (H .mul h (u .fst), u .snd) (H .mul h (v .fst), v .snd)))
        (w ↦ mere (W (H .mul h (u .fst), u .snd) (H .mul h (v .fst), v .snd)) (agset_induce_shift_witness G H φ X h u v w)) r)

def agset_induce_act (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h : H .carrier)
  (z : AgsetInduceCarrier G H φ X) : AgsetInduceCarrier G H φ X
  ≔ quotient_rec (Product (H .carrier) (agset_carrier G X)) (AgsetInduceCarrier G H φ X) (agset_induce_relation G H φ X)
      (agset_induce_carrier_set G H φ X) (u ↦ agset_induce_class G H φ X (H .mul h (u .fst)) (u .snd))
      (agset_induce_shift_respects G H φ X h) z

def agset_induce_act_mul (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h h' : H .carrier)
  (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X) (agset_induce_act G H φ X (H .mul h h') z)
      (agset_induce_act G H φ X h (agset_induce_act G H φ X h' z))
  ≔ let C ≔ AgsetInduceCarrier G H φ X in let T ≔ H .carrier in
    quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C (agset_induce_act G H φ X (H .mul h h') z) (agset_induce_act G H φ X h (agset_induce_act G H φ X h' z)))
      (z ↦ agset_induce_carrier_set G H φ X (agset_induce_act G H φ X (H .mul h h') z)
        (agset_induce_act G H φ X h (agset_induce_act G H φ X h' z)))
      (u ↦ refl ((t ↦ agset_induce_class G H φ X t (u .snd)) : T → C)
        (inverse T (H .mul h (H .mul h' (u .fst))) (H .mul (H .mul h h') (u .fst)) (H .laws .assoc h h' (u .fst))))
      z

def agset_induce_act_unit (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X) (agset_induce_act G H φ X (H .unit) z) z
  ≔ let C ≔ AgsetInduceCarrier G H φ X in let T ≔ H .carrier in
    quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C (agset_induce_act G H φ X (H .unit) z) z)
      (z ↦ agset_induce_carrier_set G H φ X (agset_induce_act G H φ X (H .unit) z) z)
      (u ↦ refl ((t ↦ agset_induce_class G H φ X t (u .snd)) : T → C) (H .laws .unit_left (u .fst)))
      z

{` def:phi_! and xca:phi_!-OK (3): φ_!(X) ≔ P_H ×_G X, an H-set. `}
def agset_induce (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) : AbstractGSet H
  ≔ agset_from_action H (AgsetInduceCarrier G H φ X, agset_induce_carrier_set G H φ X) (agset_induce_act G H φ X)
      (agset_induce_act_mul G H φ X) (agset_induce_act_unit G H φ X)

def agset_induce_act_class (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G) (h t : H .carrier)
  (x : agset_carrier G X)
  : Id (AgsetInduceCarrier G H φ X) (agset_act H (agset_induce G H φ X) h (agset_induce_class G H φ X t x))
      (agset_induce_class G H φ X (H .mul h t) x)
  ≔ refl (agset_induce_class G H φ X (H .mul h t) x)

{` xca:Bconcr-OK (1): (t, x) ↦ t φ(x) induces φ_!(P_G) ≅ P_H, with
   inverse t ↦ [t, e]. `}
def induce_principal_map (G H : AbstractGroup) (φ : AbstractHom G H) (z : AgsetInduceCarrier G H φ (agset_principal G))
  : H .carrier
  ≔ let T ≔ H .carrier in let S ≔ G .carrier in let W ≔ AgsetInduceWitness G H φ (agset_principal G) in
    quotient_rec (Product T S) T (agset_induce_relation G H φ (agset_principal G)) (abstract_group_set H)
      (u ↦ H .mul (u .fst) (φ .fst (u .snd)))
      (u v r ↦ mere_rec (W u v) (Id T (H .mul (u .fst) (φ .fst (u .snd))) (H .mul (v .fst) (φ .fst (v .snd))))
        (abstract_group_set H (H .mul (u .fst) (φ .fst (u .snd))) (H .mul (v .fst) (φ .fst (v .snd))))
        (w ↦ let g ≔ w .fst in
          calc
            H .mul (u .fst) (φ .fst (u .snd)) = H .mul (u .fst) (φ .fst (G .mul g (v .snd)))
              by refl ((x ↦ H .mul (u .fst) (φ .fst x)) : S → T) (w .snd .snd)
            = H .mul (u .fst) (H .mul (φ .fst g) (φ .fst (v .snd))) by refl (H .mul (u .fst)) (φ .snd g (v .snd))
            = H .mul (H .mul (u .fst) (φ .fst g)) (φ .fst (v .snd)) by H .laws .assoc (u .fst) (φ .fst g) (φ .fst (v .snd))
            = H .mul (v .fst) (φ .fst (v .snd)) by refl ((t ↦ H .mul t (φ .fst (v .snd))) : T → T) (w .snd .fst) ∎)
        r)
      z

def induce_principal_iso (G H : AbstractGroup) (φ : AbstractHom G H)
  : AbstractGSetIso H (agset_induce G H φ (agset_principal G)) (agset_principal H)
  ≔ let T ≔ H .carrier in let S ≔ G .carrier in let P ≔ agset_principal G in
    let C ≔ AgsetInduceCarrier G H φ P in
    let back : T → C ≔ t ↦ agset_induce_class G H φ P t (G .unit) in
    (quasi_inverse_equiv C T (induce_principal_map G H φ) back
       (z ↦ quotient_prop_induction (Product T S) (agset_induce_relation G H φ P)
          (z ↦ Id C (back (induce_principal_map G H φ z)) z)
          (z ↦ agset_induce_carrier_set G H φ P (back (induce_principal_map G H φ z)) z)
          (u ↦ inverse C (agset_induce_class G H φ P (u .fst) (u .snd)) (back (H .mul (u .fst) (φ .fst (u .snd))))
            (agset_induce_class_path G H φ P (u .fst, u .snd) (H .mul (u .fst) (φ .fst (u .snd)), G .unit)
              (u .snd, (refl (H .mul (u .fst) (φ .fst (u .snd))),
                inverse S (G .mul (u .snd) (G .unit)) (u .snd) (G .laws .unit_right (u .snd))))))
          z)
       (t ↦ concat T (H .mul t (φ .fst (G .unit))) (H .mul t (H .unit)) t
          (refl (H .mul t) (abstract_hom_preserves_unit G H (φ .fst) (φ .snd)))
          (H .laws .unit_right t)),
     h z ↦ quotient_prop_induction (Product T S) (agset_induce_relation G H φ P)
       (z ↦ Id T (induce_principal_map G H φ (agset_induce_act G H φ P h z)) (H .mul h (induce_principal_map G H φ z)))
       (z ↦ abstract_group_set H (induce_principal_map G H φ (agset_induce_act G H φ P h z)) (H .mul h (induce_principal_map G H φ z)))
       (u ↦ inverse T (H .mul h (H .mul (u .fst) (φ .fst (u .snd)))) (H .mul (H .mul h (u .fst)) (φ .fst (u .snd)))
         (H .laws .assoc h (u .fst) (φ .fst (u .snd))))
       z)

def induce_principal_path (G H : AbstractGroup) (φ : AbstractHom G H)
  : Id (AbstractGSet H) (agset_induce G H φ (agset_principal G)) (agset_principal H)
  ≔ agset_path_from_iso H (agset_induce G H φ (agset_principal G)) (agset_principal H) (induce_principal_iso G H φ)

{` φ_! on maps: [t, x] ↦ [t, f(x)] for an equivariant f. `}
def agset_induce_fun (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G)
  (f : agset_carrier G X → agset_carrier G X') (hf : AgsetEquivariant G X X' f) (z : AgsetInduceCarrier G H φ X)
  : AgsetInduceCarrier G H φ X'
  ≔ let T ≔ H .carrier in let W ≔ AgsetInduceWitness G H φ X in let W' ≔ AgsetInduceWitness G H φ X' in
    quotient_rec (Product T (agset_carrier G X)) (AgsetInduceCarrier G H φ X') (agset_induce_relation G H φ X)
      (agset_induce_carrier_set G H φ X') (u ↦ agset_induce_class G H φ X' (u .fst) (f (u .snd)))
      (u v r ↦ quotient_encode (Product T (agset_carrier G X')) (agset_induce_relation G H φ X')
        (u .fst, f (u .snd)) (v .fst, f (v .snd))
        (mere_rec (W u v) (Mere (W' (u .fst, f (u .snd)) (v .fst, f (v .snd))))
          (mere_isprop (W' (u .fst, f (u .snd)) (v .fst, f (v .snd))))
          (w ↦ mere (W' (u .fst, f (u .snd)) (v .fst, f (v .snd)))
            (w .fst, (w .snd .fst,
              concat (agset_carrier G X') (f (u .snd)) (f (agset_act G X (w .fst) (v .snd))) (agset_act G X' (w .fst) (f (v .snd)))
                (refl f (w .snd .snd)) (hf (w .fst) (v .snd))))) r))
      z

def agset_induce_fun_equivariant (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G)
  (f : agset_carrier G X → agset_carrier G X') (hf : AgsetEquivariant G X X' f)
  : AgsetEquivariant H (agset_induce G H φ X) (agset_induce G H φ X') (agset_induce_fun G H φ X X' f hf)
  ≔ let T ≔ H .carrier in let C' ≔ AgsetInduceCarrier G H φ X' in
    h z ↦ quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C' (agset_induce_fun G H φ X X' f hf (agset_induce_act G H φ X h z))
        (agset_induce_act G H φ X' h (agset_induce_fun G H φ X X' f hf z)))
      (z ↦ agset_induce_carrier_set G H φ X' (agset_induce_fun G H φ X X' f hf (agset_induce_act G H φ X h z))
        (agset_induce_act G H φ X' h (agset_induce_fun G H φ X X' f hf z)))
      (u ↦ refl (agset_induce_class G H φ X' (H .mul h (u .fst)) (f (u .snd))))
      z

{` Pointwise equal maps induce equal maps. `}
def agset_induce_fun_homotopy (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G)
  (f f' : agset_carrier G X → agset_carrier G X') (hf : AgsetEquivariant G X X' f) (hf' : AgsetEquivariant G X X' f')
  (e : (x : agset_carrier G X) → Id (agset_carrier G X') (f x) (f' x)) (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X') (agset_induce_fun G H φ X X' f hf z) (agset_induce_fun G H φ X X' f' hf' z)
  ≔ let T ≔ H .carrier in let C' ≔ AgsetInduceCarrier G H φ X' in
    quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C' (agset_induce_fun G H φ X X' f hf z) (agset_induce_fun G H φ X X' f' hf' z))
      (z ↦ agset_induce_carrier_set G H φ X' (agset_induce_fun G H φ X X' f hf z) (agset_induce_fun G H φ X X' f' hf' z))
      (u ↦ refl (agset_induce_class G H φ X' (u .fst)) (e (u .snd)))
      z

{` The induced map of a composite is the composite of induced maps. `}
def agset_induce_fun_compose (G H : AbstractGroup) (φ : AbstractHom G H) (X X' X'' : AbstractGSet G)
  (f : agset_carrier G X → agset_carrier G X') (hf : AgsetEquivariant G X X' f)
  (f' : agset_carrier G X' → agset_carrier G X'') (hf' : AgsetEquivariant G X' X'' f')
  (hff : AgsetEquivariant G X X'' (x ↦ f' (f x))) (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X'') (agset_induce_fun G H φ X X'' (x ↦ f' (f x)) hff z)
      (agset_induce_fun G H φ X' X'' f' hf' (agset_induce_fun G H φ X X' f hf z))
  ≔ let T ≔ H .carrier in let C'' ≔ AgsetInduceCarrier G H φ X'' in
    quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C'' (agset_induce_fun G H φ X X'' (x ↦ f' (f x)) hff z)
        (agset_induce_fun G H φ X' X'' f' hf' (agset_induce_fun G H φ X X' f hf z)))
      (z ↦ agset_induce_carrier_set G H φ X'' (agset_induce_fun G H φ X X'' (x ↦ f' (f x)) hff z)
        (agset_induce_fun G H φ X' X'' f' hf' (agset_induce_fun G H φ X X' f hf z)))
      (u ↦ refl (agset_induce_class G H φ X'' (u .fst) (f' (f (u .snd)))))
      z

def agset_induce_fun_identity (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractGSet G)
  (hid : AgsetEquivariant G X X (x ↦ x)) (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X) (agset_induce_fun G H φ X X (x ↦ x) hid z) z
  ≔ let T ≔ H .carrier in let C ≔ AgsetInduceCarrier G H φ X in
    quotient_prop_induction (Product T (agset_carrier G X)) (agset_induce_relation G H φ X)
      (z ↦ Id C (agset_induce_fun G H φ X X (x ↦ x) hid z) z)
      (z ↦ agset_induce_carrier_set G H φ X (agset_induce_fun G H φ X X (x ↦ x) hid z) z)
      (u ↦ refl (agset_induce_class G H φ X (u .fst) (u .snd)))
      z

{` φ_! on isomorphisms. `}
def agset_induce_iso (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G) (f : AbstractGSetIso G X X')
  : AbstractGSetIso H (agset_induce G H φ X) (agset_induce G H φ X')
  ≔ let A ≔ agset_carrier G X in let A' ≔ agset_carrier G X' in
    let C ≔ AgsetInduceCarrier G H φ X in let C' ≔ AgsetInduceCarrier G H φ X' in
    let g ≔ agset_iso_inverse G X X' f in
    let F ≔ agset_induce_fun G H φ X X' (f .fst .map) (f .snd) in
    let Gm ≔ agset_induce_fun G H φ X' X (g .fst .map) (g .snd) in
    (quasi_inverse_equiv C C' F Gm
       (z ↦ concat C (Gm (F z)) (agset_induce_fun G H φ X X (x ↦ g .fst .map (f .fst .map x))
                (agset_iso_compose G X X' X f g .snd) z) z
          (inverse C (agset_induce_fun G H φ X X (x ↦ g .fst .map (f .fst .map x)) (agset_iso_compose G X X' X f g .snd) z) (Gm (F z))
            (agset_induce_fun_compose G H φ X X' X (f .fst .map) (f .snd) (g .fst .map) (g .snd)
              (agset_iso_compose G X X' X f g .snd) z))
          (concat C (agset_induce_fun G H φ X X (x ↦ g .fst .map (f .fst .map x)) (agset_iso_compose G X X' X f g .snd) z)
             (agset_induce_fun G H φ X X (x ↦ x) (agset_iso_id G X .snd) z) z
             (agset_induce_fun_homotopy G H φ X X (x ↦ g .fst .map (f .fst .map x)) (x ↦ x)
               (agset_iso_compose G X X' X f g .snd) (agset_iso_id G X .snd) (equiv_retraction A A' (f .fst)) z)
             (agset_induce_fun_identity G H φ X (agset_iso_id G X .snd) z)))
       (z ↦ concat C' (F (Gm z)) (agset_induce_fun G H φ X' X' (x ↦ f .fst .map (g .fst .map x))
                (agset_iso_compose G X' X X' g f .snd) z) z
          (inverse C' (agset_induce_fun G H φ X' X' (x ↦ f .fst .map (g .fst .map x)) (agset_iso_compose G X' X X' g f .snd) z) (F (Gm z))
            (agset_induce_fun_compose G H φ X' X X' (g .fst .map) (g .snd) (f .fst .map) (f .snd)
              (agset_iso_compose G X' X X' g f .snd) z))
          (concat C' (agset_induce_fun G H φ X' X' (x ↦ f .fst .map (g .fst .map x)) (agset_iso_compose G X' X X' g f .snd) z)
             (agset_induce_fun G H φ X' X' (x ↦ x) (agset_iso_id G X' .snd) z) z
             (agset_induce_fun_homotopy G H φ X' X' (x ↦ f .fst .map (g .fst .map x)) (x ↦ x)
               (agset_iso_compose G X' X X' g f .snd) (agset_iso_id G X' .snd) (equiv_counit A A' (f .fst)) z)
             (agset_induce_fun_identity G H φ X' (agset_iso_id G X' .snd) z))),
     agset_induce_fun_equivariant G H φ X X' (f .fst .map) (f .snd))

{` φ_! on identifications: iso(ap_{φ_!}(p)) = φ_!(iso(p)). `}
def agset_induce_ap_map (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G) (p : Id (AbstractGSet G) X X')
  (z : AgsetInduceCarrier G H φ X)
  : Id (AgsetInduceCarrier G H φ X')
      (agset_path_to_iso H (agset_induce G H φ X) (agset_induce G H φ X') (refl (agset_induce G H φ) p) .fst .map z)
      (agset_induce_fun G H φ X X' (agset_path_to_iso G X X' p .fst .map) (agset_path_to_iso G X X' p .snd) z)
  ≔ let T ≔ H .carrier in
    J (AbstractGSet G) X
      (X' p ↦ (z : AgsetInduceCarrier G H φ X) → Id (AgsetInduceCarrier G H φ X')
        (agset_path_to_iso H (agset_induce G H φ X) (agset_induce G H φ X') (refl (agset_induce G H φ) p) .fst .map z)
        (agset_induce_fun G H φ X X' (agset_path_to_iso G X X' p .fst .map) (agset_path_to_iso G X X' p .snd) z))
      (z ↦ let C ≔ AgsetInduceCarrier G H φ X in
        concat C (agset_path_to_iso H (agset_induce G H φ X) (agset_induce G H φ X) (refl (agset_induce G H φ X)) .fst .map z) z
          (agset_induce_fun G H φ X X (agset_path_to_iso G X X (refl X) .fst .map) (agset_path_to_iso G X X (refl X) .snd) z)
          (agset_path_to_iso_refl_map H (agset_induce G H φ X) z)
          (inverse C (agset_induce_fun G H φ X X (agset_path_to_iso G X X (refl X) .fst .map) (agset_path_to_iso G X X (refl X) .snd) z) z
            (concat C (agset_induce_fun G H φ X X (agset_path_to_iso G X X (refl X) .fst .map) (agset_path_to_iso G X X (refl X) .snd) z)
              (agset_induce_fun G H φ X X (x ↦ x) (agset_iso_id G X .snd) z) z
              (agset_induce_fun_homotopy G H φ X X (agset_path_to_iso G X X (refl X) .fst .map) (x ↦ x)
                (agset_path_to_iso G X X (refl X) .snd) (agset_iso_id G X .snd) (agset_path_to_iso_refl_map G X) z)
              (agset_induce_fun_identity G H φ X (agset_iso_id G X .snd) z))))
      X' p z

def agset_induce_ap_iso (G H : AbstractGroup) (φ : AbstractHom G H) (X X' : AbstractGSet G) (p : Id (AbstractGSet G) X X')
  : Id (AbstractGSetIso H (agset_induce G H φ X) (agset_induce G H φ X'))
      (agset_path_to_iso H (agset_induce G H φ X) (agset_induce G H φ X') (refl (agset_induce G H φ) p))
      (agset_induce_iso G H φ X X' (agset_path_to_iso G X X' p))
  ≔ agset_iso_path H (agset_induce G H φ X) (agset_induce G H φ X')
      (agset_path_to_iso H (agset_induce G H φ X) (agset_induce G H φ X') (refl (agset_induce G H φ) p))
      (agset_induce_iso G H φ X X' (agset_path_to_iso G X X' p))
      (agset_induce_ap_map G H φ X X' p)
