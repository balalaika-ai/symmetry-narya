export "800-semidirect-products"
export "801-path-pair-sections"
export "403-abstract-groups"

{` Chapter 8 (congp.tex), sec:Semidirect-products, lines 266–289 and
   312–325: the symmetries of G ⋉ H as pairs, the action q' ↦ q'^p of
   USym G on USym H(sh_G), the multiplication formula
   (p', q') · (p, q) = (p' · p, (q'^p) · q), and the abstract group it
   defines. The results of module 801 are applied with X ≔ BG,
   Y(t) ≔ BH(t) and the section f(t) ≔ sh_{H(t)}, at x ≡ x' ≡ x'' ≡ sh_G.

   Book order: usym_mul G p' p = p' · p (first p, then p'). `}

{` def:pathsectionaction for G ⋉ H: q'^p for p : USym G and q' : USym H(sh_G). `}
def semidirect_loop_action (G : Group) (H : BG G .carrier → Group) (p : USym G) (q' : USym (H (shape G)))
  : USym (H (shape G))
  ≔ section_loop_action (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G) p q'

def semidirect_loop_action_unit (G : Group) (H : BG G .carrier → Group) (q' : USym (H (shape G)))
  : Id (USym (H (shape G))) (semidirect_loop_action G H (usym_unit G) q') q'
  ≔ section_loop_action_refl (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) q'

{` def:pathsectionactionassoc for G ⋉ H: (q^{p'})^p = q^{p'·p}. `}
def semidirect_loop_action_mul (G : Group) (H : BG G .carrier → Group) (p p' : USym G) (q : USym (H (shape G)))
  : Id (USym (H (shape G))) (semidirect_loop_action G H p (semidirect_loop_action G H p' q))
      (semidirect_loop_action G H (usym_mul G p' p) q)
  ≔ section_loop_action_assoc (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G) p
      (shape G) p' q

{` Line 312: "we apply lem:pathpairsection to get a bijection
   USym(G ⋉ H) ≃ USym G × USym H". The map is e ↦ (e .fst, ...). `}
def semidirect_usym_equiv (G : Group) (H : BG G .carrier → Group)
  : Equiv (USym (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
  ≔ path_pair_section_equiv (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G)

def semidirect_usym_pair (G : Group) (H : BG G .carrier → Group) (e : USym (semidirect_product G H))
  : Product (USym G) (USym (H (shape G)))
  ≔ semidirect_usym_equiv G H .map e

def semidirect_usym_unpair (G : Group) (H : BG G .carrier → Group) (a : Product (USym G) (USym (H (shape G))))
  : USym (semidirect_product G H)
  ≔ equiv_inverse_map (USym (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_equiv G H) a

def semidirect_usym_pair_fst (G : Group) (H : BG G .carrier → Group) (e : USym (semidirect_product G H))
  : Id (USym G) (semidirect_usym_pair G H e .fst) (e .fst)
  ≔ refl (e .fst)

{` The multiplication formula (p', q') · (p, q) ≔ (p' · p, (q'^p) · q) on
   USym G × USym H(sh_G). `}
def semidirect_pair_mul (G : Group) (H : BG G .carrier → Group) (a' a : Product (USym G) (USym (H (shape G))))
  : Product (USym G) (USym (H (shape G)))
  ≔ (usym_mul G (a' .fst) (a .fst),
     usym_mul (H (shape G)) (semidirect_loop_action G H (a .fst) (a' .snd)) (a .snd))

{` lem:pathpairsectionmult for G ⋉ H: the bijection carries e' · e to the
   formula applied to the pairs of e' and e. `}
def semidirect_usym_mul (G : Group) (H : BG G .carrier → Group) (e' e : USym (semidirect_product G H))
  : Id (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_mul (semidirect_product G H) e' e))
      (semidirect_pair_mul G H (semidirect_usym_pair G H e') (semidirect_usym_pair G H e))
  ≔ path_pair_section_concat (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G) (shape G)
      e e'

{` Lines 313–318: the multiplication of USym(G ⋉ H) transported to
   USym G × USym H along the bijection is given by the formula. `}
def semidirect_transported_mul (G : Group) (H : BG G .carrier → Group) (a' a : Product (USym G) (USym (H (shape G))))
  : Product (USym G) (USym (H (shape G)))
  ≔ semidirect_usym_pair G H
      (usym_mul (semidirect_product G H) (semidirect_usym_unpair G H a') (semidirect_usym_unpair G H a))

def semidirect_transported_mul_formula (G : Group) (H : BG G .carrier → Group)
  (p' : USym G) (q' : USym (H (shape G))) (p : USym G) (q : USym (H (shape G)))
  : Id (Product (USym G) (USym (H (shape G)))) (semidirect_transported_mul G H (p', q') (p, q))
      (usym_mul G p' p, usym_mul (H (shape G)) (semidirect_loop_action G H p q') q)
  ≔ concat (Product (USym G) (USym (H (shape G)))) (semidirect_transported_mul G H (p', q') (p, q))
      (semidirect_pair_mul G H (semidirect_usym_pair G H (semidirect_usym_unpair G H (p', q')))
        (semidirect_usym_pair G H (semidirect_usym_unpair G H (p, q))))
      (usym_mul G p' p, usym_mul (H (shape G)) (semidirect_loop_action G H p q') q)
      (semidirect_usym_mul G H (semidirect_usym_unpair G H (p', q')) (semidirect_usym_unpair G H (p, q)))
      (refl (semidirect_pair_mul G H)
        (equiv_counit (USym (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
          (semidirect_usym_equiv G H) (p', q'))
        (equiv_counit (USym (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
          (semidirect_usym_equiv G H) (p, q)))

{` The symmetries USym p, USym s, USym j: p forgets the second component,
   s(p) ≔ (p, apd_f(p)) and j(q) ≔ (refl, q) (up to the conjugation by the
   reflexive pointing paths). `}
def semidirect_usym_projection (G : Group) (H : BG G .carrier → Group) (e : USym (semidirect_product G H))
  : Id (USym G) (usym_hom (semidirect_product G H) G (semidirect_projection G H) e) (semidirect_usym_pair G H e .fst)
  ≔ loop_conjugate_at_refl (BG G .carrier) (shape G) (e .fst)

def semidirect_usym_section (G : Group) (H : BG G .carrier → Group) (p : USym G)
  : Id (USym (semidirect_product G H)) (usym_hom G (semidirect_product G H) (semidirect_section G H) p)
      (p, refl ((t ↦ shape (H t)) : (t : BG G .carrier) → BG (H t) .carrier) p)
  ≔ loop_conjugate_at_refl (semidirect_classifying_type G H) (semidirect_shape G H)
      (p, refl ((t ↦ shape (H t)) : (t : BG G .carrier) → BG (H t) .carrier) p)

def semidirect_usym_inclusion (G : Group) (H : BG G .carrier → Group) (q : USym (H (shape G)))
  : Id (USym (semidirect_product G H)) (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q)
      (refl (shape G), q)
  ≔ loop_conjugate_at_refl (semidirect_classifying_type G H) (semidirect_shape G H) (refl (shape G), q)

def semidirect_usym_pair_section (G : Group) (H : BG G .carrier → Group) (p : USym G)
  : Id (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_hom G (semidirect_product G H) (semidirect_section G H) p))
      (p, usym_unit (H (shape G)))
  ≔ concat (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_hom G (semidirect_product G H) (semidirect_section G H) p))
      (semidirect_usym_pair G H (p, refl ((t ↦ shape (H t)) : (t : BG G .carrier) → BG (H t) .carrier) p))
      (p, usym_unit (H (shape G)))
      (refl (semidirect_usym_pair G H) (semidirect_usym_section G H p))
      (refl p, section_pathover_loop_apd (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G) p)

def semidirect_usym_pair_inclusion (G : Group) (H : BG G .carrier → Group) (q : USym (H (shape G)))
  : Id (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q))
      (usym_unit G, q)
  ≔ concat (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q))
      (semidirect_usym_pair G H (refl (shape G), q))
      (usym_unit G, q)
      (refl (semidirect_usym_pair G H) (semidirect_usym_inclusion G H q))
      (refl (refl (shape G)),
       section_pathover_loop_refl (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) q)

{` Every symmetry of G ⋉ H is s(p) · j(q) for a unique pair (p, q): the
   pair of s(p) · j(q) is (p, q). `}
def semidirect_pair_of_mul (G : Group) (H : BG G .carrier → Group) (e' e : USym (semidirect_product G H))
  : Product (USym G) (USym (H (shape G)))
  ≔ semidirect_usym_pair G H (usym_mul (semidirect_product G H) e' e)

def semidirect_usym_split (G : Group) (H : BG G .carrier → Group) (p : USym G) (q : USym (H (shape G)))
  : Id (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_pair G H (usym_mul (semidirect_product G H)
        (usym_hom G (semidirect_product G H) (semidirect_section G H) p)
        (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q)))
      (p, q)
  ≔ concat (Product (USym G) (USym (H (shape G))))
      (semidirect_pair_of_mul G H (usym_hom G (semidirect_product G H) (semidirect_section G H) p)
        (usym_hom (H (shape G)) (semidirect_product G H) (semidirect_inclusion G H) q))
      (semidirect_pair_of_mul G H (p, refl ((t ↦ shape (H t)) : (t : BG G .carrier) → BG (H t) .carrier) p)
        (refl (shape G), q))
      (p, q)
      (refl (semidirect_pair_of_mul G H) (semidirect_usym_section G H p) (semidirect_usym_inclusion G H q))
      (path_pair_section_split (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G) (shape G) p q)

{` Transport of an abstract group structure along a bijection e : A ≃ S
   whose operations are compatible with e: the group laws on S come for
   free. Elements of S are first written as e(x) (sdp_equiv_ind). `}
def sdp_equiv_ind (A S : Type) (e : Equiv A S) (P : S → Type) (h : (a : A) → P (e .map a)) (s : S) : P s
  ≔ transport S P (e .map (equiv_inverse_map A S e s)) s (equiv_counit A S e s) (h (equiv_inverse_map A S e s))

def sdp_transported_unit_right (A : AbstractGroup) (S : Type) (e : Equiv (A .carrier) S) (u : S)
  (m : S → S → S) (hu : Id S (e .map (A .unit)) u)
  (hm : (x y : A .carrier) → Id S (e .map (A .mul x y)) (m (e .map x) (e .map y))) (x : A .carrier)
  : Id S (m (e .map x) u) (e .map x)
  ≔ calc
      m (e .map x) u = m (e .map x) (e .map (A .unit)) by refl (m (e .map x)) (inverse S (e .map (A .unit)) u hu)
      = e .map (A .mul x (A .unit))
        by inverse S (e .map (A .mul x (A .unit))) (m (e .map x) (e .map (A .unit))) (hm x (A .unit))
      = e .map x by refl (e .map) (A .laws .unit_right x) ∎

def sdp_transported_unit_left (A : AbstractGroup) (S : Type) (e : Equiv (A .carrier) S) (u : S)
  (m : S → S → S) (hu : Id S (e .map (A .unit)) u)
  (hm : (x y : A .carrier) → Id S (e .map (A .mul x y)) (m (e .map x) (e .map y))) (x : A .carrier)
  : Id S (m u (e .map x)) (e .map x)
  ≔ calc
      m u (e .map x) = m (e .map (A .unit)) (e .map x)
        by refl ((w ↦ m w (e .map x)) : S → S) (inverse S (e .map (A .unit)) u hu)
      = e .map (A .mul (A .unit) x)
        by inverse S (e .map (A .mul (A .unit) x)) (m (e .map (A .unit)) (e .map x)) (hm (A .unit) x)
      = e .map x by refl (e .map) (A .laws .unit_left x) ∎

def sdp_transported_assoc (A : AbstractGroup) (S : Type) (e : Equiv (A .carrier) S) (m : S → S → S)
  (hm : (x y : A .carrier) → Id S (e .map (A .mul x y)) (m (e .map x) (e .map y))) (x y z : A .carrier)
  : Id S (m (e .map x) (m (e .map y) (e .map z))) (m (m (e .map x) (e .map y)) (e .map z))
  ≔ calc
      m (e .map x) (m (e .map y) (e .map z)) = m (e .map x) (e .map (A .mul y z))
        by refl (m (e .map x)) (inverse S (e .map (A .mul y z)) (m (e .map y) (e .map z)) (hm y z))
      = e .map (A .mul x (A .mul y z))
        by inverse S (e .map (A .mul x (A .mul y z))) (m (e .map x) (e .map (A .mul y z))) (hm x (A .mul y z))
      = e .map (A .mul (A .mul x y) z) by refl (e .map) (A .laws .assoc x y z)
      = m (e .map (A .mul x y)) (e .map z) by hm (A .mul x y) z
      = m (m (e .map x) (e .map y)) (e .map z) by refl ((w ↦ m w (e .map z)) : S → S) (hm x y) ∎

def sdp_transported_inv_right (A : AbstractGroup) (S : Type) (e : Equiv (A .carrier) S) (u : S)
  (m : S → S → S) (i : S → S) (hu : Id S (e .map (A .unit)) u)
  (hm : (x y : A .carrier) → Id S (e .map (A .mul x y)) (m (e .map x) (e .map y)))
  (hi : (x : A .carrier) → Id S (e .map (A .inv x)) (i (e .map x))) (x : A .carrier)
  : Id S (m (e .map x) (i (e .map x))) u
  ≔ calc
      m (e .map x) (i (e .map x)) = m (e .map x) (e .map (A .inv x))
        by refl (m (e .map x)) (inverse S (e .map (A .inv x)) (i (e .map x)) (hi x))
      = e .map (A .mul x (A .inv x))
        by inverse S (e .map (A .mul x (A .inv x))) (m (e .map x) (e .map (A .inv x))) (hm x (A .inv x))
      = e .map (A .unit) by refl (e .map) (A .laws .inv_right x)
      = u by hu ∎

def sdp_transported_laws (A : AbstractGroup) (S : Type) (e : Equiv (A .carrier) S) (u : S)
  (m : S → S → S) (i : S → S) (hu : Id S (e .map (A .unit)) u)
  (hm : (x y : A .carrier) → Id S (e .map (A .mul x y)) (m (e .map x) (e .map y)))
  (hi : (x : A .carrier) → Id S (e .map (A .inv x)) (i (e .map x)))
  : AbstractGroupLaws S u m i
  ≔ (hlevel_two_to_set S
       (hlevel_equiv (suc. (suc. zero.)) (A .carrier) S e (set_to_hlevel_two (A .carrier) (A .laws .carrier_set))),
     sdp_equiv_ind (A .carrier) S e (s ↦ Id S (m s u) s) (sdp_transported_unit_right A S e u m hu hm),
     sdp_equiv_ind (A .carrier) S e (s ↦ Id S (m u s) s) (sdp_transported_unit_left A S e u m hu hm),
     s1 s2 s3 ↦ sdp_equiv_ind (A .carrier) S e (s1 ↦ Id S (m s1 (m s2 s3)) (m (m s1 s2) s3))
       (x ↦ sdp_equiv_ind (A .carrier) S e (s2 ↦ Id S (m (e .map x) (m s2 s3)) (m (m (e .map x) s2) s3))
         (y ↦ sdp_equiv_ind (A .carrier) S e
           (s3 ↦ Id S (m (e .map x) (m (e .map y) s3)) (m (m (e .map x) (e .map y)) s3))
           (z ↦ sdp_transported_assoc A S e m hm x y z) s3) s2) s1,
     sdp_equiv_ind (A .carrier) S e (s ↦ Id S (m s (i s)) u) (sdp_transported_inv_right A S e u m i hu hm hi))

{` Lines 319–322: "In a traditional algebra course ... this formula is used
   as the definition of the multiplication operation on USym G × USym H,
   but then one must prove that the operation satisfies the properties of
   def:abstractgroup." Here the laws are transported from abstr(G ⋉ H):
   the formula defines an abstract group, with unit (e, e) and the
   transported inverse, and the bijection is an abstract isomorphism
   abstr(G ⋉ H) ≅ (USym G × USym H, formula). `}
def semidirect_pair_unit (G : Group) (H : BG G .carrier → Group) : Product (USym G) (USym (H (shape G)))
  ≔ (usym_unit G, usym_unit (H (shape G)))

def semidirect_pair_inv (G : Group) (H : BG G .carrier → Group) (a : Product (USym G) (USym (H (shape G))))
  : Product (USym G) (USym (H (shape G)))
  ≔ semidirect_usym_pair G H (usym_inv (semidirect_product G H) (semidirect_usym_unpair G H a))

def semidirect_usym_pair_unit (G : Group) (H : BG G .carrier → Group)
  : Id (Product (USym G) (USym (H (shape G)))) (semidirect_usym_pair G H (usym_unit (semidirect_product G H)))
      (semidirect_pair_unit G H)
  ≔ (refl (usym_unit G),
     section_pathover_loop_refl (BG G .carrier) (t ↦ BG (H t) .carrier) (t ↦ shape (H t)) (shape G)
       (usym_unit (H (shape G))))

def semidirect_usym_pair_inv (G : Group) (H : BG G .carrier → Group) (e : USym (semidirect_product G H))
  : Id (Product (USym G) (USym (H (shape G)))) (semidirect_usym_pair G H (usym_inv (semidirect_product G H) e))
      (semidirect_pair_inv G H (semidirect_usym_pair G H e))
  ≔ refl ((d ↦ semidirect_usym_pair G H (usym_inv (semidirect_product G H) d))
        : USym (semidirect_product G H) → Product (USym G) (USym (H (shape G))))
      (inverse (USym (semidirect_product G H)) (semidirect_usym_unpair G H (semidirect_usym_pair G H e)) e
        (equiv_retraction (USym (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
          (semidirect_usym_equiv G H) e))

def semidirect_pair_laws (G : Group) (H : BG G .carrier → Group)
  : AbstractGroupLaws (Product (USym G) (USym (H (shape G)))) (semidirect_pair_unit G H) (semidirect_pair_mul G H)
      (semidirect_pair_inv G H)
  ≔ sdp_transported_laws (abstr (semidirect_product G H)) (Product (USym G) (USym (H (shape G))))
      (semidirect_usym_equiv G H) (semidirect_pair_unit G H) (semidirect_pair_mul G H) (semidirect_pair_inv G H)
      (semidirect_usym_pair_unit G H) (semidirect_usym_mul G H) (semidirect_usym_pair_inv G H)

def semidirect_abstract_group (G : Group) (H : BG G .carrier → Group) : AbstractGroup
  ≔ (Product (USym G) (USym (H (shape G))), semidirect_pair_unit G H, semidirect_pair_mul G H,
     semidirect_pair_inv G H, semidirect_pair_laws G H)

def semidirect_usym_abstract_hom (G : Group) (H : BG G .carrier → Group)
  : IsAbstractHom (abstr (semidirect_product G H)) (semidirect_abstract_group G H) (semidirect_usym_pair G H)
  ≔ e' e ↦ semidirect_usym_mul G H e' e

{` Litmus (trivial action). For H(t) ≡ K the action q'^p is trivial, the
   bijection of lem:pathpairsection is the bijection USym(G × K) ≃
   USym G × USym K of ex:productofgroups, and the formula is the
   componentwise multiplication of the product. `}
def section_pathover_loop_constant (X B : Type) (b : B) (x x' : X) (p : Id X x x') (r : Id B b b)
  : Id (Id B b b) (section_pathover_loop X (_ ↦ B) (_ ↦ b) x x' p r) r
  ≔ J X x (x' p ↦ (r : Id B b b) → Id (Id B b b) (section_pathover_loop X (_ ↦ B) (_ ↦ b) x x' p r) r)
      (r ↦ section_pathover_loop_refl X (_ ↦ B) (_ ↦ b) x r) x' p r

def semidirect_trivial_loop_action (G K : Group) (p : USym G) (q' : USym K)
  : Id (USym K) (semidirect_loop_action G (_ ↦ K) p q') q'
  ≔ section_loop_action_constant (BG G .carrier) (BG K .carrier) (shape K) (shape G) (shape G) p q'

def semidirect_trivial_usym_pair (G K : Group) (e : USym (semidirect_product G (_ ↦ K)))
  : Id (Product (USym G) (USym K)) (semidirect_usym_pair G (_ ↦ K) e) (product_group_usym_equiv G K .map e)
  ≔ (refl (e .fst),
     section_pathover_loop_constant (BG G .carrier) (BG K .carrier) (shape K) (shape G) (shape G) (e .fst) (e .snd))

def semidirect_trivial_pair_mul (G K : Group) (a' a : Product (USym G) (USym K))
  : Id (Product (USym G) (USym K)) (semidirect_pair_mul G (_ ↦ K) a' a)
      (usym_mul G (a' .fst) (a .fst), usym_mul K (a' .snd) (a .snd))
  ≔ (refl (usym_mul G (a' .fst) (a .fst)),
     refl ((r ↦ usym_mul K r (a .snd)) : USym K → USym K) (semidirect_trivial_loop_action G K (a .fst) (a' .snd)))

def product_group_usym_mul_components (G K : Group) (g h : USym (product_group G K))
  : Id (Product (USym G) (USym K)) (product_group_usym_equiv G K .map (usym_mul (product_group G K) g h))
      (usym_mul G (g .fst) (h .fst), usym_mul K (g .snd) (h .snd))
  ≔ refl (usym_mul G (g .fst) (h .fst), usym_mul K (g .snd) (h .snd))
