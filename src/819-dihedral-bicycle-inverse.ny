export "818-dihedral-bicycle-orbits"

{` The exercise at congp.tex:189: the book's inverse ψ of φ, and the
   verification that φ and ψ are inverse.

   For a bicycle (Y, a, b): S ≔ Y/a, X ≔ Y/b (orbit quotients), and, when
   every a-class α and b-class β intersect in a unique y'' (as subsets of Y:
   [y'']_a = α and [y'']_b = β), f_α(β) ≔ [a(y'')]_b. ψ(Y, a, b) ≔ (S, X, f).
   That S is a 2-element set and (X, f) lies in the component of the
   bidirectional cycle (X_S, f) are propositions; together with the unique
   intersection property they hold for φ(x) (x : BD_n): there
   (S × X)/a ≃ S, (S × X)/b ≃ X (module 818), the intersection of [(s,·)]_a and
   [(·,u)]_b is (s, u), and these equivalences identify ψ(φ(x)) with x. They
   are transported to the standard dihedral bicycle (= φ(sh)) and then to every
   bicycle of its component (the book: "S is a 2-element set, because it is
   so in the standard case").

   Results: ψ ∘ φ = id (dihedral_psi_phi, by the structure identity principle
   of module 815) and φ ∘ ψ = id (dihedral_phi_psi, using that φ is an
   equivalence, module 816), i.e. φ and ψ are inverse
   (dihedral_bicycle_inverse_equiv). `}

def PsiOrbitsA (B : Bicycles) : Type ≔ OrbitQuotient (bicycle_carrier B) (bicycle_a B)

def PsiOrbitsB (B : Bicycles) : Type ≔ OrbitQuotient (bicycle_carrier B) (bicycle_b B)

def psi_class_a (B : Bicycles) (y : bicycle_carrier B) : PsiOrbitsA B
  ≔ quotient_class (bicycle_carrier B) (orbit_relation (bicycle_carrier B) (bicycle_a B)) y

def psi_class_b (B : Bicycles) (y : bicycle_carrier B) : PsiOrbitsB B
  ≔ quotient_class (bicycle_carrier B) (orbit_relation (bicycle_carrier B) (bicycle_b B)) y

def psi_orbits_a_set (B : Bicycles) : SetTypes
  ≔ (PsiOrbitsA B, quotient_set (bicycle_carrier B) (orbit_relation (bicycle_carrier B) (bicycle_a B)))

def psi_orbits_b_set (B : Bicycles) : SetTypes
  ≔ (PsiOrbitsB B, quotient_set (bicycle_carrier B) (orbit_relation (bicycle_carrier B) (bicycle_b B)))

{` The elements of Y lying in both α and β. `}
def PsiIntersection (B : Bicycles) (α : PsiOrbitsA B) (β : PsiOrbitsB B) : Type
  ≔ Σ (bicycle_carrier B) (y ↦ Product (Id (PsiOrbitsA B) (psi_class_a B y) α) (Id (PsiOrbitsB B) (psi_class_b B y) β))

def PsiUniqueIntersections (B : Bicycles) : Type
  ≔ (α : PsiOrbitsA B) (β : PsiOrbitsB B) → BookIsContr (PsiIntersection B α β)

def psi_unique_intersections_prop (B : Bicycles) : isProp (PsiUniqueIntersections B)
  ≔ pi_prop (PsiOrbitsA B) (α ↦ (β : PsiOrbitsB B) → BookIsContr (PsiIntersection B α β))
      (α ↦ pi_prop (PsiOrbitsB B) (β ↦ BookIsContr (PsiIntersection B α β))
        (β ↦ book_iscontr_isprop (PsiIntersection B α β)))

{` f_α(β) ≔ [a(y'')]_b. `}
def psi_move (B : Bicycles) (ui : PsiUniqueIntersections B) (α : PsiOrbitsA B) (β : PsiOrbitsB B) : PsiOrbitsB B
  ≔ psi_class_b B (bicycle_a B .map (ui α β .center .fst))

def psi_frame (B : Bicycles) (ui : PsiUniqueIntersections B) : DFrame
  ≔ ((psi_orbits_a_set B, psi_orbits_b_set B), psi_move B ui)

def PsiProps (H : Subtypes Int) (h : IntegerSubgroupLaws H) (B : Bicycles) : Type
  ≔ Σ (PsiUniqueIntersections B) (ui ↦ DihedralFrameProps H h (psi_frame B ui))

def psi_props_prop (H : Subtypes Int) (h : IntegerSubgroupLaws H) (B : Bicycles) : isProp (PsiProps H h B)
  ≔ sigma_prop (PsiUniqueIntersections B) (ui ↦ DihedralFrameProps H h (psi_frame B ui))
      (psi_unique_intersections_prop B) (ui ↦ dihedral_frame_props_prop H h (psi_frame B ui))

{` Unique intersections, abstractly: if σ : QA ≃ S and g : QB ≃ X send the
   classes of (s, x) to s and x, then the intersection of α and β is the
   single element (σ α, g β). `}
def DpsIntersection (S X QA QB : Type) (clA : Product S X → QA) (clB : Product S X → QB) (α : QA) (β : QB) : Type
  ≔ Σ (Product S X) (y ↦ Product (Id QA (clA y) α) (Id QB (clB y) β))

def dps_abstract_center (S X QA QB : Type) (clA : Product S X → QA) (clB : Product S X → QB)
  (σ : Equiv QA S) (g : Equiv QB X)
  (hσ : (y : Product S X) → Id S (σ .map (clA y)) (y .fst)) (hg : (y : Product S X) → Id X (g .map (clB y)) (y .snd))
  (α : QA) (β : QB) : DpsIntersection S X QA QB clA clB α β
  ≔ let y : Product S X ≔ (σ .map α, g .map β) in
    (y,
     (calc
        clA y = equiv_inverse_map QA S σ (σ .map (clA y)) by equiv_unit QA S σ (clA y)
        = equiv_inverse_map QA S σ (σ .map α) by refl (equiv_inverse_map QA S σ) (hσ y)
        = α by equiv_retraction QA S σ α ∎,
      calc
        clB y = equiv_inverse_map QB X g (g .map (clB y)) by equiv_unit QB X g (clB y)
        = equiv_inverse_map QB X g (g .map β) by refl (equiv_inverse_map QB X g) (hg y)
        = β by equiv_retraction QB X g β ∎))

def dps_abstract_unique (S X QA QB : Type) (hA : isSet QA) (hB : isSet QB)
  (clA : Product S X → QA) (clB : Product S X → QB) (σ : Equiv QA S) (g : Equiv QB X)
  (hσ : (y : Product S X) → Id S (σ .map (clA y)) (y .fst)) (hg : (y : Product S X) → Id X (g .map (clB y)) (y .snd))
  (α : QA) (β : QB) : BookIsContr (DpsIntersection S X QA QB clA clB α β)
  ≔ (dps_abstract_center S X QA QB clA clB σ g hσ hg α β,
     w ↦ subtype_equal (Product S X) (y ↦ Product (Id QA (clA y) α) (Id QB (clB y) β))
       (y ↦ product_prop (Id QA (clA y) α) (Id QB (clB y) β) (hA (clA y) α) (hB (clB y) β))
       (dps_abstract_center S X QA QB clA clB σ g hσ hg α β) w
       (calc
          σ .map α = σ .map (clA (w .fst)) by refl (σ .map) (inverse QA (clA (w .fst)) α (w .snd .fst))
          = w .fst .fst by hσ (w .fst) ∎,
        calc
          g .map β = g .map (clB (w .fst)) by refl (g .map) (inverse QB (clB (w .fst)) β (w .snd .snd))
          = w .fst .snd by hg (w .fst) ∎))

def dps_unique_intersections (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : PsiUniqueIntersections (dihedral_bicycle H h x)
  ≔ dps_abstract_unique (two_set_carrier (x .fst)) (x .snd .fst .fst .fst) (DpsOrbitsA H h x) (DpsOrbitsB H h x)
      (quotient_set (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_a H h x)))
      (quotient_set (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_b H h x)))
      (quotient_class (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_a H h x)))
      (quotient_class (DpsProduct H h x) (orbit_relation (DpsProduct H h x) (dbc_b H h x)))
      (dihedral_orbits_a_equiv H h x) (dihedral_orbits_b_equiv H h x)
      (y ↦ refl (y .fst)) (y ↦ refl (y .snd))

def dps_center (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (α : DpsOrbitsA H h x) (β : DpsOrbitsB H h x) : PsiIntersection (dihedral_bicycle H h x) α β
  ≔ dps_unique_intersections H h x α β .center

{` g(f'_α β) = f_{σ α}(g β) for any choice of the unique-intersection proof. `}
def dps_commutes (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (ui : PsiUniqueIntersections (dihedral_bicycle H h x))
  : DFrameCommutes (DpsOrbitsA H h x) (DpsOrbitsB H h x) (two_set_carrier (x .fst)) (x .snd .fst .fst .fst)
      (psi_move (dihedral_bicycle H h x) ui) (x .snd .fst .snd)
      (dihedral_orbits_a_equiv H h x .map) (dihedral_orbits_b_equiv H h x .map)
  ≔ α β ↦ refl ((v ↦ x .snd .fst .snd (v .fst) (v .snd)) : DpsProduct H h x → x .snd .fst .fst .fst)
      (inverse (DpsProduct H h x) (dps_center H h x α β .fst) (ui α β .center .fst)
        (refl ((w ↦ w .fst) : PsiIntersection (dihedral_bicycle H h x) α β → DpsProduct H h x)
          (dps_unique_intersections H h x α β .contract (ui α β .center))))

{` The identification of the frame of ψ(φ(x)) with that of x. `}
def dps_frame_path (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  (ui : PsiUniqueIntersections (dihedral_bicycle H h x))
  : Id DFrame (psi_frame (dihedral_bicycle H h x) ui) (dbc_frame H h x)
  ≔ equiv_inverse_map (Id DFrame (psi_frame (dihedral_bicycle H h x) ui) (dbc_frame H h x))
      (DFrameIsos (psi_frame (dihedral_bicycle H h x) ui) (dbc_frame H h x))
      (dframe_paths_equiv (psi_frame (dihedral_bicycle H h x) ui) (dbc_frame H h x))
      ((dihedral_orbits_a_equiv H h x, dihedral_orbits_b_equiv H h x), dps_commutes H h x ui)

def dps_props_phi (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : PsiProps H h (dihedral_bicycle H h x)
  ≔ (dps_unique_intersections H h x,
     transport DFrame (DihedralFrameProps H h) (dbc_frame H h x)
       (psi_frame (dihedral_bicycle H h x) (dps_unique_intersections H h x))
       (inverse DFrame (psi_frame (dihedral_bicycle H h x) (dps_unique_intersections H h x)) (dbc_frame H h x)
         (dps_frame_path H h x (dps_unique_intersections H h x)))
       (x .fst .snd, x .snd .snd))

{` The standard case, and every bicycle of its component. `}
def dps_props_standard (H : Subtypes Int) (h : IntegerSubgroupLaws H) : PsiProps H h (dihedral_standard_bicycle H h)
  ≔ transport Bicycles (PsiProps H h) (dihedral_bicycle H h (dihedral_classifying_base H h)) (dihedral_standard_bicycle H h)
      (inverse Bicycles (dihedral_standard_bicycle H h) (dihedral_bicycle H h (dihedral_classifying_base H h))
        (dihedral_bicycle_base_path H h))
      (dps_props_phi H h (dihedral_classifying_base H h))

def dps_props (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h) : PsiProps H h (c .fst)
  ≔ mere_rec (Id Bicycles (dihedral_standard_bicycle H h) (c .fst)) (PsiProps H h (c .fst)) (psi_props_prop H h (c .fst))
      (p ↦ transport Bicycles (PsiProps H h) (dihedral_standard_bicycle H h) (c .fst) p (dps_props_standard H h))
      (c .snd)

{` ψ(Y, a, b) ≔ (Y/a, Y/b, f). `}
def dihedral_bicycle_psi (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  : DihedralClassifyingType H h
  ≔ dbc_ungroup H h (psi_frame (c .fst) (dps_props H h c .fst), dps_props H h c .snd)

{` Litmus: the components of ψ are the book's S = Y/a, X = Y/b and
   f_{[y]_a}([y']_b) = [a(y'')]_b. `}
def dihedral_bicycle_psi_parts (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  : Id (Product SetTypes SetTypes) (dihedral_bicycle_psi H h c .fst .fst, dihedral_bicycle_psi H h c .snd .fst .fst)
      (psi_orbits_a_set (c .fst), psi_orbits_b_set (c .fst))
  ≔ refl ((psi_orbits_a_set (c .fst), psi_orbits_b_set (c .fst)) : Product SetTypes SetTypes)

def dihedral_bicycle_psi_move (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  (y y' : bicycle_carrier (c .fst))
  : Id (PsiOrbitsB (c .fst)) (dihedral_bicycle_psi H h c .snd .fst .snd (psi_class_a (c .fst) y) (psi_class_b (c .fst) y'))
      (psi_class_b (c .fst) (bicycle_a (c .fst) .map
        (dps_props H h c .fst (psi_class_a (c .fst) y) (psi_class_b (c .fst) y') .center .fst)))
  ≔ refl (psi_class_b (c .fst) (bicycle_a (c .fst) .map
        (dps_props H h c .fst (psi_class_a (c .fst) y) (psi_class_b (c .fst) y') .center .fst)))

{` ψ ∘ φ = id. `}
def dihedral_psi_phi (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : Id (DihedralClassifyingType H h) (dihedral_bicycle_psi H h (dihedral_bicycle_map H h x)) x
  ≔ let pr ≔ dps_props H h (dihedral_bicycle_map H h x) in
    refl (dbc_ungroup H h)
      (subtype_equal DFrame (DihedralFrameProps H h) (dihedral_frame_props_prop H h)
        (psi_frame (dihedral_bicycle H h x) (pr .fst), pr .snd) (dbc_regroup H h x)
        (dps_frame_path H h x (pr .fst)))

{` φ ∘ ψ = id (φ being an equivalence, ψ is its inverse). `}
def dihedral_phi_psi (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  : Id (DihedralBicycleComponent H h) (dihedral_bicycle_map H h (dihedral_bicycle_psi H h c)) c
  ≔ let A ≔ DihedralClassifyingType H h in
    let C ≔ DihedralBicycleComponent H h in
    let w ≔ dihedral_bicycle_equiv H h .equiv c .center in
    let q : Id A (dihedral_bicycle_psi H h c) (w .fst)
          ≔ concat A (dihedral_bicycle_psi H h c) (dihedral_bicycle_psi H h (dihedral_bicycle_map H h (w .fst))) (w .fst)
              (refl (dihedral_bicycle_psi H h) (w .snd)) (dihedral_psi_phi H h (w .fst)) in
    concat C (dihedral_bicycle_map H h (dihedral_bicycle_psi H h c)) (dihedral_bicycle_map H h (w .fst)) c
      (refl (dihedral_bicycle_map H h) q) (inverse C c (dihedral_bicycle_map H h (w .fst)) (w .snd))

{` The exercise: φ and ψ are inverse equivalences. `}
def dihedral_bicycle_inverse_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DihedralClassifyingType H h) (DihedralBicycleComponent H h)
  ≔ quasi_inverse_equiv (DihedralClassifyingType H h) (DihedralBicycleComponent H h)
      (dihedral_bicycle_map H h) (dihedral_bicycle_psi H h) (dihedral_psi_phi H h) (dihedral_phi_psi H h)

{` For an order n: ψ : Bicyc_(standard) → BD_n inverse to φ. `}
def bidirectional_bicycle_inverse (n : Order)
  : Product ((x : BG (generalized_dihedral_group n) .carrier)
               → Id (BG (generalized_dihedral_group n) .carrier)
                   (dihedral_bicycle_psi (order_periods n) (order_subgroup_laws n)
                     (bidirectional_bicycle_pointed_equiv n .fst .fst x)) x)
            ((c : NativeComponent Bicycles (standard_dihedral_bicycle n))
               → Id (NativeComponent Bicycles (standard_dihedral_bicycle n))
                   (bidirectional_bicycle_pointed_equiv n .fst .fst
                     (dihedral_bicycle_psi (order_periods n) (order_subgroup_laws n) c)) c)
  ≔ (dihedral_psi_phi (order_periods n) (order_subgroup_laws n), dihedral_phi_psi (order_periods n) (order_subgroup_laws n))

{` Implementation, lines 174-176: S = Y/a is a 2-element set and X = Y/b is
   merely equivalent to Z/~n, for every bicycle of the component. `}
def dihedral_psi_orbits_a_two (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  : Mere (Id SetTypes (dihedral_two_shape .fst) (psi_orbits_a_set (c .fst)))
  ≔ dps_props H h c .snd .fst

def dihedral_psi_orbits_b_mere_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (c : DihedralBicycleComponent H h)
  : Mere (Equiv (PsiOrbitsB (c .fst)) (SubgroupQuotient H h))
  ≔ let S' : TwoElementSets ≔ (psi_orbits_a_set (c .fst), dps_props H h c .snd .fst) in
    let M ≔ Mere (Equiv (PsiOrbitsB (c .fst)) (SubgroupQuotient H h)) in
    mere_rec (Id (S2C3Type S') (dihedral_point S' H h) (psi_orbits_b_set (c .fst), psi_move (c .fst) (dps_props H h c .fst)))
      M (mere_isprop (Equiv (PsiOrbitsB (c .fst)) (SubgroupQuotient H h)))
      (p ↦ mere_rec (two_set_carrier S') M (mere_isprop (Equiv (PsiOrbitsB (c .fst)) (SubgroupQuotient H h)))
        (s ↦ mere (Equiv (PsiOrbitsB (c .fst)) (SubgroupQuotient H h))
          (compose_equiv (PsiOrbitsB (c .fst)) (DihedralCycleSet S' H h) (SubgroupQuotient H h)
            (canonical_inverse_equiv (DihedralCycleSet S' H h) (PsiOrbitsB (c .fst))
              (transport_univalence_equiv (DihedralCycleSet S' H h) (PsiOrbitsB (c .fst)) .map (p .fst .fst)))
            (dihedral_eval_equiv S' H h s)))
        (dihedral_two_set_mere S'))
      (dps_props H h c .snd .snd)
