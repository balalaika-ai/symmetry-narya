export "1303-two-element-field"
export "702-abstract-group-identity"

{` Chapter 13, section "the general linear group as automorphism group"
   (fields.tex 1303; the section has a title only). Identifications of
   modules (vector spaces) are linear isomorphisms (structure identity
   principle, proved exactly like rem:abs-iso in module 702), so the type of
   R-modules is a groupoid and GL(V) ≔ Aut_{Mod_R}(V) is a group whose
   symmetries are the linear automorphisms of V. For a field K this is the
   general linear group of a K-vector space. `}

def LinearIso (R : AbstractRing) (V W : RingModule R) : Type
  ≔ Σ (Equiv (V .carrier) (W .carrier)) (f ↦
      Product (IsAbstractHom (module_group R V) (module_group R W) (f .map)) (IsLinear R V W (f .map)))

def linear_iso_structure_prop (R : AbstractRing) (V W : RingModule R) (f : V .carrier → W .carrier)
  : isProp (Product (IsAbstractHom (module_group R V) (module_group R W) f) (IsLinear R V W f))
  ≔ product_prop (IsAbstractHom (module_group R V) (module_group R W) f) (IsLinear R V W f)
      (is_abstract_hom_prop (module_group R V) (module_group R W) f) (is_linear_prop R V W f)

def linear_iso_path (R : AbstractRing) (V W : RingModule R) (φ ψ : LinearIso R V W)
  (h : Id (V .carrier → W .carrier) (φ .fst .map) (ψ .fst .map)) : Id (LinearIso R V W) φ ψ
  ≔ subtype_equal (Equiv (V .carrier) (W .carrier))
      (f ↦ Product (IsAbstractHom (module_group R V) (module_group R W) (f .map)) (IsLinear R V W (f .map)))
      (f ↦ linear_iso_structure_prop R V W (f .map)) φ ψ
      (equiv_path (V .carrier) (W .carrier) (φ .fst) (ψ .fst) h)

def linear_iso_set (R : AbstractRing) (V W : RingModule R) : isSet (LinearIso R V W)
  ≔ sigma_set (Equiv (V .carrier) (W .carrier))
      (f ↦ Product (IsAbstractHom (module_group R V) (module_group R W) (f .map)) (IsLinear R V W (f .map)))
      (equivalences_set (V .carrier) (W .carrier) (module_set R W))
      (f ↦ prop_is_set (Product (IsAbstractHom (module_group R V) (module_group R W) (f .map)) (IsLinear R V W (f .map)))
        (linear_iso_structure_prop R V W (f .map)))

def linear_iso_map (R : AbstractRing) (V W : RingModule R) (φ : LinearIso R V W) : LinearMap R V W
  ≔ ((φ .fst .map, φ .snd .fst), φ .snd .snd)

{` The data of a module (carrier, 0, +, -, scalar multiplication) and the
   laws as one family of propositions over the data. `}
def ModuleData (R : AbstractRing) : Type
  ≔ Σ Type (S ↦ Σ S (z ↦ Σ (S → S → S) (ad ↦ Σ (S → S) (ng ↦ R .carrier → S → S))))

def module_data (R : AbstractRing) (V : RingModule R) : ModuleData R
  ≔ (V .carrier, (V .zero, (V .add, (V .neg, V .smul))))

def ModuleLawsAt (R : AbstractRing) (d : ModuleData R) : Type
  ≔ let S ≔ d .fst in let z ≔ d .snd .fst in let ad ≔ d .snd .snd .fst in
    let ng ≔ d .snd .snd .snd .fst in let sm ≔ d .snd .snd .snd .snd in
    Product (AbstractGroupLaws S z ad ng)
      (Product ((v w : S) → Id S (ad v w) (ad w v))
        (Product ((v : S) → Id S (sm (R .one) v) v)
          (Product ((a b : R .carrier) (v : S) → Id S (sm (R .mul a b) v) (sm a (sm b v)))
            (Product ((a b : R .carrier) (v : S) → Id S (sm (R .add a b) v) (ad (sm a v) (sm b v)))
              ((a : R .carrier) (v w : S) → Id S (sm a (ad v w)) (ad (sm a v) (sm a w)))))))

def module_laws (R : AbstractRing) (V : RingModule R) : ModuleLawsAt R (module_data R V)
  ≔ (V .add_laws, (V .add_comm, (V .smul_one, (V .smul_mul, (V .smul_add_scalar, V .smul_add_vector)))))

def module_laws_prop (R : AbstractRing) (d : ModuleData R) : isProp (ModuleLawsAt R d)
  ≔ let S ≔ d .fst in let z ≔ d .snd .fst in let ad ≔ d .snd .snd .fst in
    let ng ≔ d .snd .snd .snd .fst in let sm ≔ d .snd .snd .snd .snd in
    let K ≔ R .carrier in
    u v ↦ let hS ≔ u .fst .carrier_set in
    (abstract_group_laws_prop S z ad ng (u .fst) (v .fst),
     (pi_prop S (x ↦ (y : S) → Id S (ad x y) (ad y x))
        (x ↦ pi_prop S (y ↦ Id S (ad x y) (ad y x)) (y ↦ hS (ad x y) (ad y x)))
        (u .snd .fst) (v .snd .fst),
      (pi_prop S (x ↦ Id S (sm (R .one) x) x) (x ↦ hS (sm (R .one) x) x) (u .snd .snd .fst) (v .snd .snd .fst),
       (pi_prop K (a ↦ (b : K) (x : S) → Id S (sm (R .mul a b) x) (sm a (sm b x)))
          (a ↦ pi_prop K (b ↦ (x : S) → Id S (sm (R .mul a b) x) (sm a (sm b x)))
            (b ↦ pi_prop S (x ↦ Id S (sm (R .mul a b) x) (sm a (sm b x)))
              (x ↦ hS (sm (R .mul a b) x) (sm a (sm b x)))))
          (u .snd .snd .snd .fst) (v .snd .snd .snd .fst),
        (pi_prop K (a ↦ (b : K) (x : S) → Id S (sm (R .add a b) x) (ad (sm a x) (sm b x)))
           (a ↦ pi_prop K (b ↦ (x : S) → Id S (sm (R .add a b) x) (ad (sm a x) (sm b x)))
             (b ↦ pi_prop S (x ↦ Id S (sm (R .add a b) x) (ad (sm a x) (sm b x)))
               (x ↦ hS (sm (R .add a b) x) (ad (sm a x) (sm b x)))))
           (u .snd .snd .snd .snd .fst) (v .snd .snd .snd .snd .fst),
         pi_prop K (a ↦ (x y : S) → Id S (sm a (ad x y)) (ad (sm a x) (sm a y)))
           (a ↦ pi_prop S (x ↦ (y : S) → Id S (sm a (ad x y)) (ad (sm a x) (sm a y)))
             (x ↦ pi_prop S (y ↦ Id S (sm a (ad x y)) (ad (sm a x) (sm a y)))
               (y ↦ hS (sm a (ad x y)) (ad (sm a x) (sm a y)))))
           (u .snd .snd .snd .snd .snd) (v .snd .snd .snd .snd .snd))))))

def module_laws_pathover (R : AbstractRing) (d d' : ModuleData R) (q : Id (ModuleData R) d d')
  (l : ModuleLawsAt R d) (l' : ModuleLawsAt R d') : Id (ModuleLawsAt R) q l l'
  ≔ pathover_hlevel zero. (ModuleData R) (ModuleLawsAt R)
      (d ↦ prop_to_hlevel_one (ModuleLawsAt R d) (module_laws_prop R d)) d d' q l l' .center

def module_path_of_data (R : AbstractRing) (V W : RingModule R)
  (q : Id (ModuleData R) (module_data R V) (module_data R W)) : Id (RingModule R) V W
  ≔ let L ≔ module_laws_pathover R (module_data R V) (module_data R W) q (module_laws R V) (module_laws R W) in
    (q .fst, q .snd .fst, q .snd .snd .fst, q .snd .snd .snd .fst, L .fst, L .snd .fst,
     q .snd .snd .snd .snd, L .snd .snd .fst, L .snd .snd .snd .fst, L .snd .snd .snd .snd .fst,
     L .snd .snd .snd .snd .snd)

{` The data identification over ua(f) for a linear isomorphism f. `}
def module_data_path_from_iso (R : AbstractRing) (V W : RingModule R) (φ : LinearIso R V W)
  : Id (ModuleData R) (module_data R V) (module_data R W)
  ≔ let S ≔ V .carrier in let T ≔ W .carrier in let f ≔ φ .fst in let hf ≔ φ .snd .fst in
    let G ≔ module_group R V in let H ≔ module_group R W in
    (ua S T f,
     ((unglue ≔ abstract_hom_preserves_unit G H (f .map) hf),
      (x y ⤇ (unglue ≔ concat T (f .map (V .add x.0 y.0)) (W .add (f .map x.0) (f .map y.0)) (W .add x.1 y.1)
                (hf x.0 y.0) (refl (W .add) (x.2 .unglue) (y.2 .unglue))),
       (x ⤇ (unglue ≔ concat T (f .map (V .neg x.0)) (W .neg (f .map x.0)) (W .neg x.1)
                (abstract_hom_preserves_inv G H (f .map) hf x.0) (refl (W .neg) (x.2 .unglue))),
        a x ⤇ (unglue ≔ concat T (f .map (V .smul a.0 x.0)) (W .smul a.0 (f .map x.0)) (W .smul a.1 x.1)
                (φ .snd .snd a.0 x.0) (refl (W .smul) a.2 (x.2 .unglue)))))))

def module_path_from_iso (R : AbstractRing) (V W : RingModule R) (φ : LinearIso R V W) : Id (RingModule R) V W
  ≔ module_path_of_data R V W (module_data_path_from_iso R V W φ)

{` Transport along the carrier of an identification is a linear iso. `}
def module_path_to_iso (R : AbstractRing) (V W : RingModule R) (p : Id (RingModule R) V W) : LinearIso R V W
  ≔ let P ≔ p .carrier in let S ≔ V .carrier in let T ≔ W .carrier in
    (transport_equiv S T P,
     (s s' ↦ type_pathover_transport S T P (V .add s s') (W .add (P .trr s) (P .trr s'))
        (p .add (P .liftr s) (P .liftr s')),
      a s ↦ type_pathover_transport S T P (V .smul a s) (W .smul a (P .trr s))
        (p .smul (refl a) (P .liftr s))))

def module_iso_path_section (R : AbstractRing) (V W : RingModule R) (φ : LinearIso R V W)
  : Id (LinearIso R V W) (module_path_to_iso R V W (module_path_from_iso R V W φ)) φ
  ≔ linear_iso_path R V W (module_path_to_iso R V W (module_path_from_iso R V W φ)) φ (refl (φ .fst .map))

def module_iso_total_contractible (R : AbstractRing) (V : RingModule R) : isContr (Σ (RingModule R) (LinearIso R V))
  ≔ contractible_retract (Σ (RingModule R) (W ↦ Id (RingModule R) V W)) (Σ (RingModule R) (LinearIso R V))
      (iscontr_idfrom (RingModule R) V)
      (totalize (RingModule R) (W ↦ Id (RingModule R) V W) (LinearIso R V) (module_path_to_iso R V))
      (totalize (RingModule R) (LinearIso R V) (W ↦ Id (RingModule R) V W) (module_path_from_iso R V))
      (u ↦ (refl (u .fst), module_iso_path_section R V (u .fst) (u .snd)))

def module_path_to_iso_is_equiv (R : AbstractRing) (V W : RingModule R)
  : isEquiv (Id (RingModule R) V W) (LinearIso R V W) (module_path_to_iso R V W)
  ≔ fiberwise_from_total (RingModule R) (W ↦ Id (RingModule R) V W) (LinearIso R V) (module_path_to_iso R V)
      (cat_contractible_map_is_equiv (Σ (RingModule R) (W ↦ Id (RingModule R) V W)) (Σ (RingModule R) (LinearIso R V))
        (totalize (RingModule R) (W ↦ Id (RingModule R) V W) (LinearIso R V) (module_path_to_iso R V))
        (iscontr_idfrom (RingModule R) V) (module_iso_total_contractible R V)) W

{` (V = W) ≃ linear isomorphisms V ≅ W. `}
def module_path_iso_equiv (R : AbstractRing) (V W : RingModule R) : Equiv (Id (RingModule R) V W) (LinearIso R V W)
  ≔ (module_path_to_iso R V W, module_path_to_iso_is_equiv R V W)

def module_paths_set (R : AbstractRing) (V W : RingModule R) : isSet (Id (RingModule R) V W)
  ≔ hlevel_two_to_set (Id (RingModule R) V W)
      (hlevel_equiv (suc. (suc. zero.)) (LinearIso R V W) (Id (RingModule R) V W)
        (canonical_inverse_equiv (Id (RingModule R) V W) (LinearIso R V W) (module_path_iso_equiv R V W))
        (set_to_hlevel_two (LinearIso R V W) (linear_iso_set R V W)))

def module_groupoid (R : AbstractRing) : isGroupoid (RingModule R) ≔ V W ↦ module_paths_set R V W

{` GL(V) ≔ Aut_{Mod_R}(V), the automorphism group of V in the groupoid of
   R-modules; for a field K and a K-vector space V this is the general
   linear group. Its symmetries are the linear automorphisms of V. `}
def general_linear_group (R : AbstractRing) (V : RingModule R) : Group
  ≔ automorphism_group (RingModule R) (module_groupoid R) V

def vector_space_general_linear_group (K : Field) (V : VectorSpace K) : Group ≔ general_linear_group (K .fst) V

def general_linear_usym_equiv (R : AbstractRing) (V : RingModule R)
  : Equiv (USym (general_linear_group R V)) (LinearIso R V V)
  ≔ compose_equiv (USym (general_linear_group R V)) (Id (RingModule R) V V) (LinearIso R V V)
      (automorphism_group_usym_equiv (RingModule R) (module_groupoid R) V)
      (module_path_iso_equiv R V V)

{` The symmetry of GL(V) given by a linear automorphism φ; transport along
   it is φ by computation (litmus for the direction of the equivalence). `}
def general_linear_symmetry (R : AbstractRing) (V : RingModule R) (φ : LinearIso R V V)
  : USym (general_linear_group R V)
  ≔ component_path (RingModule R) V (component_point (RingModule R) V) (component_point (RingModule R) V)
      (module_path_from_iso R V V φ)

def general_linear_symmetry_transport (R : AbstractRing) (V : RingModule R) (φ : LinearIso R V V) (v : V .carrier)
  : Id (V .carrier) (general_linear_symmetry R V φ .fst .carrier .trr v) (φ .fst .map v)
  ≔ refl (φ .fst .map v)

{` Litmus: negation v ↦ -v is a linear automorphism of every module. `}
def module_negation_iso (R : AbstractRing) (V : RingModule R) : LinearIso R V V
  ≔ let G ≔ module_group R V in let S ≔ V .carrier in
    (quasi_inverse_equiv S S (V .neg) (V .neg) (x ↦ ag_inv_inv G x) (x ↦ ag_inv_inv G x),
     (s s' ↦ concat S (V .neg (V .add s s')) (V .add (V .neg s') (V .neg s)) (V .add (V .neg s) (V .neg s'))
        (ag_inv_mul G s s') (V .add_comm (V .neg s') (V .neg s)),
      a s ↦ inverse S (V .smul a (V .neg s)) (V .neg (V .smul a s))
       (ag_inv_unique_right G (V .smul a s) (V .smul a (V .neg s))
        (calc
           V .add (V .smul a s) (V .smul a (V .neg s)) = V .smul a (V .add s (V .neg s))
             by inverse S (V .smul a (V .add s (V .neg s))) (V .add (V .smul a s) (V .smul a (V .neg s)))
               (V .smul_add_vector a s (V .neg s))
           = V .smul a (V .zero) by refl (V .smul a) (V .add_laws .inv_right s)
           = V .zero by smul_zero_vector R V a ∎))))
