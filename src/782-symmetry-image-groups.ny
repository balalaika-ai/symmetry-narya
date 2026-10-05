export "701-abstract-homomorphisms"

{` Groups of symmetries of a set given as the image of a family; used for
   the "a priori different map from heaps to groups" of sec:heaps
   (absgroup.tex 1371-1389, module 783).

   Data (SymmetryImageData S): a set S, an abstract group G acting on S by
   φ : G → (S ≃ S) with φ(g·h) = φ(g) ∘ φ(h) pointwise, and a merely
   surjective family σ : I → G. The symmetries of S of the form φ(σ(i)),
   i.e. the image of i ↦ φ(σ(i)) in S ≃ S, form an abstract group under
   composition: e · d ≔ e ∘ d (first d, as in Σ_S), unit id, inverse e⁻¹
   (symmetry_image_group). If φ is injective, φ is an isomorphism from G
   onto this group (symmetry_image_iso). `}

def SymmetryImageData (S : Type) : Type ≔ sig (
  set : isSet S,
  group : AbstractGroup,
  act : group .carrier → Equiv S S,
  act_mul : (g h : group .carrier) (x : S) → Id S (act (group .mul g h) .map x) (act g .map (act h .map x)),
  index : Type,
  family : index → group .carrier,
  family_surjective : Surjective index (group .carrier) family)

def symmetry_image_map (S : Type) (D : SymmetryImageData S) (i : D .index) : Equiv S S
  ≔ D .act (D .family i)

def SymmetryImage (S : Type) (D : SymmetryImageData S) : Type
  ≔ Image (D .index) (Equiv S S) (symmetry_image_map S D)

def SymmetryImageWitness (S : Type) (D : SymmetryImageData S) (e : Equiv S S) : Type
  ≔ Mere (BookFiber (D .index) (Equiv S S) (symmetry_image_map S D) e)

def symmetry_image_witness_prop (S : Type) (D : SymmetryImageData S) (e : Equiv S S)
  : isProp (SymmetryImageWitness S D e)
  ≔ mere_isprop (BookFiber (D .index) (Equiv S S) (symmetry_image_map S D) e)

{` Elements of the image are equal when their maps agree pointwise. `}
def symmetry_image_path (S : Type) (D : SymmetryImageData S) (u v : SymmetryImage S D)
  (h : (x : S) → Id S (u .fst .map x) (v .fst .map x))
  : Id (SymmetryImage S D) u v
  ≔ subtype_equal (Equiv S S) (SymmetryImageWitness S D) (symmetry_image_witness_prop S D) u v
      (equiv_homotopy S S (u .fst) (v .fst) h)

def symmetry_image_set (S : Type) (D : SymmetryImageData S) : isSet (SymmetryImage S D)
  ≔ sigma_set (Equiv S S) (SymmetryImageWitness S D) (equivalences_set S S (D .set))
      (e ↦ prop_is_set (SymmetryImageWitness S D e) (symmetry_image_witness_prop S D e))

{` A symmetry pointwise equal to some φ(g) is in the image, since σ is
   merely surjective. `}
def symmetry_image_witness (S : Type) (D : SymmetryImageData S) (e : Equiv S S) (g : D .group .carrier)
  (h : (x : S) → Id S (e .map x) (D .act g .map x))
  : SymmetryImageWitness S D e
  ≔ mere_rec (BookFiber (D .index) (D .group .carrier) (D .family) g) (SymmetryImageWitness S D e)
      (symmetry_image_witness_prop S D e)
      (w ↦ mere (BookFiber (D .index) (Equiv S S) (symmetry_image_map S D) e)
        (w .fst, equiv_homotopy S S e (symmetry_image_map S D (w .fst))
          (x ↦ concat S (e .map x) (D .act g .map x) (D .act (D .family (w .fst)) .map x) (h x)
            (refl ((k ↦ D .act k .map x) : D .group .carrier → S) (w .snd)))))
      (D .family_surjective g)

{` φ(e) = id and φ(g⁻¹) = φ(g)⁻¹, pointwise (from the multiplicativity of φ
   and the group laws). `}
def symmetry_act_unit (S : Type) (D : SymmetryImageData S) (x : S)
  : Id S (D .act (D .group .unit) .map x) x
  ≔ let G ≔ D .group in
    let e ≔ D .act (G .unit) in
    let y ≔ equiv_inverse_map S S e x in
    calc
      e .map x = e .map (e .map y) by refl (e .map) (inverse S (e .map y) x (equiv_counit S S e x))
      = D .act (G .mul (G .unit) (G .unit)) .map y
        by inverse S (D .act (G .mul (G .unit) (G .unit)) .map y) (e .map (e .map y)) (D .act_mul (G .unit) (G .unit) y)
      = e .map y by refl ((k ↦ D .act k .map y) : G .carrier → S) (G .laws .unit_right (G .unit))
      = x by equiv_counit S S e x ∎

def symmetry_act_inv_left (S : Type) (D : SymmetryImageData S) (g : D .group .carrier) (x : S)
  : Id S (D .act (D .group .inv g) .map (D .act g .map x)) x
  ≔ let G ≔ D .group in
    calc
      D .act (G .inv g) .map (D .act g .map x) = D .act (G .mul (G .inv g) g) .map x
        by inverse S (D .act (G .mul (G .inv g) g) .map x) (D .act (G .inv g) .map (D .act g .map x))
          (D .act_mul (G .inv g) g x)
      = D .act (G .unit) .map x by refl ((k ↦ D .act k .map x) : G .carrier → S) (ag_inv_left G g)
      = x by symmetry_act_unit S D x ∎

def symmetry_act_inverse_map (S : Type) (D : SymmetryImageData S) (g : D .group .carrier) (y : S)
  : Id S (equiv_inverse_map S S (D .act g) y) (D .act (D .group .inv g) .map y)
  ≔ let G ≔ D .group in
    let ig ≔ equiv_inverse_map S S (D .act g) in
    calc
      ig y = D .act (G .inv g) .map (D .act g .map (ig y))
        by inverse S (D .act (G .inv g) .map (D .act g .map (ig y))) (ig y) (symmetry_act_inv_left S D g (ig y))
      = D .act (G .inv g) .map y by refl (D .act (G .inv g) .map) (equiv_counit S S (D .act g) y) ∎

{` The group operations on the image. `}
def symmetry_image_unit (S : Type) (D : SymmetryImageData S) : SymmetryImage S D
  ≔ (identity_equiv S,
     symmetry_image_witness S D (identity_equiv S) (D .group .unit)
       (x ↦ inverse S (D .act (D .group .unit) .map x) x (symmetry_act_unit S D x)))

def symmetry_image_mul (S : Type) (D : SymmetryImageData S) (u v : SymmetryImage S D) : SymmetryImage S D
  ≔ let I ≔ D .index in
    let G ≔ D .group in
    let f ≔ symmetry_image_map S D in
    let e ≔ compose_equiv S S S (v .fst) (u .fst) in
    (e,
     mere_rec (BookFiber I (Equiv S S) f (u .fst)) (SymmetryImageWitness S D e) (symmetry_image_witness_prop S D e)
       (wu ↦ mere_rec (BookFiber I (Equiv S S) f (v .fst)) (SymmetryImageWitness S D e)
         (symmetry_image_witness_prop S D e)
         (wv ↦ let gi ≔ D .family (wu .fst) in
           let gj ≔ D .family (wv .fst) in
           symmetry_image_witness S D e (G .mul gi gj)
             (x ↦ concat S (u .fst .map (v .fst .map x)) (D .act gi .map (D .act gj .map x))
               (D .act (G .mul gi gj) .map x)
               (wu .snd .map (wv .snd .map (refl x)))
               (inverse S (D .act (G .mul gi gj) .map x) (D .act gi .map (D .act gj .map x)) (D .act_mul gi gj x))))
         (v .snd))
       (u .snd))

def symmetry_image_inv (S : Type) (D : SymmetryImageData S) (u : SymmetryImage S D) : SymmetryImage S D
  ≔ let I ≔ D .index in
    let G ≔ D .group in
    let f ≔ symmetry_image_map S D in
    let e ≔ canonical_inverse_equiv S S (u .fst) in
    (e,
     mere_rec (BookFiber I (Equiv S S) f (u .fst)) (SymmetryImageWitness S D e) (symmetry_image_witness_prop S D e)
       (wu ↦ let gi ≔ D .family (wu .fst) in
         symmetry_image_witness S D e (G .inv gi)
           (x ↦ concat S (equiv_inverse_map S S (u .fst) x) (equiv_inverse_map S S (D .act gi) x)
             (D .act (G .inv gi) .map x)
             (refl ((d ↦ equiv_inverse_map S S d x) : Equiv S S → S) (wu .snd))
             (symmetry_act_inverse_map S D gi x)))
       (u .snd))

def symmetry_image_laws (S : Type) (D : SymmetryImageData S)
  : AbstractGroupLaws (SymmetryImage S D) (symmetry_image_unit S D) (symmetry_image_mul S D) (symmetry_image_inv S D)
  ≔ let m ≔ symmetry_image_mul S D in
    let e ≔ symmetry_image_unit S D in
    (carrier_set ≔ symmetry_image_set S D,
     unit_right ≔ u ↦ symmetry_image_path S D (m u e) u (x ↦ refl (u .fst .map x)),
     unit_left ≔ u ↦ symmetry_image_path S D (m e u) u (x ↦ refl (u .fst .map x)),
     assoc ≔ u v w ↦ symmetry_image_path S D (m u (m v w)) (m (m u v) w)
       (x ↦ refl (u .fst .map (v .fst .map (w .fst .map x)))),
     inv_right ≔ u ↦ symmetry_image_path S D (m u (symmetry_image_inv S D u)) e
       (x ↦ equiv_counit S S (u .fst) x))

def symmetry_image_group (S : Type) (D : SymmetryImageData S) : AbstractGroup
  ≔ (SymmetryImage S D, symmetry_image_unit S D, symmetry_image_mul S D, symmetry_image_inv S D,
     symmetry_image_laws S D)

{` The product is composition, judgmentally on underlying maps. `}
def symmetry_image_mul_map (S : Type) (D : SymmetryImageData S) (u v : SymmetryImage S D) (x : S)
  : Id S (symmetry_image_mul S D u v .fst .map x) (u .fst .map (v .fst .map x))
  ≔ refl (u .fst .map (v .fst .map x))

{` φ as a map into the image; it is a homomorphism, an embedding when φ is
   injective, and surjective. `}
def symmetry_image_include (S : Type) (D : SymmetryImageData S) (g : D .group .carrier) : SymmetryImage S D
  ≔ (D .act g, symmetry_image_witness S D (D .act g) g (x ↦ refl (D .act g .map x)))

def symmetry_image_include_hom (S : Type) (D : SymmetryImageData S)
  : IsAbstractHom (D .group) (symmetry_image_group S D) (symmetry_image_include S D)
  ≔ s s' ↦ symmetry_image_path S D (symmetry_image_include S D (D .group .mul s s'))
      (symmetry_image_mul S D (symmetry_image_include S D s) (symmetry_image_include S D s'))
      (x ↦ D .act_mul s s' x)

def SymmetryActInjective (S : Type) (D : SymmetryImageData S) : Type
  ≔ (g h : D .group .carrier) → ((x : S) → Id S (D .act g .map x) (D .act h .map x)) → Id (D .group .carrier) g h

def symmetry_image_include_embedding (S : Type) (D : SymmetryImageData S) (hinj : SymmetryActInjective S D)
  : IsEmbedding (D .group .carrier) (SymmetryImage S D) (symmetry_image_include S D)
  ≔ let T ≔ SymmetryImage S D in
    let inc ≔ symmetry_image_include S D in
    b ↦ u v ↦ subtype_equal (D .group .carrier) (g ↦ Id T b (inc g)) (g ↦ symmetry_image_set S D b (inc g)) u v
      (hinj (u .fst) (v .fst)
        (x ↦ concat T (inc (u .fst)) b (inc (v .fst)) (inverse T b (inc (u .fst)) (u .snd)) (v .snd)
          .fst .map (refl x)))

def symmetry_image_include_surjective (S : Type) (D : SymmetryImageData S)
  : Surjective (D .group .carrier) (SymmetryImage S D) (symmetry_image_include S D)
  ≔ let I ≔ D .index in
    let T ≔ SymmetryImage S D in
    let inc ≔ symmetry_image_include S D in
    u ↦ mere_rec (BookFiber I (Equiv S S) (symmetry_image_map S D) (u .fst))
      (Mere (BookFiber (D .group .carrier) T inc u)) (mere_isprop (BookFiber (D .group .carrier) T inc u))
      (w ↦ mere (BookFiber (D .group .carrier) T inc u)
        (D .family (w .fst), symmetry_image_path S D u (inc (D .family (w .fst))) (x ↦ w .snd .map (refl x))))
      (u .snd)

{` If φ is injective, φ : G ≅ image group. `}
def symmetry_image_iso (S : Type) (D : SymmetryImageData S) (hinj : SymmetryActInjective S D)
  : AbstractIso (D .group) (symmetry_image_group S D)
  ≔ (native_equivalence (D .group .carrier) (SymmetryImage S D)
       (embedding_surjection_equiv native_truncation (D .group .carrier) (SymmetryImage S D)
         (symmetry_image_include S D) (symmetry_image_include_embedding S D hinj)
         (symmetry_image_include_surjective S D)),
     symmetry_image_include_hom S D)

def symmetry_image_iso_map (S : Type) (D : SymmetryImageData S) (hinj : SymmetryActInjective S D) (g : D .group .carrier)
  : Id (SymmetryImage S D) (symmetry_image_iso S D hinj .fst .map g) (symmetry_image_include S D g)
  ≔ refl (symmetry_image_include S D g)
