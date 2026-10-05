export "1505-four-element-field"
export "1400-euclidean-fields"
export "431-homomorphism-remarks"
export "502-subgroups"

{` Chapter 15 (galois.tex), section "Intermediate extensions and subgroups"
   (running text only).

   (1) For i : k → K and j : K → L, restr_i restricted to components is the
   pointed map BGal(L, j) → BGal(L, j i), x ↦ x ∘ i (pointed by refl), i.e.
   the homomorphism galois_restriction_hom; since restr_i is a set bundle
   (lem:field-ext-restriction-set-bundle) it is a monomorphism, so it
   presents Gal(L, j) as a subgroup of Gal(L, j i) (galois_restriction_mono;
   subgroups are monomorphisms by lem:SubG=MonoG of chapter 5).

   (2) The Gal(L, i)-set X : (L', i') ↦ L' (galois_gset); its action is
   transport along the carrier, i.e. the k-automorphism (litmus
   galois_gset_action).

   (3) For a pointed connected g : B → BGal(L, i) (the book's "pointed
   connected set-bundle"; the bundle property is not needed for the
   constructions), K ≔ (X g)^B ≡ Π_{x : B} X(g(x)) is a set with the
   pointwise field structure (galois_fixed_field; connectedness of B is
   what makes non-invertible sections zero), with extensions
   i' : k → K, i'(a) ≔ x ↦ snd(g(x))(a) and j' : K → L, j'(f) ≔ p⁻¹ f(b),
   where p : L = L'' is the field component of the pointing path
   (L, i) = g(b) = (L'', j'') and p⁻¹ is taken as the k-isomorphism given
   by the inverse path. Then j' i' = i (galois_fixed_field_triangle).
   Corrections of misprints: the book writes "the B-set Xf" for X g, "p i' = j''"
   for p i = j'' (fixed_field_point_iso) and "j' i'(a) = … = i'(a)" for = i(a). `}

def galois_restriction_hom (k : Field) (E : FieldExt k) (F : FieldExt (E .fst))
  : GroupHom (galois_group (E .fst) F) (galois_group k (field_ext_restriction k E F))
  ≔ automorphism_group_map_hom (FieldExt (E .fst)) (FieldExt k) (field_ext_groupoid (E .fst)) (field_ext_groupoid k)
      (field_ext_restriction k E) F

{` For a set bundle f, ap_f is injective on paths. `}
def covering_ap_injective (A B : Type) (f : A → B) (c : IsCovering A B f) (x y : A) (p q : Id A x y)
  (e : Id (Id B (f x) (f y)) (refl f p) (refl f q)) : Id (Id A x y) p q
  ≔ let Fb ≔ BookFiber (Id A x y) (Id B (f x) (f y)) (map_path A B f x y) (refl f p) in
    let h ≔ hlevel_one_to_prop Fb
              (fibers_hlevel_to_ap (suc. zero.) A B f (b ↦ set_to_hlevel_two (BookFiber A B f b) (c b)) x y (refl f p)) in
    refl ((u ↦ u .fst) : Fb → Id A x y) (h (p, refl (refl f p)) (q, e))

{` restr_i presents Gal(L, j) as a subgroup of Gal(L, j i). `}
def galois_restriction_mono (k : Field) (E : FieldExt k) (F : FieldExt (E .fst))
  : IsGroupMono (galois_group (E .fst) F) (galois_group k (field_ext_restriction k E F)) (galois_restriction_hom k E F)
  ≔ let A ≔ FieldExt (E .fst) in let Bt ≔ FieldExt k in let f ≔ field_ext_restriction k E in
    let H ≔ galois_group (E .fst) F in let G ≔ galois_group k (f F) in
    let hA ≔ field_ext_groupoid (E .fst) in let hB ≔ field_ext_groupoid k in
    let u ≔ usym_hom H G (galois_restriction_hom k E F) in
    let mu ≔ automorphism_group_map_usym A Bt hA hB f F in
    let P ≔ Id Bt (f F) (f F) in
    path_reflecting_set_embedding (USym H) (USym G) (usym_set G) u
      (g g' e ↦ equivalence_injective (USym H) (Id A F F) (automorphism_group_usym_equiv A hA F) g g'
         (covering_ap_injective A Bt f (field_ext_restriction_set_bundle k E) F F (g .fst) (g' .fst)
            (concat P (refl f (g .fst)) (u g .fst) (refl f (g' .fst))
              (inverse P (u g .fst) (refl f (g .fst)) (mu g))
              (concat P (u g .fst) (u g' .fst) (refl f (g' .fst))
                (refl ((r ↦ r .fst) : USym G → P) e) (mu g')))))

{` The Gal(L, i)-set X : (L', i') ↦ L'. `}
def galois_gset (k : Field) (E : FieldExt k) : GSet (galois_group k E)
  ≔ u ↦ (u .fst .fst .fst .carrier, ring_set (u .fst .fst .fst))

{` Litmus: a symmetry g acts on X(sh) = L by the k-automorphism it corresponds to. `}
def galois_gset_action (k : Field) (E : FieldExt k) (g : USym (galois_group k E)) (x : E .fst .fst .carrier)
  : Id (E .fst .fst .carrier) (gset_usym_act (galois_group k E) (galois_gset k E) g x)
      (galois_usym_kaut_equiv k E .map g .fst .fst .map x)
  ≔ refl (gset_usym_act (galois_group k E) (galois_gset k E) g x)

def f4_frobenius_acts_on_omega
  : Id F4 (gset_usym_act (galois_group f2_field f4_over_f2) (galois_gset f2_field f4_over_f2) f4_frobenius_symmetry f4w.) f4v.
  ≔ refl ((σ ↦ σ .fst .fst .map f4w.) : FieldExtIso f2_field f4_over_f2 f4_over_f2 → F4)
      (equiv_counit (USym (galois_group f2_field f4_over_f2)) (FieldExtIso f2_field f4_over_f2 f4_over_f2)
        (galois_usym_kaut_equiv f2_field f4_over_f2) f4_frobenius_kaut)

{` The fibre rings X(g x) of a map g : B → BGal(L, i). `}
def fixed_ring_at (k : Field) (E : FieldExt k) (B : Type) (g : B → NativeComponent (FieldExt k) E) (x : B) : AbstractRing
  ≔ g x .fst .fst .fst

{` (X g)^B ≡ Π_{x : B} X(g x) with the pointwise ring structure. `}
def fixed_ring (k : Field) (E : FieldExt k) (B : Type) (g : B → NativeComponent (FieldExt k) E) : AbstractRing
  ≔ let R ≔ fixed_ring_at k E B g in
    let C ≔ (x : B) → R x .carrier in
    let F ≔ (x ↦ R x .carrier) : B → Type in
    let hC ≔ pi_set B F (x ↦ ring_set (R x)) in
    (C, (x ↦ R x .zero), (f h x ↦ R x .add (f x) (h x)), (f x ↦ R x .neg (f x)),
     (carrier_set ≔ hC,
      unit_right ≔ f ↦ funext B F (x ↦ R x .add (f x) (R x .zero)) f (x ↦ R x .add_laws .unit_right (f x)),
      unit_left ≔ f ↦ funext B F (x ↦ R x .add (R x .zero) (f x)) f (x ↦ R x .add_laws .unit_left (f x)),
      assoc ≔ f1 f2 f3 ↦ funext B F (x ↦ R x .add (f1 x) (R x .add (f2 x) (f3 x))) (x ↦ R x .add (R x .add (f1 x) (f2 x)) (f3 x))
                (x ↦ R x .add_laws .assoc (f1 x) (f2 x) (f3 x)),
      inv_right ≔ f ↦ funext B F (x ↦ R x .add (f x) (R x .neg (f x))) (x ↦ R x .zero) (x ↦ R x .add_laws .inv_right (f x))),
     (x ↦ R x .one), (f h x ↦ R x .mul (f x) (h x)),
     (hC,
      (f ↦ (funext B F (x ↦ R x .mul (f x) (R x .one)) f (x ↦ ring_mul_one_right (R x) (f x)),
            funext B F (x ↦ R x .mul (R x .one) (f x)) f (x ↦ ring_mul_one_left (R x) (f x))),
       f1 f2 f3 ↦ funext B F (x ↦ R x .mul (f1 x) (R x .mul (f2 x) (f3 x))) (x ↦ R x .mul (R x .mul (f1 x) (f2 x)) (f3 x))
                    (x ↦ ring_mul_assoc (R x) (f1 x) (f2 x) (f3 x)))),
     (f1 f2 f3 ↦ funext B F (x ↦ R x .mul (f1 x) (R x .add (f2 x) (f3 x)))
                   (x ↦ R x .add (R x .mul (f1 x) (f2 x)) (R x .mul (f1 x) (f3 x))) (x ↦ ring_ldistr (R x) (f1 x) (f2 x) (f3 x)),
      f1 f2 f3 ↦ funext B F (x ↦ R x .mul (R x .add (f1 x) (f2 x)) (f3 x))
                   (x ↦ R x .add (R x .mul (f1 x) (f3 x)) (R x .mul (f2 x) (f3 x))) (x ↦ ring_rdistr (R x) (f1 x) (f2 x) (f3 x))))

{` The carrier of the fixed ring is literally the type of fixed points of X g. `}
def fixed_ring_carrier (k : Field) (E : FieldExt k) (B : Type) (g : B → NativeComponent (FieldExt k) E)
  : Id Type (fixed_ring k E B g .carrier) ((x : B) → galois_gset k E (g x) .fst)
  ≔ refl ((x : B) → galois_gset k E (g x) .fst)

{` Over a connected B a section invertible at one point is invertible everywhere. `}
def fixed_ring_invertible_spread (k : Field) (E : FieldExt k) (B : Type) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) (f : fixed_ring k E B g .carrier) (x : B)
  (hx : IsInvertible (fixed_ring_at k E B g x) (f x)) (y : B) : IsInvertible (fixed_ring_at k E B g y) (f y)
  ≔ let R ≔ fixed_ring_at k E B g in
    mere_rec (Id B x y) (IsInvertible (R y) (f y)) (is_invertible_prop (R y) (f y))
      (p ↦ J B x (y' p' ↦ IsInvertible (R y') (f y')) hx y p) (hB .snd x y)

def fixed_ring_invertible_from_point (k : Field) (E : FieldExt k) (B : Type) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) (f : fixed_ring k E B g .carrier) (x : B)
  (hx : IsInvertible (fixed_ring_at k E B g x) (f x)) : IsInvertible (fixed_ring k E B g) f
  ≔ let R ≔ fixed_ring_at k E B g in let F ≔ (y ↦ R y .carrier) : B → Type in
    let w ≔ (y ↦ mere_rec (InverseWitness (R y) (f y)) (InverseWitness (R y) (f y)) (inverse_witness_prop (R y) (f y))
                   (t ↦ t) (fixed_ring_invertible_spread k E B hB g f x hx y))
            : (y : B) → InverseWitness (R y) (f y) in
    invertible_intro (fixed_ring k E B g) f (y ↦ w y .fst)
      (funext B F (y ↦ R y .mul (f y) (w y .fst)) (y ↦ R y .one) (y ↦ w y .snd .fst))
      (funext B F (y ↦ R y .mul (w y .fst) (f y)) (y ↦ R y .one) (y ↦ w y .snd .snd))

def fixed_ring_non_invertibles_zero (k : Field) (E : FieldExt k) (B : Type) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) : NonInvertiblesAreZero (fixed_ring k E B g)
  ≔ let R ≔ fixed_ring_at k E B g in
    f nf ↦ funext B (x ↦ R x .carrier) f (x ↦ R x .zero)
      (x ↦ field_non_invertible_zero (R x) (g x .fst .fst .snd) (f x)
             (hx ↦ nf (fixed_ring_invertible_from_point k E B hB g f x hx)))

def fixed_ring_non_trivial_cring (k : Field) (E : FieldExt k) (B : Type) (b : B)
  (g : B → NativeComponent (FieldExt k) E) : IsNonTrivialCRing (fixed_ring k E B g)
  ≔ let R ≔ fixed_ring_at k E B g in
    (f h ↦ funext B (x ↦ R x .carrier) (x ↦ R x .mul (f x) (h x)) (x ↦ R x .mul (h x) (f x))
              (x ↦ g x .fst .fst .snd .fst .fst (f x) (h x)),
     p ↦ g b .fst .fst .snd .fst .snd (p (refl b)))

{` K = (X g)^B is a field. `}
def galois_fixed_field (k : Field) (E : FieldExt k) (B : Type) (b : B) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) : Field
  ≔ (fixed_ring k E B g,
     field_from_non_invertible_zero (fixed_ring k E B g) (fixed_ring_non_trivial_cring k E B b g)
       (fixed_ring_non_invertibles_zero k E B hB g))

{` i' : k → K, i'(a) ≔ x ↦ snd(g x)(a). `}
def galois_fixed_field_base (k : Field) (E : FieldExt k) (B : Type) (b : B) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) : FieldExt k
  ≔ let R ≔ fixed_ring_at k E B g in let F ≔ (x ↦ R x .carrier) : B → Type in
    let i ≔ (x ↦ g x .fst .snd) : (x : B) → RingHom (k .fst) (R x) in
    (galois_fixed_field k E B b hB g,
     ((a x ↦ i x .fst .fst a,
       a a' ↦ funext B F (x ↦ i x .fst .fst (k .fst .add a a')) (x ↦ R x .add (i x .fst .fst a) (i x .fst .fst a'))
                (x ↦ i x .fst .snd a a')),
      (funext B F (x ↦ i x .fst .fst (k .fst .one)) (x ↦ R x .one) (x ↦ i x .snd .fst),
       a a' ↦ funext B F (x ↦ i x .fst .fst (k .fst .mul a a')) (x ↦ R x .mul (i x .fst .fst a) (i x .fst .fst a'))
                (x ↦ i x .snd .snd a a'))))

{` The pointing (L, i) = g(b) = (L'', j'') gives p : L ≅ L'' with p i = j''. `}
def fixed_field_point_iso (k : Field) (E : FieldExt k) (B : Type) (b : B)
  (g : B → NativeComponent (FieldExt k) E) (pt : Id (NativeComponent (FieldExt k) E) (component_point (FieldExt k) E) (g b))
  : FieldExtIso k E (g b .fst)
  ≔ field_ext_path_equiv k E (g b .fst) .map (pt .fst)

{` p⁻¹ : (L'', j'') ≅ (L, i), the k-isomorphism of the inverse path. `}
def fixed_field_point_iso_inverse (k : Field) (E : FieldExt k) (B : Type) (b : B)
  (g : B → NativeComponent (FieldExt k) E) (pt : Id (NativeComponent (FieldExt k) E) (component_point (FieldExt k) E) (g b))
  : FieldExtIso k (g b .fst) E
  ≔ field_ext_path_equiv k (g b .fst) E .map (inverse (FieldExt k) E (g b .fst) (pt .fst))

{` j' : K → L, j'(f) ≔ p⁻¹ f(b). `}
def galois_fixed_field_top (k : Field) (E : FieldExt k) (B : Type) (b : B) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) (pt : Id (NativeComponent (FieldExt k) E) (component_point (FieldExt k) E) (g b))
  : RingHom (fixed_ring k E B g) (E .fst .fst)
  ≔ let R ≔ fixed_ring_at k E B g in let K ≔ fixed_ring k E B g in
    let ev ≔ ((f ↦ f b, f h ↦ refl (R b .add (f b) (h b))), (refl (R b .one), f h ↦ refl (R b .mul (f b) (h b))))
             : RingHom K (R b) in
    ring_hom_compose K (R b) (E .fst .fst) ev
      (ring_iso_hom (R b) (E .fst .fst) (fixed_field_point_iso_inverse k E B b g pt .fst))

{` j' i' = i. `}
def galois_fixed_field_triangle (k : Field) (E : FieldExt k) (B : Type) (b : B) (hB : Connected B)
  (g : B → NativeComponent (FieldExt k) E) (pt : Id (NativeComponent (FieldExt k) E) (component_point (FieldExt k) E) (g b))
  : Id (RingHom (k .fst) (E .fst .fst))
      (ring_hom_compose (k .fst) (fixed_ring k E B g) (E .fst .fst)
        (galois_fixed_field_base k E B b hB g .snd) (galois_fixed_field_top k E B b hB g pt))
      (E .snd)
  ≔ let τ ≔ fixed_field_point_iso_inverse k E B b g pt in
    let L ≔ E .fst .fst in
    ring_hom_ext (k .fst) L
      (ring_hom_compose (k .fst) (fixed_ring k E B g) L (galois_fixed_field_base k E B b hB g .snd) (galois_fixed_field_top k E B b hB g pt))
      (E .snd)
      (a ↦ refl ((χ ↦ χ .fst .fst a) : RingHom (k .fst) L → L .carrier) (τ .snd))

{` Litmus: the construction for g = id on BGal(𝔽₄/𝔽₂) (the Galois-fixed field). `}
def f4_galois_fixed_field : Field
  ≔ galois_fixed_field f2_field f4_over_f2 (BG (galois_group f2_field f4_over_f2) .carrier)
      (shape (galois_group f2_field f4_over_f2)) (galois_group f2_field f4_over_f2 .classifying .connected) (x ↦ x)

def f4_galois_fixed_field_triangle
  : Id (RingHom f2_ring f4_ring)
      (ring_hom_compose f2_ring (f4_galois_fixed_field .fst) f4_ring
        (galois_fixed_field_base f2_field f4_over_f2 (BG (galois_group f2_field f4_over_f2) .carrier)
           (shape (galois_group f2_field f4_over_f2)) (galois_group f2_field f4_over_f2 .classifying .connected) (x ↦ x) .snd)
        (galois_fixed_field_top f2_field f4_over_f2 (BG (galois_group f2_field f4_over_f2) .carrier)
           (shape (galois_group f2_field f4_over_f2)) (galois_group f2_field f4_over_f2 .classifying .connected) (x ↦ x)
           (refl (shape (galois_group f2_field f4_over_f2)))))
      f2_to_f4_hom
  ≔ galois_fixed_field_triangle f2_field f4_over_f2 (BG (galois_group f2_field f4_over_f2) .carrier)
      (shape (galois_group f2_field f4_over_f2)) (galois_group f2_field f4_over_f2 .classifying .connected) (x ↦ x)
      (refl (shape (galois_group f2_field f4_over_f2)))
