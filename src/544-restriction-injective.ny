export "542-restriction-induction"

{` Chapter 5, lem:epifullyfaithful: if USym f is surjective, then the
   restriction f^* : GSet H → GSet G is an injection. As in the book, the
   identifications X = Y are the invariant maps of the H-set
   Z(w) = (X(w) ≃ Y(w)); the key step is that restriction of invariant maps
   along Bf is an equivalence when USym f is surjective (the book's
   comparison of fixed elements, fig:epifullyfaithful). `}

{` Sections of a set-valued family over a connected type agree once they agree
   at one point. `}
def connected_sections_agree (B : Type) (hB : Connected B) (Z : B → SetTypes) (s s' : (w : B) → Z w .fst)
  (b0 : B) (e : Id (Z b0 .fst) (s b0) (s' b0)) : Id ((w : B) → Z w .fst) s s'
  ≔ funext B (w ↦ Z w .fst) s s'
      (connected_based_elim native_truncation B hB b0 (w ↦ Id (Z w .fst) (s w) (s' w))
        (w ↦ Z w .snd (s w) (s' w)) e)

def invariant_maps_restrict (G H : Group) (f : GroupHom G H) (Z : GSet H) (s : InvariantMaps H Z)
  : InvariantMaps G (gset_restrict G H f Z)
  ≔ z ↦ s (hom_function G H f z)

def invariant_maps_restrict_reflects (G H : Group) (f : GroupHom G H) (Z : GSet H)
  : PathReflecting (InvariantMaps H Z) (InvariantMaps G (gset_restrict G H f Z)) (invariant_maps_restrict G H f Z)
  ≔ s s' e ↦ connected_sections_agree (BG H .carrier) (bg_connected H) Z s s' (hom_function G H f (shape G))
      (happly (BG G .carrier) (z ↦ Z (hom_function G H f z) .fst)
        (invariant_maps_restrict G H f Z s) (invariant_maps_restrict G H f Z s') e (shape G))

{` A loop at Bf(sh_G) acts trivially on t(sh_G) for an invariant map t of
   f^*Z, when USym f is surjective (the loop is merely ap_{Bf}(g)). `}
def restricted_section_loop (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  (l : Id (BG H .carrier) (hom_function G H f (shape G)) (hom_function G H f (shape G)))
  : Id (Z (hom_function G H f (shape G)) .fst)
      (transport (BG H .carrier) (w ↦ Z w .fst) (hom_function G H f (shape G)) (hom_function G H f (shape G)) l (t (shape G)))
      (t (shape G))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let Bf ≔ hom_function G H f in
    let b ≔ Bf (shape G) in
    let p ≔ hom_point G H f in
    let F : B → Type ≔ w ↦ Z w .fst in
    let Goal ≔ Id (F b) (transport B F b b l (t (shape G))) (t (shape G)) in
    mere_rec (BookFiber (USym G) (USym H) (usym_hom G H f) (pointed_loop_conjugate B (shape H) b p l)) Goal
      (Z b .snd (transport B F b b l (t (shape G))) (t (shape G)))
      (u ↦
        let q : Id (Id B b b) l (map_path A B Bf (shape G) (shape G) (u .fst))
          ≔ mono_loop_conjugate_injective B (shape H) b p l (map_path A B Bf (shape G) (shape G) (u .fst)) (u .snd) in
        concat (F b) (transport B F b b l (t (shape G)))
          (transport B F b b (map_path A B Bf (shape G) (shape G) (u .fst)) (t (shape G))) (t (shape G))
          (map_path (Id B b b) (F b) (r ↦ transport B F b b r (t (shape G))) l
            (map_path A B Bf (shape G) (shape G) (u .fst)) q)
          (pathover_transport_equiv A (z ↦ F (Bf z)) (shape G) (shape G) (u .fst) (t (shape G)) (t (shape G))
            .map (apd A (z ↦ F (Bf z)) t (shape G) (shape G) (u .fst))))
      (hs (pointed_loop_conjugate B (shape H) b p l))

def ch5_concat_cancel_inverse_right (B : Type) (x y z : B) (p : Id B x y) (q : Id B z y)
  : Id (Id B x y) (concat B x z y (concat B x y z p (inverse B z y q)) q) p
  ≔ J B z (y q ↦ (p : Id B x y) → Id (Id B x y) (concat B x z y (concat B x y z p (inverse B z y q)) q) p)
      (p ↦ calc
        concat B x z z (concat B x z z p (inverse B z z (refl z))) (refl z)
        = concat B x z z p (inverse B z z (refl z)) by concat_p1 B x z (concat B x z z p (inverse B z z (refl z)))
        = concat B x z z p (refl z) by map_path (Id B z z) (Id B x z) (concat B x z z p) (inverse B z z (refl z)) (refl z)
             (inverse_refl B z)
        = p by concat_p1 B x z p ∎)
      y q p

{` The extension of t to BH: for w : BH, the unique y : Z(w) with
   y = p · t(sh_G) for all p : Bf(sh_G) = w. `}
def RestrictedExtension (G H : Group) (f : GroupHom G H) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  (w : BG H .carrier) : Type
  ≔ Σ (Z w .fst) (y ↦ (p : Id (BG H .carrier) (hom_function G H f (shape G)) w) →
      Id (Z w .fst) y (transport (BG H .carrier) (v ↦ Z v .fst) (hom_function G H f (shape G)) w p (t (shape G))))

def restricted_extension_prop (G H : Group) (f : GroupHom G H) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  (w : BG H .carrier) : isProp (RestrictedExtension G H f Z t w)
  ≔ let B ≔ BG H .carrier in
    let b ≔ hom_function G H f (shape G) in
    let F : B → Type ≔ v ↦ Z v .fst in
    let P : Z w .fst → Type ≔ y ↦ (p : Id B b w) → Id (F w) y (transport B F b w p (t (shape G))) in
    let hP : (y : Z w .fst) → isProp (P y)
      ≔ y ↦ pi_prop (Id B b w) (p ↦ Id (F w) y (transport B F b w p (t (shape G))))
          (p ↦ Z w .snd y (transport B F b w p (t (shape G)))) in
    u v ↦ subtype_equal (Z w .fst) P hP u v
      (mere_rec (Id B b w) (Id (F w) (u .fst) (v .fst)) (Z w .snd (u .fst) (v .fst))
        (p ↦ concat (F w) (u .fst) (transport B F b w p (t (shape G))) (v .fst) (u .snd p)
          (inverse (F w) (v .fst) (transport B F b w p (t (shape G))) (v .snd p)))
        (bg_connected H .snd b w))

def restricted_extension_exists (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  (w : BG H .carrier) : RestrictedExtension G H f Z t w
  ≔ let B ≔ BG H .carrier in
    let b ≔ hom_function G H f (shape G) in
    let F : B → Type ≔ v ↦ Z v .fst in
    let t0 ≔ t (shape G) in
    mere_rec (Id B b w) (RestrictedExtension G H f Z t w) (restricted_extension_prop G H f Z t w)
      (p0 ↦ (transport B F b w p0 t0,
        p ↦ let l ≔ concat B b w b p0 (inverse B b w p) in
          calc
            transport B F b w p0 t0
            = transport B F b w (concat B b b w l p) t0
              by map_path (Id B b w) (F w) (r ↦ transport B F b w r t0) p0 (concat B b b w l p)
                   (inverse (Id B b w) (concat B b b w l p) p0
                     (ch5_concat_cancel_inverse_right B b w b p0 p))
            = transport B F b w p (transport B F b b l t0) by transport_concat B F b b w l p t0
            = transport B F b w p t0
              by map_path (F b) (F w) (transport B F b w p) (transport B F b b l t0) t0
                   (restricted_section_loop G H f hs Z t l) ∎))
      (bg_connected H .snd b w)

def restricted_extension (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  : InvariantMaps H Z
  ≔ w ↦ restricted_extension_exists G H f hs Z t w .fst

def restricted_extension_restricts (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (Z : GSet H) (t : InvariantMaps G (gset_restrict G H f Z))
  : Id (InvariantMaps G (gset_restrict G H f Z))
      (invariant_maps_restrict G H f Z (restricted_extension G H f hs Z t)) t
  ≔ let b ≔ hom_function G H f (shape G) in
    connected_sections_agree (BG G .carrier) (bg_connected G) (gset_restrict G H f Z)
      (invariant_maps_restrict G H f Z (restricted_extension G H f hs Z t)) t (shape G)
      (concat (Z b .fst) (restricted_extension G H f hs Z t b)
        (transport (BG H .carrier) (v ↦ Z v .fst) b b (refl b) (t (shape G))) (t (shape G))
        (restricted_extension_exists G H f hs Z t b .snd (refl b))
        (transport_refl (BG H .carrier) (v ↦ Z v .fst) b (t (shape G))))

def invariant_maps_restrict_equiv (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (Z : GSet H)
  : BookEquiv (InvariantMaps H Z) (InvariantMaps G (gset_restrict G H f Z))
  ≔ embedding_surjection_equiv native_truncation (InvariantMaps H Z) (InvariantMaps G (gset_restrict G H f Z))
      (invariant_maps_restrict G H f Z)
      (path_reflecting_set_embedding (InvariantMaps H Z) (InvariantMaps G (gset_restrict G H f Z))
        (invariant_maps_set G (gset_restrict G H f Z)) (invariant_maps_restrict G H f Z)
        (invariant_maps_restrict_reflects G H f Z))
      (t ↦ mere (BookFiber (InvariantMaps H Z) (InvariantMaps G (gset_restrict G H f Z)) (invariant_maps_restrict G H f Z) t)
        (restricted_extension G H f hs Z t,
         inverse (InvariantMaps G (gset_restrict G H f Z))
           (invariant_maps_restrict G H f Z (restricted_extension G H f hs Z t)) t
           (restricted_extension_restricts G H f hs Z t)))

{` lem:epifullyfaithful. ap of f^* is an equivalence for all X, Y (lem:inj-ap). `}
def gset_equivalences_hset (H : Group) (X Y : GSet H) : GSet H
  ≔ w ↦ (Equiv (X w .fst) (Y w .fst), equivalences_set (X w .fst) (Y w .fst) (Y w .snd))

def restrict_paths_is_equiv (G H : Group) (f : GroupHom G H)
  (hs : Surjective (USym G) (USym H) (usym_hom G H f)) (X Y : GSet H)
  : BookIsEquiv (Id (GSet H) X Y) (Id (GSet G) (gset_restrict G H f X) (gset_restrict G H f Y))
      (map_path (GSet H) (GSet G) (gset_restrict G H f) X Y)
  ≔ let fX ≔ gset_restrict G H f X in
    let fY ≔ gset_restrict G H f Y in
    let PH ≔ Id (GSet H) X Y in
    let PG ≔ Id (GSet G) fX fY in
    let EH ≔ InvariantMaps H (gset_equivalences_hset H X Y) in
    let EG ≔ InvariantMaps G (gset_restrict G H f (gset_equivalences_hset H X Y)) in
    let c ≔ compose_equiv PH EH PG (gset_path_equiv H X Y)
      (compose_equiv EH EG PG
        (native_equivalence EH EG (invariant_maps_restrict_equiv G H f hs (gset_equivalences_hset H X Y)))
        (canonical_inverse_equiv PG EG (gset_path_equiv G fX fY))) in
    book_equivalence PH PG
      (equiv_change_map PH PG c (map_path (GSet H) (GSet G) (gset_restrict G H f) X Y)
        (e ↦ equiv_retraction PG EG (gset_path_equiv G fX fY) (map_path (GSet H) (GSet G) (gset_restrict G H f) X Y e)))
    .equiv

def restriction_injective (G H : Group) (f : GroupHom G H) (hs : Surjective (USym G) (USym H) (usym_hom G H f))
  : IsEmbedding (GSet H) (GSet G) (gset_restrict G H f)
  ≔ path_equivalences_embedding (GSet H) (GSet G) (gset_restrict G H f) (X Y ↦ restrict_paths_is_equiv G H f hs X Y)
