export "822-pullback-group-symmetries"
export "436-maps-from-classifying-types"

{` Chapter 8 (congp.tex), the exercise at line 479, first part:
   the pointed version of xca:univpropofpullback and the induced
   equivalence Hom(K,H) ×_{Hom(K,G)} Hom(K,H') ≃ Hom(K, H ×_G H') for all
   groups K. `}

{` The pointed pullback of pointed maps f : B →* D, g : C →* D, pointed at
   (pt_B, pt_C, f_pt⁻¹ g_pt) (concatenation order: f_pt⁻¹ first). For
   groups this is (BH ×_{BG} BH', pt_{H ×_G H'}) of def:intersectionofgroups. `}
def PointedPullback (B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D) : Pointed
  ≔ (TypePullback (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst),
     ((B .point, C .point), pbg_twist (D .carrier) (D .point) (f .fst (B .point)) (g .fst (C .point)) (f .snd) (g .snd)))

def pointed_pullback_groups (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id Pointed (PointedPullback (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f'))
      (pbg_space G H H' f f', pbg_point G H H' f f')
  ≔ refl (PointedPullback (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f'))

{` Cones: a map into the pullback is a triple (β, γ, H) with
   H : f ∘ β ~ g ∘ γ (judgmentally, up to eta). `}
def PbgConeData (X : Type) (B C D : Type) (f : B → D) (g : C → D) : Type
  ≔ Σ (Product (X → B) (X → C)) (bg ↦ (x : X) → Id D (f (bg .fst x)) (g (bg .snd x)))

def pbg_cone_gap (X : Type) (B C D : Type) (f : B → D) (g : C → D) (w : PbgConeData X B C D f g)
  : X → TypePullback B C D f g
  ≔ x ↦ ((w .fst .fst x, w .fst .snd x), w .snd x)

def pbg_cone_split (X : Type) (B C D : Type) (f : B → D) (g : C → D) (h : X → TypePullback B C D f g)
  : PbgConeData X B C D f g
  ≔ ((x ↦ h x .fst .fst, x ↦ h x .fst .snd), x ↦ h x .snd)

{` The equivalence conditions. For fp : dd = y0, gp : dd = z0, r : y0 = y1,
   s : z0 = z1, v : y1 = z1, the square condition (fp⁻¹ gp) · s = r · v
   and the pointed-homotopy condition (fp · r) · v = gp · s are logically
   equivalent. `}
def PbgConeLeft (D : Type) (dd y0 z0 y1 z1 : D) (fp : Id D dd y0) (gp : Id D dd z0) (r : Id D y0 y1) (s : Id D z0 z1)
  (v : Id D y1 z1) : Type
  ≔ Id (Id D y0 z1) (concat D y0 z0 z1 (pbg_twist D dd y0 z0 fp gp) s) (concat D y0 y1 z1 r v)

def PbgConeRight (D : Type) (dd y0 z0 y1 z1 : D) (fp : Id D dd y0) (gp : Id D dd z0) (r : Id D y0 y1) (s : Id D z0 z1)
  (v : Id D y1 z1) : Type
  ≔ Id (Id D dd z1) (concat D dd y1 z1 (concat D dd y0 y1 fp r) v) (concat D dd z0 z1 gp s)

def pbg_twist_left_path (D : Type) (dd z1 : D) (s : Id D dd z1)
  : Id (Id D dd z1) (concat D dd dd z1 (pbg_twist D dd dd dd (refl dd) (refl dd)) s) s
  ≔ concat (Id D dd z1) (concat D dd dd z1 (pbg_twist D dd dd dd (refl dd) (refl dd)) s)
      (concat D dd dd z1 (refl dd) s) s
      (refl ((c ↦ concat D dd dd z1 c s) : Id D dd dd → Id D dd z1) (pbg_twist_refl D dd))
      (concat_1p D dd z1 s)

def pbg_cone_conditions_base (D : Type) (dd y1 z1 : D) (r : Id D dd y1) (s : Id D dd z1) (v : Id D y1 z1)
  : Product (PbgConeLeft D dd dd dd y1 z1 (refl dd) (refl dd) r s v → PbgConeRight D dd dd dd y1 z1 (refl dd) (refl dd) r s v)
      (PbgConeRight D dd dd dd y1 z1 (refl dd) (refl dd) r s v → PbgConeLeft D dd dd dd y1 z1 (refl dd) (refl dd) r s v)
  ≔ let c ≔ pbg_twist D dd dd dd (refl dd) (refl dd) in
    (h ↦ calc
       concat D dd y1 z1 (concat D dd dd y1 (refl dd) r) v = concat D dd y1 z1 r v
         by refl ((t ↦ concat D dd y1 z1 t v) : Id D dd y1 → Id D dd z1) (concat_1p D dd y1 r)
       = concat D dd dd z1 c s by inverse (Id D dd z1) (concat D dd dd z1 c s) (concat D dd y1 z1 r v) h
       = s by pbg_twist_left_path D dd z1 s
       = concat D dd dd z1 (refl dd) s by inverse (Id D dd z1) (concat D dd dd z1 (refl dd) s) s (concat_1p D dd z1 s) ∎,
     k ↦ calc
       concat D dd dd z1 c s = s by pbg_twist_left_path D dd z1 s
       = concat D dd dd z1 (refl dd) s by inverse (Id D dd z1) (concat D dd dd z1 (refl dd) s) s (concat_1p D dd z1 s)
       = concat D dd y1 z1 (concat D dd dd y1 (refl dd) r) v
         by inverse (Id D dd z1) (concat D dd y1 z1 (concat D dd dd y1 (refl dd) r) v) (concat D dd dd z1 (refl dd) s) k
       = concat D dd y1 z1 r v
         by refl ((t ↦ concat D dd y1 z1 t v) : Id D dd y1 → Id D dd z1) (concat_1p D dd y1 r) ∎)

def pbg_cone_conditions (D : Type) (dd y0 : D) (fp : Id D dd y0) (z0 : D) (gp : Id D dd z0) (y1 z1 : D)
  (r : Id D y0 y1) (s : Id D z0 z1) (v : Id D y1 z1)
  : Product (PbgConeLeft D dd y0 z0 y1 z1 fp gp r s v → PbgConeRight D dd y0 z0 y1 z1 fp gp r s v)
      (PbgConeRight D dd y0 z0 y1 z1 fp gp r s v → PbgConeLeft D dd y0 z0 y1 z1 fp gp r s v)
  ≔ J D dd
      (y0 fp ↦ (z0 : D) (gp : Id D dd z0) (r : Id D y0 y1) (s : Id D z0 z1)
        → Product (PbgConeLeft D dd y0 z0 y1 z1 fp gp r s v → PbgConeRight D dd y0 z0 y1 z1 fp gp r s v)
            (PbgConeRight D dd y0 z0 y1 z1 fp gp r s v → PbgConeLeft D dd y0 z0 y1 z1 fp gp r s v))
      (z0 gp ↦ J D dd
        (z0 gp ↦ (r : Id D dd y1) (s : Id D z0 z1)
          → Product (PbgConeLeft D dd dd z0 y1 z1 (refl dd) gp r s v → PbgConeRight D dd dd z0 y1 z1 (refl dd) gp r s v)
              (PbgConeRight D dd dd z0 y1 z1 (refl dd) gp r s v → PbgConeLeft D dd dd z0 y1 z1 (refl dd) gp r s v))
        (r s ↦ pbg_cone_conditions_base D dd y1 z1 r s v) z0 gp)
      y0 fp z0 gp r s

{` The chain of equivalences for the pointed universal property. `}
def PbgPointedCone (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst)) : Type
  ≔ Id (PointedPullback B C D f g .carrier) (PointedPullback B C D f g .point)
      (pbg_cone_gap (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) w (X .point))

def pbg_pointed_cone_split_equiv (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  : Equiv (BookPointedMap X (PointedPullback B C D f g))
      (Σ (PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst)) (PbgPointedCone X B C D f g))
  ≔ let W ≔ PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) in
    quasi_inverse_equiv (BookPointedMap X (PointedPullback B C D f g)) (Σ W (PbgPointedCone X B C D f g))
      (h ↦ (pbg_cone_split (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) (h .fst), h .snd))
      (t ↦ (pbg_cone_gap (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) (t .fst), t .snd))
      (h ↦ refl h) (t ↦ refl t)

def PbgConeQ (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst)) : Type
  ≔ Id (Product (B .carrier) (C .carrier)) (B .point, C .point) (w .fst .fst (X .point), w .fst .snd (X .point))

def PbgConeL (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst))
  (q : PbgConeQ X B C D f g w) : Type
  ≔ PbgConeLeft (D .carrier) (D .point) (f .fst (B .point)) (g .fst (C .point))
      (f .fst (w .fst .fst (X .point))) (g .fst (w .fst .snd (X .point))) (f .snd) (g .snd)
      (refl (f .fst) (q .fst)) (refl (g .fst) (q .snd)) (w .snd (X .point))

def PbgConeR (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst))
  (q : PbgConeQ X B C D f g w) : Type
  ≔ PbgConeRight (D .carrier) (D .point) (f .fst (B .point)) (g .fst (C .point))
      (f .fst (w .fst .fst (X .point))) (g .fst (w .fst .snd (X .point))) (f .snd) (g .snd)
      (refl (f .fst) (q .fst)) (refl (g .fst) (q .snd)) (w .snd (X .point))

def pbg_pointed_cone_left_equiv (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst))
  : Equiv (PbgPointedCone X B C D f g w) (Σ (PbgConeQ X B C D f g w) (PbgConeL X B C D f g w))
  ≔ let BC ≔ Product (B .carrier) (C .carrier) in
    let F ≔ pbg_fam (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) in
    let PB ≔ PointedPullback B C D f g in
    let u ≔ pbg_cone_gap (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) w (X .point) in
    let d0 ≔ pbg_twist (D .carrier) (D .point) (f .fst (B .point)) (g .fst (C .point)) (f .snd) (g .snd) in
    compose_equiv (PbgPointedCone X B C D f g w) (SigmaPath BC F (PB .point) u)
      (Σ (PbgConeQ X B C D f g w) (PbgConeL X B C D f g w))
      (canonical_inverse_equiv (SigmaPath BC F (PB .point) u) (Id (PB .carrier) (PB .point) u)
        (sigma_path_equiv BC F (PB .point) u))
      (family_equiv (PbgConeQ X B C D f g w) (q ↦ Id F q d0 (w .snd (X .point))) (PbgConeL X B C D f g w)
        (q ↦ pbg_square_equiv (D .carrier) (f .fst (B .point)) (f .fst (w .fst .fst (X .point))) (refl (f .fst) (q .fst))
          (g .fst (C .point)) (g .fst (w .fst .snd (X .point))) (refl (g .fst) (q .snd)) d0 (w .snd (X .point))))

def pbg_pointed_cone_lr_equiv (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (hD : isGroupoid (D .carrier))
  (w : PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst))
  (q : PbgConeQ X B C D f g w)
  : Equiv (PbgConeL X B C D f g w q) (PbgConeR X B C D f g w q)
  ≔ let Dc ≔ D .carrier in
    let y0 ≔ f .fst (B .point) in let z0 ≔ g .fst (C .point) in
    let y1 ≔ f .fst (w .fst .fst (X .point)) in let z1 ≔ g .fst (w .fst .snd (X .point)) in
    let r ≔ refl (f .fst) (q .fst) in let s ≔ refl (g .fst) (q .snd) in let v ≔ w .snd (X .point) in
    let c ≔ pbg_cone_conditions Dc (D .point) y0 (f .snd) z0 (g .snd) y1 z1 r s v in
    iff_equiv (PbgConeL X B C D f g w q) (PbgConeR X B C D f g w q)
      (hD y0 z1 (concat Dc y0 z0 z1 (pbg_twist Dc (D .point) y0 z0 (f .snd) (g .snd)) s) (concat Dc y0 y1 z1 r v))
      (hD (D .point) z1 (concat Dc (D .point) y1 z1 (concat Dc (D .point) y0 y1 (f .snd) r) v)
        (concat Dc (D .point) z0 z1 (g .snd) s))
      (c .fst) (c .snd)

def PbgPointedPullbackOfMaps (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D) : Type
  ≔ TypePullback (BookPointedMap X B) (BookPointedMap X C) (BookPointedMap X D)
      (beta ↦ book_pointed_compose X B D beta f) (gamma ↦ book_pointed_compose X C D gamma g)

def PbgPointedHomotopyPairs (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D) : Type
  ≔ Σ (Product (BookPointedMap X B) (BookPointedMap X C))
      (bc ↦ PointedHomotopy X D (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g))

def pbg_pointed_reassoc_equiv (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  : Equiv (Σ (PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst))
            (w ↦ Σ (PbgConeQ X B C D f g w) (PbgConeR X B C D f g w)))
      (PbgPointedHomotopyPairs X B C D f g)
  ≔ let W ≔ PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) in
    let S ≔ Σ W (w ↦ Σ (PbgConeQ X B C D f g w) (PbgConeR X B C D f g w)) in
    quasi_inverse_equiv S (PbgPointedHomotopyPairs X B C D f g)
      (t ↦ (((t .fst .fst .fst, t .snd .fst .fst), (t .fst .fst .snd, t .snd .fst .snd)), (t .fst .snd, t .snd .snd)))
      (t ↦ (((t .fst .fst .fst, t .fst .snd .fst), t .snd .fst),
            (((t .fst .fst .snd, t .fst .snd .snd) : Id (Product (B .carrier) (C .carrier)) (B .point, C .point)
               (t .fst .fst .fst (X .point), t .fst .snd .fst (X .point))), t .snd .snd)))
      (t ↦ refl t) (t ↦ refl t)

{` The pointed version of xca:univpropofpullback: for a groupoid D,
   (X →* B ×_D C) ≃ (X →* B) ×_{(X →* D)} (X →* C), the pullback of
   f ∘ - and g ∘ -. (The groupoid hypothesis makes the coherence types
   propositions; it holds for all classifying types.) `}
def pointed_pullback_universal_property (X B C D : Pointed) (f : BookPointedMap B D) (g : BookPointedMap C D)
  (hD : isGroupoid (D .carrier))
  : Equiv (BookPointedMap X (PointedPullback B C D f g)) (PbgPointedPullbackOfMaps X B C D f g)
  ≔ let W ≔ PbgConeData (X .carrier) (B .carrier) (C .carrier) (D .carrier) (f .fst) (g .fst) in
    let Q ≔ PbgConeQ X B C D f g in
    compose_equiv (BookPointedMap X (PointedPullback B C D f g)) (Σ W (PbgPointedCone X B C D f g))
      (PbgPointedPullbackOfMaps X B C D f g)
      (pbg_pointed_cone_split_equiv X B C D f g)
      (compose_equiv (Σ W (PbgPointedCone X B C D f g)) (Σ W (w ↦ Σ (Q w) (PbgConeL X B C D f g w)))
        (PbgPointedPullbackOfMaps X B C D f g)
        (family_equiv W (PbgPointedCone X B C D f g) (w ↦ Σ (Q w) (PbgConeL X B C D f g w))
          (pbg_pointed_cone_left_equiv X B C D f g))
        (compose_equiv (Σ W (w ↦ Σ (Q w) (PbgConeL X B C D f g w))) (Σ W (w ↦ Σ (Q w) (PbgConeR X B C D f g w)))
          (PbgPointedPullbackOfMaps X B C D f g)
          (family_equiv W (w ↦ Σ (Q w) (PbgConeL X B C D f g w)) (w ↦ Σ (Q w) (PbgConeR X B C D f g w))
            (w ↦ family_equiv (Q w) (PbgConeL X B C D f g w) (PbgConeR X B C D f g w)
              (pbg_pointed_cone_lr_equiv X B C D f g hD w)))
          (compose_equiv (Σ W (w ↦ Σ (Q w) (PbgConeR X B C D f g w))) (PbgPointedHomotopyPairs X B C D f g)
            (PbgPointedPullbackOfMaps X B C D f g)
            (pbg_pointed_reassoc_equiv X B C D f g)
            (family_equiv (Product (BookPointedMap X B) (BookPointedMap X C))
              (bc ↦ PointedHomotopy X D (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g))
              (bc ↦ Id (BookPointedMap X D) (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g))
              (bc ↦ canonical_inverse_equiv
                (Id (BookPointedMap X D) (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g))
                (PointedHomotopy X D (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g))
                (pointed_map_path_equiv X D (book_pointed_compose X B D (bc .fst) f) (book_pointed_compose X C D (bc .snd) g)))))))

{` The group version. HomPullback K is Hom(K,H) ×_{Hom(K,G)} Hom(K,H'),
   the pullback of f ∘ - and f' ∘ - (group_hom_compose K H G k f = f ∘ k). `}
def HomPullback (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group) : Type
  ≔ TypePullback (GroupHom K H) (GroupHom K H') (GroupHom K G)
      (k ↦ group_hom_compose K H G k f) (k ↦ group_hom_compose K H' G k f')

def pbg_hom_pullback_classifying_equiv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  : Equiv (PbgPointedPullbackOfMaps (BG K) (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f'))
      (HomPullback G H H' f f' K)
  ≔ quasi_inverse_equiv (PbgPointedPullbackOfMaps (BG K) (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f'))
      (HomPullback G H H' f f' K)
      (t ↦ ((mkhom K H (t .fst .fst), mkhom K H' (t .fst .snd)), (classifying_map ≔ t .snd)))
      (t ↦ ((hom_B K H (t .fst .fst), hom_B K H' (t .fst .snd)), t .snd .classifying_map))
      (t ↦ refl t) (t ↦ refl t)

{` xca (line 479): Hom(K, H ×_G H') ≃ Hom(K,H) ×_{Hom(K,G)} Hom(K,H'),
   induced by the pointed universal property (with A ≔ BK) and
   xca:ptd-conn-to-comp (maps from the connected BK into BH ×_{BG} BH'
   land in the component of the point). `}
def pullback_group_hom_equiv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  : Equiv (GroupHom K (pullback_group G H H' f f')) (HomPullback G H H' f f' K)
  ≔ let P ≔ pullback_group G H H' f f' in
    let S ≔ pbg_space G H H' f f' in
    let pt ≔ pbg_point G H H' f f' in
    compose_equiv (GroupHom K P) (BookPointedMap (BG K) (BG P)) (HomPullback G H H' f f' K)
      (group_hom_classifying_equiv K P)
      (compose_equiv (BookPointedMap (BG K) (BG P)) (BookPointedMap (BG K) (S, pt)) (HomPullback G H H' f f' K)
        (canonical_inverse_equiv (BookPointedMap (BG K) (S, pt)) (BookPointedMap (BG K) (BG P))
          (pointed_maps_into_component (BG K) (bg_connected K) S pt))
        (compose_equiv (BookPointedMap (BG K) (S, pt))
          (PbgPointedPullbackOfMaps (BG K) (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f'))
          (HomPullback G H H' f f' K)
          (pointed_pullback_universal_property (BG K) (BG H) (BG H') (BG G) (hom_B H G f) (hom_B H' G f') (bg_groupoid G))
          (pbg_hom_pullback_classifying_equiv G H H' f f' K)))

{` In the book's direction. `}
def pullback_group_hom_equiv_book (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  : Equiv (HomPullback G H H' f f' K) (GroupHom K (pullback_group G H H' f f'))
  ≔ canonical_inverse_equiv (GroupHom K (pullback_group G H H' f f')) (HomPullback G H H' f f' K)
      (pullback_group_hom_equiv G H H' f f' K)

{` The equivalence is the one induced by composing with the projections:
   its components are prj_H ∘ k and prj_H' ∘ k. `}
def pullback_group_hom_equiv_left (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  (k : GroupHom K (pullback_group G H H' f f'))
  : Id (GroupHom K H) (pullback_group_hom_equiv G H H' f f' K .map k .fst .fst)
      (group_hom_compose K (pullback_group G H H' f f') H k (pullback_group_proj_left G H H' f f'))
  ≔ let P ≔ pullback_group G H H' f f' in
    let a ≔ k .classifying_map .snd .fst .fst .fst in
    equiv_inverse_map (Id (GroupHom K H) (pullback_group_hom_equiv G H H' f f' K .map k .fst .fst)
        (group_hom_compose K P H k (pullback_group_proj_left G H H' f f')))
      (PointedHomotopy (BG K) (BG H) (hom_B K H (pullback_group_hom_equiv G H H' f f' K .map k .fst .fst))
        (hom_B K H (group_hom_compose K P H k (pullback_group_proj_left G H H' f f'))))
      (group_hom_path_equiv K H (pullback_group_hom_equiv G H H' f f' K .map k .fst .fst)
        (group_hom_compose K P H k (pullback_group_proj_left G H H' f f')))
      ((x ↦ refl (k .classifying_map .fst x .fst .fst .fst)),
       concat (Id (BG H .carrier) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst))
         (concat (BG H .carrier) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst)
           (k .classifying_map .fst (shape K) .fst .fst .fst) a (refl (k .classifying_map .fst (shape K) .fst .fst .fst)))
         a (concat (BG H .carrier) (shape H) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst) (refl (shape H)) a)
         (concat_p1 (BG H .carrier) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst) a)
         (inverse (Id (BG H .carrier) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst))
           (concat (BG H .carrier) (shape H) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst) (refl (shape H)) a)
           a (concat_1p (BG H .carrier) (shape H) (k .classifying_map .fst (shape K) .fst .fst .fst) a)))

def pullback_group_hom_equiv_right (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (K : Group)
  (k : GroupHom K (pullback_group G H H' f f'))
  : Id (GroupHom K H') (pullback_group_hom_equiv G H H' f f' K .map k .fst .snd)
      (group_hom_compose K (pullback_group G H H' f f') H' k (pullback_group_proj_right G H H' f f'))
  ≔ let P ≔ pullback_group G H H' f f' in
    let a ≔ k .classifying_map .snd .fst .fst .snd in
    let y ≔ k .classifying_map .fst (shape K) .fst .fst .snd in
    equiv_inverse_map (Id (GroupHom K H') (pullback_group_hom_equiv G H H' f f' K .map k .fst .snd)
        (group_hom_compose K P H' k (pullback_group_proj_right G H H' f f')))
      (PointedHomotopy (BG K) (BG H') (hom_B K H' (pullback_group_hom_equiv G H H' f f' K .map k .fst .snd))
        (hom_B K H' (group_hom_compose K P H' k (pullback_group_proj_right G H H' f f'))))
      (group_hom_path_equiv K H' (pullback_group_hom_equiv G H H' f f' K .map k .fst .snd)
        (group_hom_compose K P H' k (pullback_group_proj_right G H H' f f')))
      ((x ↦ refl (k .classifying_map .fst x .fst .fst .snd)),
       concat (Id (BG H' .carrier) (shape H') y)
         (concat (BG H' .carrier) (shape H') y y a (refl y))
         a (concat (BG H' .carrier) (shape H') (shape H') y (refl (shape H')) a)
         (concat_p1 (BG H' .carrier) (shape H') y a)
         (inverse (Id (BG H' .carrier) (shape H') y)
           (concat (BG H' .carrier) (shape H') (shape H') y (refl (shape H')) a)
           a (concat_1p (BG H' .carrier) (shape H') y a)))
