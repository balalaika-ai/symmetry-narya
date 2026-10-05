export "666-pullbacks"
export "404-group-examples"

{` Chapter 8 (congp.tex), section "The pullback": def:intersectionofgroups
   (line 457), the pullback of two homomorphisms with common target.

   Conventions. TypePullback B C D f g (module 666) is
   Σ_{(b,c) : B × C} f(b) = g(c). For f : Hom(H,G), f' : Hom(H',G) with
   pointing paths p_f : sh_G = Bf(sh_H) (hom_point), the book's point
   (sh_H, sh_H', p_{f'} p_f⁻¹) has as third component the path
   Bf(sh_H) = Bf'(sh_H') that first follows p_f⁻¹ and then p_{f'}, in
   concatenation order `concat (inverse p_f) p_f'` (pbg_twist_point). `}

{` The family of the pullback, as a named function (so that its
   dependent identity types are recognised). `}
def pbg_fam (B C D : Type) (f : B → D) (g : C → D) (bc : Product B C) : Type
  ≔ Id D (f (bc .fst)) (g (bc .snd))

{` Squares. In Narya a square with sides r : x00 = x01, s : x10 = x11,
   u : x00 = x10, v : x01 = x11 is an element of Id (Id A) r s u v; it is
   equivalent to the equation u · s = r · v (concatenation order). `}
def pbg_square_base (A : Type) (x00 x10 : A) (u v : Id A x00 x10)
  : Equiv (Id (Id A x00 x10) u v)
      (Id (Id A x00 x10) (concat A x00 x10 x10 u (refl x10)) (concat A x00 x00 x10 (refl x00) v))
  ≔ id_to_equiv (Id (Id A x00 x10) u v)
      (Id (Id A x00 x10) (concat A x00 x10 x10 u (refl x10)) (concat A x00 x00 x10 (refl x00) v))
      (refl ((a b ↦ Id (Id A x00 x10) a b) : Id A x00 x10 → Id A x00 x10 → Type)
        (inverse (Id A x00 x10) (concat A x00 x10 x10 u (refl x10)) u (concat_p1 A x00 x10 u))
        (inverse (Id A x00 x10) (concat A x00 x00 x10 (refl x00) v) v (concat_1p A x00 x10 v)))

def pbg_square_equiv (A : Type) (x00 x01 : A) (r : Id A x00 x01) (x10 x11 : A) (s : Id A x10 x11)
  (u : Id A x00 x10) (v : Id A x01 x11)
  : Equiv (Id (Id A) r s u v) (Id (Id A x00 x11) (concat A x00 x10 x11 u s) (concat A x00 x01 x11 r v))
  ≔ J A x00
      (x01 r ↦ (x11 : A) (s : Id A x10 x11) (v : Id A x01 x11)
        → Equiv (Id (Id A) r s u v) (Id (Id A x00 x11) (concat A x00 x10 x11 u s) (concat A x00 x01 x11 r v)))
      (x11 s ↦ J A x10
        (x11 s ↦ (v : Id A x00 x11)
          → Equiv (Id (Id A) (refl x00) s u v)
              (Id (Id A x00 x11) (concat A x00 x10 x11 u s) (concat A x00 x00 x11 (refl x00) v)))
        (v ↦ pbg_square_base A x00 x10 u v) x11 s)
      x01 r x11 s v

{` The twisted path p⁻¹ p' : y = y' for p : g0 = y and p' : g0 = y'. `}
def pbg_twist (D : Type) (g0 y y' : D) (p : Id D g0 y) (p' : Id D g0 y') : Id D y y'
  ≔ concat D y g0 y' (inverse D g0 y p) p'

{` The square condition d · v = u · d (d the twisted path) is logically
   equivalent to the equality of the conjugated loops p u p⁻¹ = p' v p'⁻¹
   (written in concatenation order as pointed_loop_conjugate). `}
def PbgSquareCondition (D : Type) (g0 y y' : D) (p : Id D g0 y) (p' : Id D g0 y') (u : Id D y y) (v : Id D y' y')
  : Type
  ≔ Id (Id D y y') (concat D y y' y' (pbg_twist D g0 y y' p p') v) (concat D y y y' u (pbg_twist D g0 y y' p p'))

def PbgConjugateCondition (D : Type) (g0 y y' : D) (p : Id D g0 y) (p' : Id D g0 y') (u : Id D y y) (v : Id D y' y')
  : Type
  ≔ Id (Id D g0 g0) (pointed_loop_conjugate D g0 y p u) (pointed_loop_conjugate D g0 y' p' v)

def pbg_twist_refl (D : Type) (g0 : D)
  : Id (Id D g0 g0) (pbg_twist D g0 g0 g0 (refl g0) (refl g0)) (refl g0)
  ≔ concat_inverse_left D g0 g0 (refl g0)

def pbg_twist_left (D : Type) (g0 : D) (v : Id D g0 g0)
  : Id (Id D g0 g0) (concat D g0 g0 g0 (pbg_twist D g0 g0 g0 (refl g0) (refl g0)) v) v
  ≔ concat (Id D g0 g0) (concat D g0 g0 g0 (pbg_twist D g0 g0 g0 (refl g0) (refl g0)) v)
      (concat D g0 g0 g0 (refl g0) v) v
      (refl ((c ↦ concat D g0 g0 g0 c v) : Id D g0 g0 → Id D g0 g0) (pbg_twist_refl D g0))
      (concat_1p D g0 g0 v)

def pbg_twist_right (D : Type) (g0 : D) (u : Id D g0 g0)
  : Id (Id D g0 g0) (concat D g0 g0 g0 u (pbg_twist D g0 g0 g0 (refl g0) (refl g0))) u
  ≔ concat (Id D g0 g0) (concat D g0 g0 g0 u (pbg_twist D g0 g0 g0 (refl g0) (refl g0)))
      (concat D g0 g0 g0 u (refl g0)) u
      (refl (concat D g0 g0 g0 u) (pbg_twist_refl D g0))
      (concat_p1 D g0 g0 u)

def pbg_conditions_base (D : Type) (g0 : D) (u v : Id D g0 g0)
  : Product
      (PbgSquareCondition D g0 g0 g0 (refl g0) (refl g0) u v → PbgConjugateCondition D g0 g0 g0 (refl g0) (refl g0) u v)
      (PbgConjugateCondition D g0 g0 g0 (refl g0) (refl g0) u v → PbgSquareCondition D g0 g0 g0 (refl g0) (refl g0) u v)
  ≔ let c ≔ pbg_twist D g0 g0 g0 (refl g0) (refl g0) in
    (h ↦ calc
       pointed_loop_conjugate D g0 g0 (refl g0) u = u by loop_conjugate_at_refl D g0 u
       = concat D g0 g0 g0 u c
         by inverse (Id D g0 g0) (concat D g0 g0 g0 u c) u (pbg_twist_right D g0 u)
       = concat D g0 g0 g0 c v by inverse (Id D g0 g0) (concat D g0 g0 g0 c v) (concat D g0 g0 g0 u c) h
       = v by pbg_twist_left D g0 v
       = pointed_loop_conjugate D g0 g0 (refl g0) v
         by inverse (Id D g0 g0) (pointed_loop_conjugate D g0 g0 (refl g0) v) v (loop_conjugate_at_refl D g0 v) ∎,
     k ↦ calc
       concat D g0 g0 g0 c v = v by pbg_twist_left D g0 v
       = pointed_loop_conjugate D g0 g0 (refl g0) v
         by inverse (Id D g0 g0) (pointed_loop_conjugate D g0 g0 (refl g0) v) v (loop_conjugate_at_refl D g0 v)
       = pointed_loop_conjugate D g0 g0 (refl g0) u
         by inverse (Id D g0 g0) (pointed_loop_conjugate D g0 g0 (refl g0) u)
           (pointed_loop_conjugate D g0 g0 (refl g0) v) k
       = u by loop_conjugate_at_refl D g0 u
       = concat D g0 g0 g0 u c
         by inverse (Id D g0 g0) (concat D g0 g0 g0 u c) u (pbg_twist_right D g0 u) ∎)

def pbg_conditions (D : Type) (g0 y : D) (p : Id D g0 y) (u : Id D y y) (y' : D) (p' : Id D g0 y') (v : Id D y' y')
  : Product (PbgSquareCondition D g0 y y' p p' u v → PbgConjugateCondition D g0 y y' p p' u v)
      (PbgConjugateCondition D g0 y y' p p' u v → PbgSquareCondition D g0 y y' p p' u v)
  ≔ J D g0
      (y p ↦ (u : Id D y y) (y' : D) (p' : Id D g0 y') (v : Id D y' y')
        → Product (PbgSquareCondition D g0 y y' p p' u v → PbgConjugateCondition D g0 y y' p p' u v)
            (PbgConjugateCondition D g0 y y' p p' u v → PbgSquareCondition D g0 y y' p p' u v))
      (u y' p' ↦ J D g0
        (y' p' ↦ (v : Id D y' y')
          → Product (PbgSquareCondition D g0 g0 y' (refl g0) p' u v → PbgConjugateCondition D g0 g0 y' (refl g0) p' u v)
              (PbgConjugateCondition D g0 g0 y' (refl g0) p' u v → PbgSquareCondition D g0 g0 y' (refl g0) p' u v))
        (v ↦ pbg_conditions_base D g0 u v) y' p')
      y p u y' p' v

{` def:intersectionofgroups. The pullback type BH ×_{BG} BH', its point
   (sh_H, sh_H', p_{f'} p_f⁻¹), and the pullback group H ×_G H' as the
   automorphism group of that point, i.e. the pointed component
   (def:automorphism-group). `}
def pbg_space (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Type
  ≔ TypePullback (BG H .carrier) (BG H' .carrier) (BG G .carrier) (hom_function H G f) (hom_function H' G f')

def pbg_twist_point (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id (BG G .carrier) (hom_function H G f (shape H)) (hom_function H' G f' (shape H'))
  ≔ pbg_twist (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_function H' G f' (shape H'))
      (hom_point H G f) (hom_point H' G f')

def pbg_point (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : pbg_space G H H' f f'
  ≔ ((shape H, shape H'), pbg_twist_point G H H' f f')

def pbg_space_groupoid (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : isGroupoid (pbg_space G H H' f f')
  ≔ hlevel_to_groupoid (pbg_space G H H' f f')
      (hlevel_sigma (suc. (suc. (suc. zero.)))
        (Product (BG H .carrier) (BG H' .carrier))
        (pbg_fam (BG H .carrier) (BG H' .carrier) (BG G .carrier) (hom_function H G f) (hom_function H' G f'))
        (hlevel_product (suc. (suc. (suc. zero.))) (BG H .carrier) (BG H' .carrier)
          (groupoid_to_hlevel (BG H .carrier) (bg_groupoid H)) (groupoid_to_hlevel (BG H' .carrier) (bg_groupoid H')))
        (bc ↦ groupoid_to_hlevel (Id (BG G .carrier) (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd)))
          (set_is_groupoid (Id (BG G .carrier) (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd)))
            (bg_groupoid G (hom_function H G f (bc .fst)) (hom_function H' G f' (bc .snd))))))

def pullback_group (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Group
  ≔ automorphism_group (pbg_space G H H' f f') (pbg_space_groupoid G H H' f f') (pbg_point G H H' f f')

def pullback_group_classifying (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id Pointed (BG (pullback_group G H H' f f'))
      (NativeComponent (pbg_space G H H' f f') (pbg_point G H H' f f'),
       component_point (pbg_space G H H' f f') (pbg_point G H H' f f'))
  ≔ refl (BG (pullback_group G H H' f f'))

{` The two projections H ×_G H' → H and H ×_G H' → H', pointed by refl. `}
def pullback_group_proj_left (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : GroupHom (pullback_group G H H' f f') H
  ≔ mkhom (pullback_group G H H' f f') H ((u ↦ u .fst .fst .fst), refl (shape H))

def pullback_group_proj_right (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : GroupHom (pullback_group G H H' f f') H'
  ≔ mkhom (pullback_group G H H' f f') H' ((u ↦ u .fst .fst .snd), refl (shape H'))

{` The pullback square of groups commutes: f ∘ prj_H = f' ∘ prj_H' in
   Hom(H ×_G H', G). The homotopy is u ↦ (third component of u); its
   pointing coherence is p_f · (p_f⁻¹ p_{f'}) = p_{f'}. `}
def pullback_group_square_coherence (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id (Id (BG G .carrier) (shape G) (hom_function H' G f' (shape H')))
      (concat (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_function H' G f' (shape H'))
        (concat (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_function H G f (shape H))
          (hom_point H G f) (refl (hom_function H G f) (refl (shape H))))
        (pbg_twist_point G H H' f f'))
      (concat (BG G .carrier) (shape G) (hom_function H' G f' (shape H')) (hom_function H' G f' (shape H'))
        (hom_point H' G f') (refl (hom_function H' G f') (refl (shape H'))))
  ≔ let D ≔ BG G .carrier in
    let g0 ≔ shape G in
    let y ≔ hom_function H G f (shape H) in
    let y' ≔ hom_function H' G f' (shape H') in
    let p ≔ hom_point H G f in
    let p' ≔ hom_point H' G f' in
    calc
      concat D g0 y y' (concat D g0 y y p (refl y)) (pbg_twist_point G H H' f f')
      = concat D g0 y y' p (pbg_twist_point G H H' f f')
        by refl ((z ↦ concat D g0 y y' z (pbg_twist_point G H H' f f')) : Id D g0 y → Id D g0 y') (concat_p1 D g0 y p)
      = concat D g0 g0 y' (concat D g0 y g0 p (inverse D g0 y p)) p'
        by inverse (Id D g0 y') (concat D g0 g0 y' (concat D g0 y g0 p (inverse D g0 y p)) p')
          (concat D g0 y y' p (pbg_twist_point G H H' f f'))
          (concat_assoc D g0 y g0 y' p (inverse D g0 y p) p')
      = concat D g0 g0 y' (refl g0) p'
        by refl ((z ↦ concat D g0 g0 y' z p') : Id D g0 g0 → Id D g0 y') (concat_inverse_right D g0 y p)
      = p' by concat_1p D g0 y' p'
      = concat D g0 y' y' p' (refl y') by inverse (Id D g0 y') (concat D g0 y' y' p' (refl y')) p' (concat_p1 D g0 y' p') ∎

def pullback_group_square (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id (GroupHom (pullback_group G H H' f f') G)
      (group_hom_compose (pullback_group G H H' f f') H G (pullback_group_proj_left G H H' f f') f)
      (group_hom_compose (pullback_group G H H' f f') H' G (pullback_group_proj_right G H H' f f') f')
  ≔ let P ≔ pullback_group G H H' f f' in
    equiv_inverse_map
      (Id (GroupHom P G) (group_hom_compose P H G (pullback_group_proj_left G H H' f f') f)
        (group_hom_compose P H' G (pullback_group_proj_right G H H' f f') f'))
      (PointedHomotopy (BG P) (BG G)
        (hom_B P G (group_hom_compose P H G (pullback_group_proj_left G H H' f f') f))
        (hom_B P G (group_hom_compose P H' G (pullback_group_proj_right G H H' f f') f')))
      (group_hom_path_equiv P G (group_hom_compose P H G (pullback_group_proj_left G H H' f f') f)
        (group_hom_compose P H' G (pullback_group_proj_right G H H' f f') f'))
      ((u ↦ u .fst .snd), pullback_group_square_coherence G H H' f f')

{` Litmus: the projections send the shape of H ×_G H' to the shapes, and
   the commuting homotopy at the shape is the twisted point path. `}
def pullback_group_litmus_shape (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Id (Product (BG H .carrier) (BG H' .carrier))
      (hom_function (pullback_group G H H' f f') H (pullback_group_proj_left G H H' f f') (shape (pullback_group G H H' f f')),
       hom_function (pullback_group G H H' f f') H' (pullback_group_proj_right G H H' f f') (shape (pullback_group G H H' f f')))
      (shape H, shape H')
  ≔ refl ((shape H, shape H') : Product (BG H .carrier) (BG H' .carrier))
