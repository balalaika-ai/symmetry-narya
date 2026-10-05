export "822-pullback-group-symmetries"
export "507-subgroups-monos-equiv"

{` Chapter 9 (subgroups.tex), the exercise at line 1801: the intersection
   of abstract subgroups of an abstract group, agreeing with
   def:intersectionofgroups for monomorphisms.

   An abstract subgroup of an abstract group 𝒢 is a family of propositions
   on the carrier containing the unit and closed under multiplication and
   inverses; the intersection 𝓗 ∩ 𝓚 is the pointwise conjunction. For a
   monomorphism (H, f) into a group G the symmetries picked out by it
   (SymmetryPickedOut, lem:E-preserves-symms) form an abstract subgroup of
   abstr(G), and the abstract subgroup picked out by the intersection
   H ∩ H' (group_mono_intersection of chapter 8, the pullback group with
   f ∘ prj_H) is the intersection of the abstract subgroups picked out by
   H and H' (via USym(H ×_G H') ≃ USym H ×_{USym G} USym H', module 822). `}

def IsAbstractSubgroup (AG : AbstractGroup) (P : AG .carrier → Type) : Type
  ≔ Product ((x : AG .carrier) → isProp (P x))
      (Product (P (AG .unit))
        (Product ((x y : AG .carrier) → P x → P y → P (AG .mul x y)) ((x : AG .carrier) → P x → P (AG .inv x))))

def AbstractSubgroups (AG : AbstractGroup) : Type ≔ Σ (AG .carrier → Type) (IsAbstractSubgroup AG)

def abstract_subgroup_intersection (AG : AbstractGroup) (P Q : AbstractSubgroups AG) : AbstractSubgroups AG
  ≔ (x ↦ Product (P .fst x) (Q .fst x),
     (x ↦ product_prop (P .fst x) (Q .fst x) (P .snd .fst x) (Q .snd .fst x),
      ((P .snd .snd .fst, Q .snd .snd .fst),
       (x y a b ↦ (P .snd .snd .snd .fst x y (a .fst) (b .fst), Q .snd .snd .snd .fst x y (a .snd) (b .snd)),
        x a ↦ (P .snd .snd .snd .snd x (a .fst), Q .snd .snd .snd .snd x (a .snd))))))

{` The symmetries picked out by a monomorphism form an abstract subgroup. `}
def picked_out_unit (G : Group) (m : GroupMonos G) : SymmetryPickedOut G m (usym_unit G)
  ≔ let H ≔ m .fst in
    let f ≔ m .snd .fst in
    mere (Σ (USym H) (h ↦ Id (USym G) (usym_unit G) (usym_hom H G f h)))
      (usym_unit H, inverse (USym G) (usym_hom H G f (usym_unit H)) (usym_unit G) (usym_hom_unit H G f))

def picked_out_mul (G : Group) (m : GroupMonos G) (x y : USym G) (a : SymmetryPickedOut G m x) (b : SymmetryPickedOut G m y)
  : SymmetryPickedOut G m (usym_mul G x y)
  ≔ let H ≔ m .fst in
    let f ≔ m .snd .fst in
    let F ≔ usym_hom H G f in
    let W ≔ Σ (USym H) (h ↦ Id (USym G) (usym_mul G x y) (F h)) in
    mere_rec (Σ (USym H) (h ↦ Id (USym G) x (F h))) (Mere W) (mere_isprop W)
      (u ↦ mere_rec (Σ (USym H) (h ↦ Id (USym G) y (F h))) (Mere W) (mere_isprop W)
        (v ↦ mere W (usym_mul H (u .fst) (v .fst),
          calc
            usym_mul G x y = usym_mul G (F (u .fst)) y by refl ((t ↦ usym_mul G t y) : USym G → USym G) (u .snd)
            = usym_mul G (F (u .fst)) (F (v .fst)) by refl (usym_mul G (F (u .fst))) (v .snd)
            = F (usym_mul H (u .fst) (v .fst))
              by inverse (USym G) (F (usym_mul H (u .fst) (v .fst))) (usym_mul G (F (u .fst)) (F (v .fst)))
                   (usym_hom_mul H G f (u .fst) (v .fst)) ∎))
        b)
      a

def picked_out_inv (G : Group) (m : GroupMonos G) (x : USym G) (a : SymmetryPickedOut G m x)
  : SymmetryPickedOut G m (usym_inv G x)
  ≔ let H ≔ m .fst in
    let f ≔ m .snd .fst in
    let F ≔ usym_hom H G f in
    let W ≔ Σ (USym H) (h ↦ Id (USym G) (usym_inv G x) (F h)) in
    mere_rec (Σ (USym H) (h ↦ Id (USym G) x (F h))) (Mere W) (mere_isprop W)
      (u ↦ mere W (usym_inv H (u .fst),
        concat (USym G) (usym_inv G x) (usym_inv G (F (u .fst))) (F (usym_inv H (u .fst)))
          (refl (usym_inv G) (u .snd))
          (inverse (USym G) (F (usym_inv H (u .fst))) (usym_inv G (F (u .fst))) (usym_hom_inv H G f (u .fst)))))
      a

def picked_out_abstract_subgroup (G : Group) (m : GroupMonos G) : AbstractSubgroups (abstr G)
  ≔ (SymmetryPickedOut G m,
     (x ↦ mere_isprop (Σ (USym (m .fst)) (h ↦ Id (USym G) x (usym_hom (m .fst) G (m .snd .fst) h))),
      (picked_out_unit G m, (picked_out_mul G m, picked_out_inv G m))))

{` The exercise: g is picked out by H ∩ H' iff it is picked out by H and
   by H'. `}
def intersection_picked_out_both (G : Group) (m m' : GroupMonos G) (g : USym G)
  (t : SymmetryPickedOut G (group_mono_intersection G m m') g)
  : Product (SymmetryPickedOut G m g) (SymmetryPickedOut G m' g)
  ≔ let H ≔ m .fst in let f ≔ m .snd .fst in
    let H' ≔ m' .fst in let f' ≔ m' .snd .fst in
    let P ≔ pullback_group G H H' f f' in
    let p1 ≔ pullback_group_proj_left G H H' f f' in
    let p2 ≔ pullback_group_proj_right G H H' f f' in
    let A ≔ Σ (USym H) (h ↦ Id (USym G) g (usym_hom H G f h)) in
    let A' ≔ Σ (USym H') (h ↦ Id (USym G) g (usym_hom H' G f' h)) in
    let R ≔ Product (Mere A) (Mere A') in
    mere_rec (Σ (USym P) (w ↦ Id (USym G) g (usym_hom P G (group_hom_compose P H G p1 f) w))) R
      (product_prop (Mere A) (Mere A') (mere_isprop A) (mere_isprop A'))
      (u ↦
        let w ≔ u .fst in
        let e1 : Id (USym G) g (usym_hom H G f (usym_hom P H p1 w))
          ≔ concat (USym G) g (usym_hom P G (group_hom_compose P H G p1 f) w) (usym_hom H G f (usym_hom P H p1 w))
              (u .snd) (usym_hom_compose P H G p1 f (refl w)) in
        (mere A (usym_hom P H p1 w, e1),
         mere A' (usym_hom P H' p2 w,
           concat (USym G) g (usym_hom H G f (usym_hom P H p1 w)) (usym_hom H' G f' (usym_hom P H' p2 w))
             e1 (pullback_group_usym_square G H H' f f' w))))
      t

def both_picked_out_intersection (G : Group) (m m' : GroupMonos G) (g : USym G)
  (ab : Product (SymmetryPickedOut G m g) (SymmetryPickedOut G m' g))
  : SymmetryPickedOut G (group_mono_intersection G m m') g
  ≔ let H ≔ m .fst in let f ≔ m .snd .fst in
    let H' ≔ m' .fst in let f' ≔ m' .snd .fst in
    let P ≔ pullback_group G H H' f f' in
    let p1 ≔ pullback_group_proj_left G H H' f f' in
    let PU ≔ PullbackUSym G H H' f f' in
    let E ≔ pullback_group_usym_equiv G H H' f f' in
    let W ≔ Σ (USym P) (w ↦ Id (USym G) g (usym_hom P G (group_hom_compose P H G p1 f) w)) in
    mere_rec (Σ (USym H) (h ↦ Id (USym G) g (usym_hom H G f h))) (Mere W) (mere_isprop W)
      (u ↦ mere_rec (Σ (USym H') (h ↦ Id (USym G) g (usym_hom H' G f' h))) (Mere W) (mere_isprop W)
        (v ↦
          let t : PU ≔ ((u .fst, v .fst),
            concat (USym G) (usym_hom H G f (u .fst)) g (usym_hom H' G f' (v .fst))
              (inverse (USym G) g (usym_hom H G f (u .fst)) (u .snd)) (v .snd)) in
          let w ≔ equiv_inverse_map (USym P) PU E t in
          let c : Id (USym H) (usym_hom P H p1 w) (u .fst)
            ≔ refl ((s ↦ s .fst .fst) : PU → USym H) (equiv_counit (USym P) PU E t) in
          mere W (w,
            calc
              g = usym_hom H G f (u .fst) by u .snd
              = usym_hom H G f (usym_hom P H p1 w)
                by refl (usym_hom H G f) (inverse (USym H) (usym_hom P H p1 w) (u .fst) c)
              = usym_hom P G (group_hom_compose P H G p1 f) w
                by inverse (USym G) (usym_hom P G (group_hom_compose P H G p1 f) w) (usym_hom H G f (usym_hom P H p1 w))
                     (usym_hom_compose P H G p1 f (refl w)) ∎))
        (ab .snd))
      (ab .fst)

def intersection_picked_out_iff (G : Group) (m m' : GroupMonos G) (g : USym G)
  : Product
      (SymmetryPickedOut G (group_mono_intersection G m m') g → Product (SymmetryPickedOut G m g) (SymmetryPickedOut G m' g))
      (Product (SymmetryPickedOut G m g) (SymmetryPickedOut G m' g) → SymmetryPickedOut G (group_mono_intersection G m m') g)
  ≔ (intersection_picked_out_both G m m' g, both_picked_out_intersection G m m' g)

{` In terms of abstract subgroups: the carrier family of the abstract
   subgroup of H ∩ H' agrees pointwise with that of the intersection of
   the abstract subgroups of H and H'. `}
def intersection_abstract_subgroup_agrees (G : Group) (m m' : GroupMonos G) (g : USym G)
  : Product
      (picked_out_abstract_subgroup G (group_mono_intersection G m m') .fst g
        → abstract_subgroup_intersection (abstr G) (picked_out_abstract_subgroup G m) (picked_out_abstract_subgroup G m') .fst g)
      (abstract_subgroup_intersection (abstr G) (picked_out_abstract_subgroup G m) (picked_out_abstract_subgroup G m') .fst g
        → picked_out_abstract_subgroup G (group_mono_intersection G m m') .fst g)
  ≔ intersection_picked_out_iff G m m' g

{` Litmus: a monomorphism picks out the images of its symmetries, and the
   intersection of H with itself picks out the same symmetries. `}
def picked_out_image (G : Group) (m : GroupMonos G) (h : USym (m .fst))
  : picked_out_abstract_subgroup G m .fst (usym_hom (m .fst) G (m .snd .fst) h)
  ≔ mere (Σ (USym (m .fst)) (k ↦ Id (USym G) (usym_hom (m .fst) G (m .snd .fst) h) (usym_hom (m .fst) G (m .snd .fst) k)))
      (h, refl (usym_hom (m .fst) G (m .snd .fst) h))

def picked_out_self_intersection (G : Group) (m : GroupMonos G) (g : USym G) (t : SymmetryPickedOut G m g)
  : SymmetryPickedOut G (group_mono_intersection G m m) g
  ≔ both_picked_out_intersection G m m g (t, t)
