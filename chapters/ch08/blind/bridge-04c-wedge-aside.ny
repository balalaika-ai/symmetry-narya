export "bridge-04b-wedge"

{` Bridges bridge for the aside of xca:whatAREabeliangroups (congp.tex:593):
   an unpointed r with r ∘ i = fold makes G abelian (our
   unpointed_extension_abelian, after identifying the blind fold and i with
   ours), and Ω fold sends i1^g(g), i2^g(h) to g, h; so it sends the
   commutator x y x⁻¹ y⁻¹ (book products) to g h g⁻¹ h⁻¹ = refl. `}

def bw_commutator_trivial (A : Type) (a : A) (g h : Id A a a)
  (ab : Id (Id A a a) (concat A a a a h g) (concat A a a a g h))
  : Id (Id A a a) (concat A a a a (concat A a a a (concat A a a a (inverse A a a h) (inverse A a a g)) h) g) (refl a)
  ≔ let L ≔ Id A a a in
    let c : L → L → L ≔ concat A a a a in
    let hi ≔ inverse A a a h in let gi ≔ inverse A a a g in
    calc
      c (c (c hi gi) h) g
      = c (c hi gi) (c h g) by concat_assoc A a a a a (c hi gi) h g
      = c (c hi gi) (c g h) by refl (c (c hi gi)) ab
      = c hi (c gi (c g h)) by concat_assoc A a a a a hi gi (c g h)
      = c hi (c (c gi g) h) by refl (c hi) (inverse L (c (c gi g) h) (c gi (c g h)) (concat_assoc A a a a a gi g h))
      = c hi (c (refl a) h) by refl ((u ↦ c hi (c u h)) : L → L) (concat_inverse_left A a a g)
      = c hi h by refl (c hi) (concat_1p A a a h)
      = refl a by concat_inverse_left A a a h ∎

{` Ω fold ∘ i1^g = id and Ω fold ∘ i2^g = id for the blind fold. `}
def bw_fold_loop1 (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W) (g : USym G)
  : Id (USym G)
      (loops_map (blind_wedge_pointed (BG G) (BG G) W) (BG G) (D .fst) (blind_wedge_i1g (BG G) (BG G) W g)) g
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let V ≔ wedge_pointed (BG G) (BG G) W' in
    let j ≔ wedge_incl1_pointed (BG G) (BG G) W' in
    calc
      loops_map V (BG G) (D .fst) (wedge_loop1 (BG G) (BG G) W' g)
      = loops_map V (BG G) (D .fst) (loops_map (BG G) V j g)
        by refl (loops_map V (BG G) (D .fst)) (wedge_loop1_loops_map (BG G) (BG G) W' g)
      = loops_map (BG G) (BG G) (book_pointed_compose (BG G) V (BG G) j (D .fst)) g
        by inverse (USym G) (loops_map (BG G) (BG G) (book_pointed_compose (BG G) V (BG G) j (D .fst)) g)
             (loops_map V (BG G) (D .fst) (loops_map (BG G) V j g))
             (loops_map_compose_pointwise (BG G) V (BG G) j (D .fst) g)
      = loops_map (BG G) (BG G) (blind_pointed_id (BG G)) g
        by refl ((k ↦ loops_map (BG G) (BG G) k g) : BookPointedMap (BG G) (BG G) → USym G) (D .snd .fst .fst)
      = g by loop_conjugate_at_refl (BG G .carrier) (shape G) g ∎

def bw_fold_loop2 (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W) (h : USym G)
  : Id (USym G)
      (loops_map (blind_wedge_pointed (BG G) (BG G) W) (BG G) (D .fst) (blind_wedge_i2g (BG G) (BG G) W h)) h
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let V ≔ wedge_pointed (BG G) (BG G) W' in
    let j ≔ wedge_incl2_pointed (BG G) (BG G) W' in
    calc
      loops_map V (BG G) (D .fst) (loops_map (BG G) V j h)
      = loops_map (BG G) (BG G) (book_pointed_compose (BG G) V (BG G) j (D .fst)) h
        by inverse (USym G) (loops_map (BG G) (BG G) (book_pointed_compose (BG G) V (BG G) j (D .fst)) h)
             (loops_map V (BG G) (D .fst) (loops_map (BG G) V j h))
             (loops_map_compose_pointwise (BG G) V (BG G) j (D .fst) h)
      = loops_map (BG G) (BG G) (blind_pointed_id (BG G)) h
        by refl ((k ↦ loops_map (BG G) (BG G) k h) : BookPointedMap (BG G) (BG G) → USym G) (D .snd .fst .snd)
      = h by loop_conjugate_at_refl (BG G .carrier) (shape G) h ∎

{` G is abelian. `}
def bw_aside_abelian (G : Group) (W : BlindWedge (BG G) (BG G)) (D : BlindFoldData G W)
  (r : BG (product_group G G) .carrier → BG G .carrier)
  (hr : Id (W .fst → BG G .carrier) (x ↦ r (D .snd .snd .fst .fst x)) (D .fst .fst))
  : IsAbelian G
  ≔ let W' ≔ bridge_wedge_signature (BG G) (BG G) W in
    let S ≔ BG (product_group G G) .carrier in
    let B ≔ BG G .carrier in
    let incl ≔ D .snd .snd .fst .fst in
    let ib ≔ wedge_incl_book G W' .fst in
    let fold ≔ D .fst .fst in
    let fb ≔ wedge_fold_book G W' .fst in
    let ie ≔ happly (W .fst) (_ ↦ S) incl ib (bw_incl_eq G W D .fst) in
    let fe ≔ happly (W .fst) (_ ↦ B) fold fb (bw_fold_eq G W D .fst) in
    let hh ≔ happly (W .fst) (_ ↦ B) (x ↦ r (incl x)) fold hr in
    unpointed_extension_abelian G W'
      (r, w ↦ concat B (r (ib w)) (r (incl w)) (fb w)
                (refl r (inverse S (incl w) (ib w) (ie w)))
                (concat B (r (incl w)) (fold w) (fb w) (hh w) (fe w)))

def bridge_xca_whatAREabeliangroups_aside : blind_xca_whatAREabeliangroups_aside
  ≔ G W D r hr g h ↦
    let V ≔ blind_wedge_pointed (BG G) (BG G) W in
    let X ≔ W .fst in let a12 ≔ W .snd .i1 (shape G) in
    let B ≔ BG G .carrier in let b ≔ shape G in
    let L ≔ Id X a12 a12 in
    let x ≔ blind_wedge_i1g (BG G) (BG G) W g in
    let y ≔ blind_wedge_i2g (BG G) (BG G) W h in
    let xi ≔ inverse X a12 a12 x in let yi ≔ inverse X a12 a12 y in
    let O ≔ loops_map V (BG G) (D .fst) in
    let cB : USym G → USym G → USym G ≔ concat B b b b in
    let cX : L → L → L ≔ concat X a12 a12 a12 in
    let ab ≔ bw_aside_abelian G W D r hr g h in
    let lx ≔ bw_fold_loop1 G W D g in
    let ly ≔ bw_fold_loop2 G W D h in
    calc
      O (cX (cX (cX yi xi) y) x)
      = cB (O (cX (cX yi xi) y)) (O x) by loops_map_concat V (BG G) (D .fst) (cX (cX yi xi) y) x
      = cB (cB (O (cX yi xi)) (O y)) (O x)
        by refl ((u ↦ cB u (O x)) : USym G → USym G) (loops_map_concat V (BG G) (D .fst) (cX yi xi) y)
      = cB (cB (cB (O yi) (O xi)) (O y)) (O x)
        by refl ((u ↦ cB (cB u (O y)) (O x)) : USym G → USym G) (loops_map_concat V (BG G) (D .fst) yi xi)
      = cB (cB (cB (inverse B b b h) (inverse B b b g)) h) g
        by refl ((p q s t ↦ cB (cB (cB p q) s) t) : USym G → USym G → USym G → USym G → USym G)
             (concat (USym G) (O yi) (inverse B b b (O y)) (inverse B b b h)
               (loops_map_inverse V (BG G) (D .fst) y) (refl (inverse B b b) ly))
             (concat (USym G) (O xi) (inverse B b b (O x)) (inverse B b b g)
               (loops_map_inverse V (BG G) (D .fst) x) (refl (inverse B b b) lx))
             ly lx
      = refl b by bw_commutator_trivial B b g h ab ∎
