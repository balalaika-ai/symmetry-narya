export "821-pullback-groups"
export "701-abstract-homomorphisms"
export "502-subgroups"

{` Chapter 8 (congp.tex), the exercise after the example (line 479), second
   and third parts: USym H ×_{USym G} USym H' ≃ USym(H ×_G H'), and its
   elevation to abstract groups; plus the intersection of two
   monomorphisms (def:intersectionofgroups, second paragraph). `}

def PullbackUSym (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : Type
  ≔ TypePullback (USym H) (USym H') (USym G) (usym_hom H G f) (usym_hom H' G f')

def pullback_usym_set (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : isSet (PullbackUSym G H H' f f')
  ≔ sigma_set (Product (USym H) (USym H'))
      (ab ↦ Id (USym G) (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd)))
      (product_set (USym H) (USym H') (usym_set H) (usym_set H'))
      (ab ↦ prop_is_set (Id (USym G) (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd)))
        (usym_set G (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd))))

{` Elements of the set pullback are equal when their first two components
   are. `}
def pullback_usym_path (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (t t' : PullbackUSym G H H' f f')
  (p : Id (USym H) (t .fst .fst) (t' .fst .fst)) (q : Id (USym H') (t .fst .snd) (t' .fst .snd))
  : Id (PullbackUSym G H H' f f') t t'
  ≔ subtype_equal (Product (USym H) (USym H'))
      (ab ↦ Id (USym G) (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd)))
      (ab ↦ usym_set G (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd))) t t'
      ((p, q) : Id (Product (USym H) (USym H')) (t .fst) (t' .fst))

{` The chain of equivalences USym(H ×_G H') ≃ (pt = pt in BH ×_{BG} BH')
   ≃ Σ_{(α,β)} (square over (α,β)) ≃ Σ_{(α,β)} (USym f α = USym f' β). `}
def pbg_loop_condition (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (ab : Id (Product (BG H .carrier) (BG H' .carrier)) (shape H, shape H') (shape H, shape H')) : Type
  ≔ PbgSquareCondition (BG G .carrier) (shape G) (hom_function H G f (shape H)) (hom_function H' G f' (shape H'))
      (hom_point H G f) (hom_point H' G f') (refl (hom_function H G f) (ab .fst)) (refl (hom_function H' G f') (ab .snd))

def pbg_loop_usym_condition (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (ab : Id (Product (BG H .carrier) (BG H' .carrier)) (shape H, shape H') (shape H, shape H')) : Type
  ≔ Id (USym G) (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd))

def pbg_loop_condition_equiv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (ab : Id (Product (BG H .carrier) (BG H' .carrier)) (shape H, shape H') (shape H, shape H'))
  : Equiv (pbg_loop_condition G H H' f f' ab) (pbg_loop_usym_condition G H H' f f' ab)
  ≔ let D ≔ BG G .carrier in
    let y ≔ hom_function H G f (shape H) in
    let y' ≔ hom_function H' G f' (shape H') in
    let u ≔ refl (hom_function H G f) (ab .fst) in
    let v ≔ refl (hom_function H' G f') (ab .snd) in
    let c ≔ pbg_conditions D (shape G) y (hom_point H G f) u y' (hom_point H' G f') v in
    iff_equiv (pbg_loop_condition G H H' f f' ab) (pbg_loop_usym_condition G H H' f f' ab)
      (bg_groupoid G y y' (concat D y y' y' (pbg_twist_point G H H' f f') v)
        (concat D y y y' u (pbg_twist_point G H H' f f')))
      (usym_set G (usym_hom H G f (ab .fst)) (usym_hom H' G f' (ab .snd)))
      (c .fst) (c .snd)

def pbg_loops_sigma_equiv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Equiv (Σ (Id (Product (BG H .carrier) (BG H' .carrier)) (shape H, shape H') (shape H, shape H'))
            (pbg_loop_usym_condition G H H' f f'))
      (PullbackUSym G H H' f f')
  ≔ let I ≔ Id (Product (BG H .carrier) (BG H' .carrier)) (shape H, shape H') (shape H, shape H') in
    quasi_inverse_equiv (Σ I (pbg_loop_usym_condition G H H' f f')) (PullbackUSym G H H' f f')
      (t ↦ ((t .fst .fst, t .fst .snd), t .snd))
      (t ↦ (((t .fst .fst, t .fst .snd) : I), t .snd))
      (t ↦ refl t) (t ↦ refl t)

def pullback_group_usym_chain (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Equiv (USym (pullback_group G H H' f f')) (PullbackUSym G H H' f f')
  ≔ let S ≔ pbg_space G H H' f f' in
    let pt ≔ pbg_point G H H' f f' in
    let BC ≔ Product (BG H .carrier) (BG H' .carrier) in
    let F ≔ pbg_fam (BG H .carrier) (BG H' .carrier) (BG G .carrier) (hom_function H G f) (hom_function H' G f') in
    let I ≔ Id BC (shape H, shape H') (shape H, shape H') in
    let d ≔ pbg_twist_point G H H' f f' in
    let y ≔ hom_function H G f (shape H) in
    let y' ≔ hom_function H' G f' (shape H') in
    compose_equiv (USym (pullback_group G H H' f f')) (Id S pt pt) (PullbackUSym G H H' f f')
      (automorphism_group_usym_equiv S (pbg_space_groupoid G H H' f f') pt)
      (compose_equiv (Id S pt pt) (SigmaPath BC F pt pt) (PullbackUSym G H H' f f')
        (canonical_inverse_equiv (SigmaPath BC F pt pt) (Id S pt pt) (sigma_path_equiv BC F pt pt))
        (compose_equiv (SigmaPath BC F pt pt) (Σ I (pbg_loop_condition G H H' f f')) (PullbackUSym G H H' f f')
          (family_equiv I (ab ↦ Id F ab d d) (pbg_loop_condition G H H' f f')
            (ab ↦ pbg_square_equiv (BG G .carrier) y y (refl (hom_function H G f) (ab .fst)) y' y'
              (refl (hom_function H' G f') (ab .snd)) d d))
          (compose_equiv (Σ I (pbg_loop_condition G H H' f f')) (Σ I (pbg_loop_usym_condition G H H' f f'))
            (PullbackUSym G H H' f f')
            (family_equiv I (pbg_loop_condition G H H' f f') (pbg_loop_usym_condition G H H' f f')
              (pbg_loop_condition_equiv G H H' f f'))
            (pbg_loops_sigma_equiv G H H' f f'))))

{` The canonical map ω ↦ (USym prj_H ω, USym prj_H' ω, !), where ! comes
   from the commuting square f ∘ prj_H = f' ∘ prj_H'. `}
def pullback_group_usym_square (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (w : USym (pullback_group G H H' f f'))
  : Id (USym G) (usym_hom H G f (usym_hom (pullback_group G H H' f f') H (pullback_group_proj_left G H H' f f') w))
      (usym_hom H' G f' (usym_hom (pullback_group G H H' f f') H' (pullback_group_proj_right G H H' f f') w))
  ≔ let P ≔ pullback_group G H H' f f' in
    let p1 ≔ pullback_group_proj_left G H H' f f' in
    let p2 ≔ pullback_group_proj_right G H H' f f' in
    calc
      usym_hom H G f (usym_hom P H p1 w) = usym_hom P G (group_hom_compose P H G p1 f) w
        by inverse (USym G) (usym_hom P G (group_hom_compose P H G p1 f) w) (usym_hom H G f (usym_hom P H p1 w))
          (usym_hom_compose P H G p1 f (refl w))
      = usym_hom P G (group_hom_compose P H' G p2 f') w
        by refl ((h ↦ usym_hom P G h w) : GroupHom P G → USym G) (pullback_group_square G H H' f f')
      = usym_hom H' G f' (usym_hom P H' p2 w) by usym_hom_compose P H' G p2 f' (refl w) ∎

def pullback_group_usym_map (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (w : USym (pullback_group G H H' f f')) : PullbackUSym G H H' f f'
  ≔ ((usym_hom (pullback_group G H H' f f') H (pullback_group_proj_left G H H' f f') w,
      usym_hom (pullback_group G H H' f f') H' (pullback_group_proj_right G H H' f f') w),
     pullback_group_usym_square G H H' f f' w)

def pullback_group_usym_chain_map (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (w : USym (pullback_group G H H' f f'))
  : Id (PullbackUSym G H H' f f') (pullback_group_usym_chain G H H' f f' .map w) (pullback_group_usym_map G H H' f f' w)
  ≔ pullback_usym_path G H H' f f' (pullback_group_usym_chain G H H' f f' .map w) (pullback_group_usym_map G H H' f f' w)
      (inverse (USym H) (pointed_loop_conjugate (BG H .carrier) (shape H) (shape H) (refl (shape H)) (w .fst .fst .fst))
        (w .fst .fst .fst) (loop_conjugate_at_refl (BG H .carrier) (shape H) (w .fst .fst .fst)))
      (inverse (USym H') (pointed_loop_conjugate (BG H' .carrier) (shape H') (shape H') (refl (shape H')) (w .fst .fst .snd))
        (w .fst .fst .snd) (loop_conjugate_at_refl (BG H' .carrier) (shape H') (w .fst .fst .snd)))

{` xca (line 479), USym part: USym(H ×_G H') ≃ USym H ×_{USym G} USym H',
   by the canonical map. The book states the equivalence in the other
   direction; its inverse is pullback_group_usym_equiv_book. `}
def pullback_group_usym_equiv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Equiv (USym (pullback_group G H H' f f')) (PullbackUSym G H H' f f')
  ≔ equiv_change_map (USym (pullback_group G H H' f f')) (PullbackUSym G H H' f f')
      (pullback_group_usym_chain G H H' f f') (pullback_group_usym_map G H H' f f')
      (pullback_group_usym_chain_map G H H' f f')

def pullback_group_usym_equiv_book (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : Equiv (PullbackUSym G H H' f f') (USym (pullback_group G H H' f f'))
  ≔ canonical_inverse_equiv (USym (pullback_group G H H' f f')) (PullbackUSym G H H' f f')
      (pullback_group_usym_equiv G H H' f f')

{` "Elevate the last equivalence to a statement about abstract groups":
   the set pullback carries the componentwise abstract group structure,
   and the canonical equivalence is an isomorphism of abstract groups
   abstr(H ×_G H') ≅ abstr H ×_{abstr G} abstr H'. `}
def pullback_usym_unit (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : PullbackUSym G H H' f f'
  ≔ ((usym_unit H, usym_unit H'),
     concat (USym G) (usym_hom H G f (usym_unit H)) (usym_unit G) (usym_hom H' G f' (usym_unit H'))
       (usym_hom_unit H G f) (inverse (USym G) (usym_hom H' G f' (usym_unit H')) (usym_unit G) (usym_hom_unit H' G f')))

def pullback_usym_mul (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (t t' : PullbackUSym G H H' f f')
  : PullbackUSym G H H' f f'
  ≔ ((usym_mul H (t .fst .fst) (t' .fst .fst), usym_mul H' (t .fst .snd) (t' .fst .snd)), calc
      usym_hom H G f (usym_mul H (t .fst .fst) (t' .fst .fst))
      = usym_mul G (usym_hom H G f (t .fst .fst)) (usym_hom H G f (t' .fst .fst))
        by usym_hom_mul H G f (t .fst .fst) (t' .fst .fst)
      = usym_mul G (usym_hom H' G f' (t .fst .snd)) (usym_hom H' G f' (t' .fst .snd))
        by refl (usym_mul G) (t .snd) (t' .snd)
      = usym_hom H' G f' (usym_mul H' (t .fst .snd) (t' .fst .snd))
        by inverse (USym G) (usym_hom H' G f' (usym_mul H' (t .fst .snd) (t' .fst .snd)))
          (usym_mul G (usym_hom H' G f' (t .fst .snd)) (usym_hom H' G f' (t' .fst .snd)))
          (usym_hom_mul H' G f' (t .fst .snd) (t' .fst .snd)) ∎)

def pullback_usym_inv (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (t : PullbackUSym G H H' f f')
  : PullbackUSym G H H' f f'
  ≔ ((usym_inv H (t .fst .fst), usym_inv H' (t .fst .snd)), calc
      usym_hom H G f (usym_inv H (t .fst .fst)) = usym_inv G (usym_hom H G f (t .fst .fst))
        by usym_hom_inv H G f (t .fst .fst)
      = usym_inv G (usym_hom H' G f' (t .fst .snd)) by refl (usym_inv G) (t .snd)
      = usym_hom H' G f' (usym_inv H' (t .fst .snd))
        by inverse (USym G) (usym_hom H' G f' (usym_inv H' (t .fst .snd))) (usym_inv G (usym_hom H' G f' (t .fst .snd)))
          (usym_hom_inv H' G f' (t .fst .snd)) ∎)

def pullback_usym_laws (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : AbstractGroupLaws (PullbackUSym G H H' f f') (pullback_usym_unit G H H' f f') (pullback_usym_mul G H H' f f')
      (pullback_usym_inv G H H' f f')
  ≔ let T ≔ PullbackUSym G H H' f f' in
    let e ≔ pullback_usym_unit G H H' f f' in
    let m ≔ pullback_usym_mul G H H' f f' in
    let LH ≔ usym_abstract_laws H in
    let LH' ≔ usym_abstract_laws H' in
    (pullback_usym_set G H H' f f',
     t ↦ pullback_usym_path G H H' f f' (m t e) t (LH .unit_right (t .fst .fst)) (LH' .unit_right (t .fst .snd)),
     t ↦ pullback_usym_path G H H' f f' (m e t) t (LH .unit_left (t .fst .fst)) (LH' .unit_left (t .fst .snd)),
     t1 t2 t3 ↦ pullback_usym_path G H H' f f' (m t1 (m t2 t3)) (m (m t1 t2) t3)
       (LH .assoc (t1 .fst .fst) (t2 .fst .fst) (t3 .fst .fst)) (LH' .assoc (t1 .fst .snd) (t2 .fst .snd) (t3 .fst .snd)),
     t ↦ pullback_usym_path G H H' f f' (m t (pullback_usym_inv G H H' f f' t)) e
       (LH .inv_right (t .fst .fst)) (LH' .inv_right (t .fst .snd)))

def pullback_abstract_group (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) : AbstractGroup
  ≔ (PullbackUSym G H H' f f', pullback_usym_unit G H H' f f', pullback_usym_mul G H H' f f',
     pullback_usym_inv G H H' f f', pullback_usym_laws G H H' f f')

def pullback_group_usym_map_hom (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : IsAbstractHom (abstr (pullback_group G H H' f f')) (pullback_abstract_group G H H' f f')
      (pullback_group_usym_map G H H' f f')
  ≔ let P ≔ pullback_group G H H' f f' in
    s s' ↦ pullback_usym_path G H H' f f'
      (pullback_group_usym_map G H H' f f' (usym_mul P s s'))
      (pullback_usym_mul G H H' f f' (pullback_group_usym_map G H H' f f' s) (pullback_group_usym_map G H H' f f' s'))
      (usym_hom_mul P H (pullback_group_proj_left G H H' f f') s s')
      (usym_hom_mul P H' (pullback_group_proj_right G H H' f f') s s')

def pullback_group_abstract_iso (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  : AbstractIso (abstr (pullback_group G H H' f f')) (pullback_abstract_group G H H' f f')
  ≔ (pullback_group_usym_equiv G H H' f f', pullback_group_usym_map_hom G H H' f f')

{` Intersection (def:intersectionofgroups, second paragraph). If f' is a
   monomorphism then so is prj_H, and symmetrically. `}
def pbg_usym_reflects (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  : PathReflecting (USym H) (USym G) (usym_hom H G i)
  ≔ embedding_reflects_paths (USym H) (USym G) (usym_hom H G i) m

def pullback_group_proj_left_reflects (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (m' : IsGroupMono H' G f')
  : PathReflecting (USym (pullback_group G H H' f f')) (USym H) (usym_hom (pullback_group G H H' f f') H
      (pullback_group_proj_left G H H' f f'))
  ≔ let P ≔ pullback_group G H H' f f' in
    let p1 ≔ pullback_group_proj_left G H H' f f' in
    let p2 ≔ pullback_group_proj_right G H H' f f' in
    let sq ≔ pullback_group_usym_square G H H' f f' in
    w w' h ↦ equivalence_injective (USym P) (PullbackUSym G H H' f f') (pullback_group_usym_equiv G H H' f f') w w'
      (pullback_usym_path G H H' f f' (pullback_group_usym_map G H H' f f' w) (pullback_group_usym_map G H H' f f' w') h
        (pbg_usym_reflects H' G f' m' (usym_hom P H' p2 w) (usym_hom P H' p2 w') (calc
          usym_hom H' G f' (usym_hom P H' p2 w) = usym_hom H G f (usym_hom P H p1 w)
            by inverse (USym G) (usym_hom H G f (usym_hom P H p1 w)) (usym_hom H' G f' (usym_hom P H' p2 w)) (sq w)
          = usym_hom H G f (usym_hom P H p1 w') by refl (usym_hom H G f) h
          = usym_hom H' G f' (usym_hom P H' p2 w') by sq w' ∎)))

def pullback_group_proj_right_reflects (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G)
  (m : IsGroupMono H G f)
  : PathReflecting (USym (pullback_group G H H' f f')) (USym H') (usym_hom (pullback_group G H H' f f') H'
      (pullback_group_proj_right G H H' f f'))
  ≔ let P ≔ pullback_group G H H' f f' in
    let p1 ≔ pullback_group_proj_left G H H' f f' in
    let p2 ≔ pullback_group_proj_right G H H' f f' in
    let sq ≔ pullback_group_usym_square G H H' f f' in
    w w' h ↦ equivalence_injective (USym P) (PullbackUSym G H H' f f') (pullback_group_usym_equiv G H H' f f') w w'
      (pullback_usym_path G H H' f f' (pullback_group_usym_map G H H' f f' w) (pullback_group_usym_map G H H' f f' w')
        (pbg_usym_reflects H G f m (usym_hom P H p1 w) (usym_hom P H p1 w') (calc
          usym_hom H G f (usym_hom P H p1 w) = usym_hom H' G f' (usym_hom P H' p2 w) by sq w
          = usym_hom H' G f' (usym_hom P H' p2 w') by refl (usym_hom H' G f') h
          = usym_hom H G f (usym_hom P H p1 w')
            by inverse (USym G) (usym_hom H G f (usym_hom P H p1 w')) (usym_hom H' G f' (usym_hom P H' p2 w')) (sq w') ∎))
        h)

def pullback_group_proj_left_mono (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (m' : IsGroupMono H' G f')
  : IsGroupMono (pullback_group G H H' f f') H (pullback_group_proj_left G H H' f f')
  ≔ path_reflecting_set_embedding (USym (pullback_group G H H' f f')) (USym H) (usym_set H)
      (usym_hom (pullback_group G H H' f f') H (pullback_group_proj_left G H H' f f'))
      (pullback_group_proj_left_reflects G H H' f f' m')

def pullback_group_proj_right_mono (G H H' : Group) (f : GroupHom H G) (f' : GroupHom H' G) (m : IsGroupMono H G f)
  : IsGroupMono (pullback_group G H H' f f') H' (pullback_group_proj_right G H H' f f')
  ≔ path_reflecting_set_embedding (USym (pullback_group G H H' f f')) (USym H') (usym_set H')
      (usym_hom (pullback_group G H H' f f') H' (pullback_group_proj_right G H H' f f'))
      (pullback_group_proj_right_reflects G H H' f f' m)

{` The composite of two monomorphisms is a monomorphism. `}
def pbg_compose_mono (K H G : Group) (i : GroupHom K H) (j : GroupHom H G) (mi : IsGroupMono K H i) (mj : IsGroupMono H G j)
  : IsGroupMono K G (group_hom_compose K H G i j)
  ≔ path_reflecting_set_embedding (USym K) (USym G) (usym_set G) (usym_hom K G (group_hom_compose K H G i j))
      (w w' h ↦ pbg_usym_reflects K H i mi w w'
        (pbg_usym_reflects H G j mj (usym_hom K H i w) (usym_hom K H i w') (calc
          usym_hom H G j (usym_hom K H i w) = usym_hom K G (group_hom_compose K H G i j) w
            by inverse (USym G) (usym_hom K G (group_hom_compose K H G i j) w) (usym_hom H G j (usym_hom K H i w))
              (usym_hom_compose K H G i j (refl w))
          = usym_hom K G (group_hom_compose K H G i j) w' by h
          = usym_hom H G j (usym_hom K H i w') by usym_hom_compose K H G i j (refl w') ∎)))

{` def:intersectionofgroups for monomorphisms (H, f, !), (H', f', !): the
   intersection H ∩ H' is the pullback group with the monomorphism
   f ∘ prj_H into G. `}
def group_mono_intersection (G : Group) (m m' : GroupMonos G) : GroupMonos G
  ≔ (pullback_group G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst),
     (group_hom_compose (pullback_group G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst)) (m .fst) G
       (pullback_group_proj_left G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst)) (m .snd .fst),
     pbg_compose_mono (pullback_group G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst)) (m .fst) G
       (pullback_group_proj_left G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst)) (m .snd .fst)
       (pullback_group_proj_left_mono G (m .fst) (m' .fst) (m .snd .fst) (m' .snd .fst) (m' .snd .snd))
       (m .snd .snd)))
