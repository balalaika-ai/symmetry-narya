export "824-integer-intersection"
export "973-abstract-subgroup-intersections"
export "594-circle-power-subgroups"

{` Chapter 8 (congp.tex:471), the example aℤ ∩ bℤ = lcm(a,b)ℤ for ALL
   natural numbers a, b, in the subgroup formulation of ex:Rm0-subgroup:
   aℤ ⊂ ℤ is the subgroup (R_a, 0) for a > 0 and (R, 0) (the trivial
   subgroup) for a = 0, as monomorphisms into ℤ = circle_group C via
   subgroup_to_mono. Module 824 covers a, b > 0 with the multiplication
   homomorphisms; here 0ℤ is included.

   Route: a monomorphism (H, i) picks out g : USym ℤ iff a divides the
   winding number of g (rmsub_picks_out, rsub_picks_out with lem:E-preserves-symms);
   the intersection picks out g iff both do (intersection_picked_out_iff,
   module 973); Multiples a ∩ Multiples b = Multiples (lcm a b)
   (nat_lcm_intersection, module 148, including the cases a = 0, b = 0).
   Two monomorphisms into G picking out the same symmetries are isomorphic
   over G (mono_iso_of_same_symmetries: USym of the comparison map is the
   lift through the second embedding, an abstract homomorphism, delooped by
   lem:homomabstrconcr). `}

{` The lift of a symmetry picked out by a monomorphism (fibres are propositions). `}
def isub_lift (G : Group) (n : GroupMonos G) (g : USym G) (t : SymmetryPickedOut G n g)
  : BookFiber (USym (n .fst)) (USym G) (usym_hom (n .fst) G (n .snd .fst)) g
  ≔ mere_rec (BookFiber (USym (n .fst)) (USym G) (usym_hom (n .fst) G (n .snd .fst)) g)
      (BookFiber (USym (n .fst)) (USym G) (usym_hom (n .fst) G (n .snd .fst)) g)
      (n .snd .snd g) (x ↦ x) t

def isub_map (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g) (h : USym (m .fst)) : USym (n .fst)
  ≔ let i ≔ usym_hom (m .fst) G (m .snd .fst) in
    isub_lift G n (i h) (hyp (i h) (mere (BookFiber (USym (m .fst)) (USym G) i (i h)) (h, refl (i h)))) .fst

def isub_map_spec (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g) (h : USym (m .fst))
  : Id (USym G) (usym_hom (m .fst) G (m .snd .fst) h) (usym_hom (n .fst) G (n .snd .fst) (isub_map G m n hyp h))
  ≔ let i ≔ usym_hom (m .fst) G (m .snd .fst) in
    isub_lift G n (i h) (hyp (i h) (mere (BookFiber (USym (m .fst)) (USym G) i (i h)) (h, refl (i h)))) .snd

def isub_map_mul (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g) (s s' : USym (m .fst))
  : Id (USym (n .fst)) (isub_map G m n hyp (usym_mul (m .fst) s s'))
      (usym_mul (n .fst) (isub_map G m n hyp s) (isub_map G m n hyp s'))
  ≔ let H ≔ m .fst in let K ≔ n .fst in
    let i ≔ usym_hom H G (m .snd .fst) in let j ≔ usym_hom K G (n .snd .fst) in
    let u ≔ isub_map G m n hyp in let us ≔ isub_map_spec G m n hyp in
    embedding_reflects_paths (USym K) (USym G) j (n .snd .snd) (u (usym_mul H s s')) (usym_mul K (u s) (u s'))
      (calc
        j (u (usym_mul H s s')) = i (usym_mul H s s')
          by inverse (USym G) (i (usym_mul H s s')) (j (u (usym_mul H s s'))) (us (usym_mul H s s'))
        = usym_mul G (i s) (i s') by usym_hom_mul H G (m .snd .fst) s s'
        = usym_mul G (j (u s)) (j (u s')) by refl (usym_mul G) (us s) (us s')
        = j (usym_mul K (u s) (u s'))
          by inverse (USym G) (j (usym_mul K (u s) (u s'))) (usym_mul G (j (u s)) (j (u s')))
            (usym_hom_mul K G (n .snd .fst) (u s) (u s')) ∎)

def isub_abstract_hom (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g)
  : AbstractHom (abstr (m .fst)) (abstr (n .fst))
  ≔ (isub_map G m n hyp, s s' ↦ isub_map_mul G m n hyp s s')

def isub_hom (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g) : GroupHom (m .fst) (n .fst)
  ≔ deloop_hom (m .fst) (n .fst) (isub_abstract_hom G m n hyp)

def isub_hom_usym (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g) (h : USym (m .fst))
  : Id (USym (n .fst)) (usym_hom (m .fst) (n .fst) (isub_hom G m n hyp) h) (isub_map G m n hyp h)
  ≔ refl ((t ↦ t .fst h) : AbstractHom (abstr (m .fst)) (abstr (n .fst)) → USym (n .fst))
      (deloop_hom_section (m .fst) (n .fst) (isub_abstract_hom G m n hyp))

{` The lift back and forth are inverse (both embeddings reflect paths). `}
def isub_roundtrip (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g)
  (hyp' : (g : USym G) → SymmetryPickedOut G n g → SymmetryPickedOut G m g) (h : USym (m .fst))
  : Id (USym (m .fst)) (isub_map G n m hyp' (isub_map G m n hyp h)) h
  ≔ let i ≔ usym_hom (m .fst) G (m .snd .fst) in let j ≔ usym_hom (n .fst) G (n .snd .fst) in
    let k ≔ isub_map G m n hyp h in
    embedding_reflects_paths (USym (m .fst)) (USym G) i (m .snd .snd) (isub_map G n m hyp' k) h
      (concat (USym G) (i (isub_map G n m hyp' k)) (j k) (i h)
        (inverse (USym G) (j k) (i (isub_map G n m hyp' k)) (isub_map_spec G n m hyp' k))
        (inverse (USym G) (i h) (j k) (isub_map_spec G m n hyp h)))

{` Two monomorphisms into G picking out the same symmetries are isomorphic
   over G. `}
def mono_iso_of_same_symmetries (G : Group) (m n : GroupMonos G)
  (hyp : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G n g)
  (hyp' : (g : USym G) → SymmetryPickedOut G n g → SymmetryPickedOut G m g)
  : Σ (GroupIso (m .fst) (n .fst)) (phi ↦
      Id (GroupHom (m .fst) G) (m .snd .fst) (group_hom_compose (m .fst) (n .fst) G (phi .fst) (n .snd .fst)))
  ≔ let H ≔ m .fst in let K ≔ n .fst in
    let phi ≔ isub_hom G m n hyp in
    let j ≔ usym_hom K G (n .snd .fst) in
    let E : Equiv (USym H) (USym K)
      ≔ quasi_inverse_equiv (USym H) (USym K) (isub_map G m n hyp) (isub_map G n m hyp')
          (isub_roundtrip G m n hyp hyp') (isub_roundtrip G n m hyp' hyp) in
    ((phi, pbg_group_iso_from_usym_equiv H K phi E
        (h ↦ inverse (USym K) (usym_hom H K phi h) (isub_map G m n hyp h) (isub_hom_usym G m n hyp h))),
     pbg_hom_ext_usym H G (m .snd .fst) (group_hom_compose H K G phi (n .snd .fst)) (h ↦ calc
       usym_hom H G (m .snd .fst) h = j (isub_map G m n hyp h) by isub_map_spec G m n hyp h
       = j (usym_hom H K phi h)
         by refl j (inverse (USym K) (usym_hom H K phi h) (isub_map G m n hyp h) (isub_hom_usym G m n hyp h))
       = usym_hom H G (group_hom_compose H K G phi (n .snd .fst)) h
         by inverse (USym G) (usym_hom H G (group_hom_compose H K G phi (n .snd .fst)) h) (j (usym_hom H K phi h))
           (usym_hom_compose H K G phi (n .snd .fst) (refl h)) ∎))

{` aℤ ⊂ ℤ: (R_a, 0) for a > 0, (R, 0) for a = 0 (ex:Rm0-subgroup). `}
def multiples_subgroup (C : CircleSignature) (a : Nat) : Subgroups (circle_group C)
  ≔ match a [ zero. ↦ rsub_subgroup C | suc. k ↦ rmsub_subgroup C k ]

def multiples_subgroup_mono (C : CircleSignature) (a : Nat) : GroupMonos (circle_group C)
  ≔ subgroup_to_mono (circle_group C) (multiples_subgroup C a)

{` g is picked out by aℤ iff a divides the winding number of g. `}
def isub_picked_multiple (C : CircleSignature) (a : Nat) (g : USym (circle_group C))
  (t : SymmetryPickedOut (circle_group C) (multiples_subgroup_mono C a) g) : Multiples a (circle_winding C g) .fst
  ≔ let Z ≔ circle_group C in
    let lp ≔ loop_power (C .carrier) (C .base) (C .loop) in
    let w ≔ circle_winding C g in
    match a [
    | zero. ↦
      let e : Id (USym Z) g (refl (C .base))
        ≔ rsub_picks_out C g .map (subgroup_picked_out_fixes Z (rsub_subgroup C) g t) in
      mere (MultipleWitness zero. w)
        (int_zero, concat Int w (circle_winding C (lp int_zero)) int_zero (refl (circle_winding C) e)
           (circle_winding_power C int_zero))
    | suc. k ↦
      mere_rec (Σ Int (q ↦ Id (USym Z) g (lp (int_mul q (pos. (suc. k)))))) (Multiples (suc. k) w .fst)
        (Multiples (suc. k) w .snd)
        (v ↦ mere (MultipleWitness (suc. k) w)
          (v .fst, concat Int w (circle_winding C (lp (int_mul (v .fst) (pos. (suc. k))))) (int_mul (v .fst) (pos. (suc. k)))
             (refl (circle_winding C) (v .snd)) (circle_winding_power C (int_mul (v .fst) (pos. (suc. k))))))
        (rmsub_picks_out C k g .map (subgroup_picked_out_fixes Z (rmsub_subgroup C k) g t)) ]

def isub_multiple_picked (C : CircleSignature) (a : Nat) (g : USym (circle_group C))
  (t : Multiples a (circle_winding C g) .fst) : SymmetryPickedOut (circle_group C) (multiples_subgroup_mono C a) g
  ≔ let Z ≔ circle_group C in
    let lp ≔ loop_power (C .carrier) (C .base) (C .loop) in
    let w ≔ circle_winding C g in
    let back : (z : Int) → Id Int w z → Id (USym Z) g (lp z)
      ≔ z e ↦ concat (USym Z) g (lp w) (lp z) (inverse (USym Z) (lp w) g (circle_power_winding C g)) (refl lp e) in
    match a [
    | zero. ↦
      subgroup_fixes_picked_out Z (rsub_subgroup C) g
        (mere_rec (MultipleWitness zero. w)
          (Id (gset_underlying Z (rsub_gset C)) (gset_usym_act Z (rsub_gset C) g (rsub_point C)) (rsub_point C))
          (gset_underlying_set Z (rsub_gset C) (gset_usym_act Z (rsub_gset C) g (rsub_point C)) (rsub_point C))
          (v ↦ equiv_inverse_map
             (Id (gset_underlying Z (rsub_gset C)) (gset_usym_act Z (rsub_gset C) g (rsub_point C)) (rsub_point C))
             (Id (USym Z) g (refl (C .base))) (rsub_picks_out C g) (back (int_mul (v .fst) (pos. zero.)) (v .snd)))
          t)
    | suc. k ↦
      subgroup_fixes_picked_out Z (rmsub_subgroup C k) g
        (equiv_inverse_map
           (Id (RmBase C k) (gset_usym_act Z (rmsub_gset C k) g (rmsub_point C k)) (rmsub_point C k))
           (Mere (Σ Int (q ↦ Id (USym Z) g (lp (int_mul q (pos. (suc. k)))))))
           (rmsub_picks_out C k g)
           (mere_rec (MultipleWitness (suc. k) w) (Mere (Σ Int (q ↦ Id (USym Z) g (lp (int_mul q (pos. (suc. k)))))))
             (mere_isprop (Σ Int (q ↦ Id (USym Z) g (lp (int_mul q (pos. (suc. k)))))))
             (v ↦ mere (Σ Int (q ↦ Id (USym Z) g (lp (int_mul q (pos. (suc. k))))))
               (v .fst, back (int_mul (v .fst) (pos. (suc. k))) (v .snd)))
             t)) ]

{` aℤ ∩ bℤ and lcm(a,b)ℤ pick out the same symmetries. `}
def isub_intersection_to_lcm (C : CircleSignature) (a b : Nat) (g : USym (circle_group C))
  (t : SymmetryPickedOut (circle_group C)
         (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b)) g)
  : SymmetryPickedOut (circle_group C) (multiples_subgroup_mono C (nat_lcm a b)) g
  ≔ let Z ≔ circle_group C in
    let w ≔ circle_winding C g in
    let both ≔ intersection_picked_out_iff Z (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) g .fst t in
    isub_multiple_picked C (nat_lcm a b) g
      (transport (Subtypes Int) (K ↦ K w .fst) (SubgroupIntersection (Multiples a) (Multiples b))
         (Multiples (nat_lcm a b)) (nat_lcm_intersection a b)
         (isub_picked_multiple C a g (both .fst), isub_picked_multiple C b g (both .snd)))

def isub_lcm_to_intersection (C : CircleSignature) (a b : Nat) (g : USym (circle_group C))
  (t : SymmetryPickedOut (circle_group C) (multiples_subgroup_mono C (nat_lcm a b)) g)
  : SymmetryPickedOut (circle_group C)
      (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b)) g
  ≔ let Z ≔ circle_group C in
    let w ≔ circle_winding C g in
    let both : Product (Multiples a w .fst) (Multiples b w .fst)
      ≔ transport (Subtypes Int) (K ↦ K w .fst) (Multiples (nat_lcm a b))
          (SubgroupIntersection (Multiples a) (Multiples b))
          (inverse (Subtypes Int) (SubgroupIntersection (Multiples a) (Multiples b)) (Multiples (nat_lcm a b))
            (nat_lcm_intersection a b))
          (isub_picked_multiple C (nat_lcm a b) g t) in
    intersection_picked_out_iff Z (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) g .snd
      (isub_multiple_picked C a g (both .fst), isub_multiple_picked C b g (both .snd))

{` congp.tex:471 for all a, b : ℕ (L = lcm(a,b)): an isomorphism
   φ : aℤ ∩ bℤ ≅ Lℤ with incl_{aℤ ∩ bℤ} = incl_{Lℤ} ∘ φ, the intersection
   being the pullback group with the inclusion through aℤ. `}
def integer_intersection_subgroups (C : CircleSignature) (a b : Nat)
  : Σ (GroupIso (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) .fst)
                (multiples_subgroup_mono C (nat_lcm a b) .fst)) (phi ↦
      Id (GroupHom (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) .fst)
           (circle_group C))
        (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) .snd .fst)
        (group_hom_compose
           (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b) .fst)
           (multiples_subgroup_mono C (nat_lcm a b) .fst) (circle_group C) (phi .fst)
           (multiples_subgroup_mono C (nat_lcm a b) .snd .fst)))
  ≔ mono_iso_of_same_symmetries (circle_group C)
      (group_mono_intersection (circle_group C) (multiples_subgroup_mono C a) (multiples_subgroup_mono C b))
      (multiples_subgroup_mono C (nat_lcm a b))
      (isub_intersection_to_lcm C a b) (isub_lcm_to_intersection C a b)
