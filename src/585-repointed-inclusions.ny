export "584-subgroup-e-for-sigma3"

{` Chapter 5, xca:SG2subSG3 (the book writes i_3 for i_2): varying the pointing
   path of i_m : Σ_m → Σ_{m+1} by a symmetry p of Fin (m+1). USym i^p(s) is the
   conjugate p⁻¹ · USym i_m(s) · p, and im(USym i^p) is the stabilizer of the
   point p⁻¹ · ★ (★ = inr ★ the added point): for m = 2 the six pointing
   paths give the three subgroups {e, (a b)}, each twice. `}

def repointed_inclusion (m : Nat) (p : USym (symmetric_group (suc. m)))
  : GroupHom (symmetric_group m) (symmetric_group (suc. m))
  ≔ mkhom (symmetric_group m) (symmetric_group (suc. m))
      (hom_function (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m), p)

def repointed_inclusion_usym (m : Nat) (p : USym (symmetric_group (suc. m))) (s : USym (symmetric_group m))
  : Id (USym (symmetric_group (suc. m)))
      (usym_hom (symmetric_group m) (symmetric_group (suc. m)) (repointed_inclusion m p) s)
      (usym_mul (symmetric_group (suc. m))
        (usym_mul (symmetric_group (suc. m)) (usym_inv (symmetric_group (suc. m)) p)
          (usym_hom (symmetric_group m) (symmetric_group (suc. m)) (symmetric_group_inclusion m) s)) p)
  ≔ let K ≔ symmetric_group (suc. m) in
    let C ≔ BG K .carrier in
    let c0 ≔ shape K in
    let Bi ≔ hom_function (symmetric_group m) K (symmetric_group_inclusion m) in
    let l ≔ map_path (BG (symmetric_group m) .carrier) C Bi (shape (symmetric_group m)) (shape (symmetric_group m)) s in
    map_path (USym K) (USym K) (k ↦ concat C c0 c0 c0 p (concat C c0 c0 c0 k (inverse C c0 c0 p))) l
      (usym_hom (symmetric_group m) K (symmetric_group_inclusion m) s)
      (inverse (USym K) (usym_hom (symmetric_group m) K (symmetric_group_inclusion m) s) l (loop_conjugate_at_refl C c0 l))

def repointed_inclusion_mono (m : Nat) (p : USym (symmetric_group (suc. m)))
  : IsGroupMono (symmetric_group m) (symmetric_group (suc. m)) (repointed_inclusion m p)
  ≔ let K ≔ symmetric_group (suc. m) in
    let C ≔ BG K .carrier in
    let c0 ≔ shape K in
    let Bi ≔ hom_function (symmetric_group m) K (symmetric_group_inclusion m) in
    let apb ≔ map_path (BG (symmetric_group m) .carrier) C Bi (shape (symmetric_group m)) (shape (symmetric_group m)) in
    path_reflecting_set_embedding (USym (symmetric_group m)) (USym K) (usym_set K)
      (usym_hom (symmetric_group m) K (repointed_inclusion m p))
      (s s' e ↦ symmetric_group_inclusion_reflects m s s'
        (map_path (USym K) (USym K) (k ↦ concat C c0 c0 c0 (refl c0) (concat C c0 c0 c0 k (inverse C c0 c0 (refl c0))))
          (apb s) (apb s') (mono_loop_conjugate_injective C c0 c0 p (apb s) (apb s') e)))

def repointed_monomorphism (m : Nat) (p : USym (symmetric_group (suc. m))) : GroupMonos (symmetric_group (suc. m))
  ≔ (symmetric_group m, (repointed_inclusion m p, repointed_inclusion_mono m p))

{` Path algebra for conjugation by a path p : a = b. `}
def conj_out (A : Type) (a b : A) (p : Id A a b) (y : Id A b b) : Id A a a
  ≔ concat A a b a p (concat A b b a y (inverse A a b p))

def conj_in (A : Type) (a b : A) (p : Id A a b) (h : Id A a a) : Id A b b
  ≔ concat A b a b (inverse A a b p) (concat A a a b h p)

def conj_in_out (A : Type) (a b : A) (p : Id A a b) (y : Id A b b)
  : Id (Id A b b) (conj_in A a b p (conj_out A a b p y)) y
  ≔ J A a (b p ↦ (y : Id A b b) → Id (Id A b b) (conj_in A a b p (conj_out A a b p y)) y)
      (y ↦ calc
        conj_in A a a (refl a) (conj_out A a a (refl a) y)
        = concat A a a a (refl a) (concat A a a a (conj_out A a a (refl a) y) (refl a))
          by map_path (Id A a a) (Id A a a) (r ↦ concat A a a a r (concat A a a a (conj_out A a a (refl a) y) (refl a)))
               (inverse A a a (refl a)) (refl a) (inverse_refl A a)
        = concat A a a a (conj_out A a a (refl a) y) (refl a)
          by concat_1p A a a (concat A a a a (conj_out A a a (refl a) y) (refl a))
        = conj_out A a a (refl a) y by concat_p1 A a a (conj_out A a a (refl a) y)
        = y by loop_conjugate_at_refl A a y ∎)
      b p y

def conj_out_in (A : Type) (a b : A) (p : Id A a b) (h : Id A a a)
  : Id (Id A a a) (conj_out A a b p (conj_in A a b p h)) h
  ≔ J A a (b p ↦ (h : Id A a a) → Id (Id A a a) (conj_out A a b p (conj_in A a b p h)) h)
      (h ↦ calc
        conj_out A a a (refl a) (conj_in A a a (refl a) h)
        = conj_in A a a (refl a) h by loop_conjugate_at_refl A a (conj_in A a a (refl a) h)
        = concat A a a a (refl a) (concat A a a a h (refl a))
          by map_path (Id A a a) (Id A a a) (r ↦ concat A a a a r (concat A a a a h (refl a)))
               (inverse A a a (refl a)) (refl a) (inverse_refl A a)
        = concat A a a a h (refl a) by concat_1p A a a (concat A a a a h (refl a))
        = h by concat_p1 A a a h ∎)
      b p h

{` im(USym i^p): h is picked out iff h fixes p⁻¹ · ★. `}
def repointed_point (m : Nat) (p : USym (symmetric_group (suc. m))) : Fin (suc. m)
  ≔ gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) (usym_inv (symmetric_group (suc. m)) p) (inr. star.)

def inclusion_picked_out_iff (m : Nat) (h : USym (symmetric_group (suc. m)))
  : Product
      (SymmetryPickedOut (symmetric_group (suc. m)) (symmetric_group_inclusion_monomorphism m) h
        → Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (inr. star.)) (inr. star.))
      (Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (inr. star.)) (inr. star.)
        → SymmetryPickedOut (symmetric_group (suc. m)) (symmetric_group_inclusion_monomorphism m) h)
  ≔ let K ≔ symmetric_group (suc. m) in
    let P ≔ Id (Fin (suc. m)) (gset_usym_act K (standard_symmetric_gset (suc. m)) h (inr. star.)) (inr. star.) in
    transport (GroupMonos K) (n ↦ Product (SymmetryPickedOut K n h → P) (P → SymmetryPickedOut K n h))
      (subgroup_to_mono K (fixed_point_subgroup m (inr. star.))) (symmetric_group_inclusion_monomorphism m)
      (fix_point_mono_path m)
      ((fixed_point_subgroup_symmetries m (inr. star.) h .snd), (fixed_point_subgroup_symmetries m (inr. star.) h .fst))

def repointed_image_iff (m : Nat) (p h : USym (symmetric_group (suc. m)))
  : Product
      (SymmetryPickedOut (symmetric_group (suc. m)) (repointed_monomorphism m p) h
        → SymmetryPickedOut (symmetric_group (suc. m)) (symmetric_group_inclusion_monomorphism m)
            (conj_in (BG (symmetric_group (suc. m)) .carrier) (shape (symmetric_group (suc. m))) (shape (symmetric_group (suc. m))) p h))
      (SymmetryPickedOut (symmetric_group (suc. m)) (symmetric_group_inclusion_monomorphism m)
            (conj_in (BG (symmetric_group (suc. m)) .carrier) (shape (symmetric_group (suc. m))) (shape (symmetric_group (suc. m))) p h)
        → SymmetryPickedOut (symmetric_group (suc. m)) (repointed_monomorphism m p) h)
  ≔ let K ≔ symmetric_group (suc. m) in
    let C ≔ BG K .carrier in
    let c0 ≔ shape K in
    let S2 ≔ USym (symmetric_group m) in
    let ii ≔ usym_hom (symmetric_group m) K (symmetric_group_inclusion m) in
    let ip ≔ usym_hom (symmetric_group m) K (repointed_inclusion m p) in
    let hin ≔ conj_in C c0 c0 p h in
    (t ↦ mere_rec (Σ S2 (s ↦ Id (USym K) h (ip s))) (Mere (Σ S2 (s ↦ Id (USym K) hin (ii s))))
          (mere_isprop (Σ S2 (s ↦ Id (USym K) hin (ii s))))
          (u ↦ mere (Σ S2 (s ↦ Id (USym K) hin (ii s)))
            (u .fst, concat (USym K) hin (conj_in C c0 c0 p (conj_out C c0 c0 p (ii (u .fst)))) (ii (u .fst))
              (map_path (USym K) (USym K) (conj_in C c0 c0 p) h (conj_out C c0 c0 p (ii (u .fst)))
                (concat (USym K) h (ip (u .fst)) (conj_out C c0 c0 p (ii (u .fst))) (u .snd)
                  (repointed_inclusion_usym m p (u .fst))))
              (conj_in_out C c0 c0 p (ii (u .fst)))))
          t,
     t ↦ mere_rec (Σ S2 (s ↦ Id (USym K) hin (ii s))) (Mere (Σ S2 (s ↦ Id (USym K) h (ip s))))
          (mere_isprop (Σ S2 (s ↦ Id (USym K) h (ip s))))
          (u ↦ mere (Σ S2 (s ↦ Id (USym K) h (ip s)))
            (u .fst, calc
              h = conj_out C c0 c0 p hin by inverse (USym K) (conj_out C c0 c0 p hin) h (conj_out_in C c0 c0 p h)
              = conj_out C c0 c0 p (ii (u .fst)) by map_path (USym K) (USym K) (conj_out C c0 c0 p) hin (ii (u .fst)) (u .snd)
              = ip (u .fst) by inverse (USym K) (ip (u .fst)) (conj_out C c0 c0 p (ii (u .fst))) (repointed_inclusion_usym m p (u .fst)) ∎))
          t)

{` The action of the conjugate: (p h p⁻¹) · ★ = ★ iff h fixes p⁻¹ · ★. `}
def repointed_fixed_iff (m : Nat) (p h : USym (symmetric_group (suc. m)))
  : Product
      (Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m))
          (conj_in (BG (symmetric_group (suc. m)) .carrier) (shape (symmetric_group (suc. m))) (shape (symmetric_group (suc. m))) p h)
          (inr. star.)) (inr. star.)
        → Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (repointed_point m p))
            (repointed_point m p))
      (Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (repointed_point m p))
          (repointed_point m p)
        → Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m))
            (conj_in (BG (symmetric_group (suc. m)) .carrier) (shape (symmetric_group (suc. m))) (shape (symmetric_group (suc. m))) p h)
            (inr. star.)) (inr. star.))
  ≔ let K ≔ symmetric_group (suc. m) in
    let X ≔ standard_symmetric_gset (suc. m) in
    let C ≔ BG K .carrier in
    let c0 ≔ shape K in
    let F ≔ Fin (suc. m) in
    let act ≔ gset_usym_act K X in
    let q ≔ repointed_point m p in
    let pinv ≔ inverse C c0 c0 p in
    let e1 : Id F (act (conj_in C c0 c0 p h) (inr. star.)) (act p (act h q))
      ≔ calc
          act (conj_in C c0 c0 p h) (inr. star.)
          = gset_act K X c0 c0 (concat C c0 c0 c0 h p) (act pinv (inr. star.))
            by gset_act_concat K X c0 c0 c0 pinv (concat C c0 c0 c0 h p) (inr. star.)
          = act p (act h q) by gset_act_concat K X c0 c0 c0 h p q ∎ in
    (e ↦ calc
       act h q = act pinv (act p (act h q)) by inverse F (act pinv (act p (act h q))) (act h q) (gset_act_inv_left K X p (act h q))
       = act pinv (act (conj_in C c0 c0 p h) (inr. star.))
         by map_path F F (act pinv) (act p (act h q)) (act (conj_in C c0 c0 p h) (inr. star.)) (inverse F (act (conj_in C c0 c0 p h) (inr. star.)) (act p (act h q)) e1)
       = q by map_path F F (act pinv) (act (conj_in C c0 c0 p h) (inr. star.)) (inr. star.) e ∎,
     e ↦ calc
       act (conj_in C c0 c0 p h) (inr. star.) = act p (act h q) by e1
       = act p q by map_path F F (act p) (act h q) q e
       = inr. star. by gset_act_inv_right K X p (inr. star.) ∎)

{` xca:SG2subSG3, in general form: h is in im(USym i^p) iff h fixes p⁻¹ · ★. `}
def repointed_image_stabilizer (m : Nat) (p h : USym (symmetric_group (suc. m)))
  : Product
      (SymmetryPickedOut (symmetric_group (suc. m)) (repointed_monomorphism m p) h
        → Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (repointed_point m p))
            (repointed_point m p))
      (Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) h (repointed_point m p))
          (repointed_point m p)
        → SymmetryPickedOut (symmetric_group (suc. m)) (repointed_monomorphism m p) h)
  ≔ let hin ≔ conj_in (BG (symmetric_group (suc. m)) .carrier) (shape (symmetric_group (suc. m))) (shape (symmetric_group (suc. m))) p h in
    (t ↦ repointed_fixed_iff m p h .fst (inclusion_picked_out_iff m hin .fst (repointed_image_iff m p h .fst t)),
     e ↦ repointed_image_iff m p h .snd (inclusion_picked_out_iff m hin .snd (repointed_fixed_iff m p h .snd e)))
