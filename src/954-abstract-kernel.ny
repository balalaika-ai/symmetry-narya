export "903-normal-subgroups"

{` Chapter 9 (subgroups.tex 778-789), xca:abstract-kernel, and the link
   between kernel membership and the stabilizer of Bf_pt used in
   exa:fibersofcomposites.

   X(f)(z) ≔ Σ_{p : sh_H = Bf(z)} ∃_{g : sh_G = z} (p = Bf(g) Bf_pt), where
   the book's Bf(g) Bf_pt (first Bf_pt, then ap_{Bf}(g)) is
   concat Bf_pt (ap_{Bf} g). `}

{` Transport in z ↦ (b = f z) along e is post-composition with ap_f(e). `}
def ch9w2_transport_ap_path (X Y : Type) (f : X → Y) (b : Y) (x x' : X) (e : Id X x x') (i : Id Y b (f x))
  : Id (Id Y b (f x')) (transport X (z ↦ Id Y b (f z)) x x' e i) (concat Y b (f x) (f x') i (refl f e))
  ≔ J X x (x' e ↦ Id (Id Y b (f x')) (transport X (z ↦ Id Y b (f z)) x x' e i) (concat Y b (f x) (f x') i (refl f e)))
      (calc
        transport X (z ↦ Id Y b (f z)) x x (refl x) i = i by transport_refl X (z ↦ Id Y b (f z)) x i
        = concat Y b (f x) (f x) i (refl (f x)) by inverse (Id Y b (f x)) (concat Y b (f x) (f x) i (refl (f x))) i (concat_p1 Y b (f x) i) ∎)
      x' e

{` g ∈ Ker(f) (the stabilizer of Bf_pt in f^*P_H) iff USym f(g) = e. `}
def kernel_member_iff (G H : Group) (f : GroupHom G H) (g : USym G)
  : Product
      (Id (gset_underlying G (kernel_gset G H f)) (gset_usym_act G (kernel_gset G H f) g (hom_point G H f)) (hom_point G H f)
        → Id (USym H) (usym_hom G H f g) (usym_unit H))
      (Id (USym H) (usym_hom G H f g) (usym_unit H)
        → Id (gset_underlying G (kernel_gset G H f)) (gset_usym_act G (kernel_gset G H f) g (hom_point G H f)) (hom_point G H f))
  ≔ let B ≔ BG H .carrier in let a ≔ shape H in let Bf ≔ hom_function G H f in let b ≔ Bf (shape G) in
    let p ≔ hom_point G H f in let r ≔ refl Bf g in
    let tr : Id (Id B a b) (gset_usym_act G (kernel_gset G H f) g p) (concat B a b b p r)
      ≔ ch9w2_transport_ap_path (BG G .carrier) B Bf a (shape G) (shape G) g p in
    (e ↦ calc
       usym_hom G H f g
       = concat B a b a p (concat B b b a r (inverse B a b p)) by refl (usym_hom G H f g)
       = concat B a b a (concat B a b b p r) (inverse B a b p)
         by inverse (Id B a a) (concat B a b a (concat B a b b p r) (inverse B a b p)) (concat B a b a p (concat B b b a r (inverse B a b p)))
              (concat_assoc B a b b a p r (inverse B a b p))
       = concat B a b a p (inverse B a b p)
         by refl ((q ↦ concat B a b a q (inverse B a b p)) : Id B a b → Id B a a)
              (concat (Id B a b) (concat B a b b p r) (gset_usym_act G (kernel_gset G H f) g p) p
                (inverse (Id B a b) (gset_usym_act G (kernel_gset G H f) g p) (concat B a b b p r) tr) e)
       = refl a by concat_inverse_right B a b p ∎,
     e ↦ calc
       gset_usym_act G (kernel_gset G H f) g p
       = concat B a b b p r by tr
       = concat B a b b p (concat B b a b (concat B b b a r (inverse B a b p)) p)
         by refl (concat B a b b p)
              (calc
                r = concat B b b b r (refl b) by inverse (Id B b b) (concat B b b b r (refl b)) r (concat_p1 B b b r)
                = concat B b b b r (concat B b a b (inverse B a b p) p)
                  by refl (concat B b b b r) (inverse (Id B b b) (concat B b a b (inverse B a b p) p) (refl b) (concat_inverse_left B a b p))
                = concat B b a b (concat B b b a r (inverse B a b p)) p
                  by inverse (Id B b b) (concat B b a b (concat B b b a r (inverse B a b p)) p) (concat B b b b r (concat B b a b (inverse B a b p) p))
                       (concat_assoc B b b a b r (inverse B a b p) p) ∎)
       = concat B a a b (concat B a b a p (concat B b b a r (inverse B a b p))) p
         by inverse (Id B a b) (concat B a a b (concat B a b a p (concat B b b a r (inverse B a b p))) p)
              (concat B a b b p (concat B b a b (concat B b b a r (inverse B a b p)) p))
              (concat_assoc B a b a b p (concat B b b a r (inverse B a b p)) p)
       = concat B a a b (refl a) p by refl ((q ↦ concat B a a b q p) : Id B a a → Id B a b) e
       = p by concat_1p B a b p ∎)

{` xca:abstract-kernel. The G-set X(f). `}
def AbstractKernelWitness (G H : Group) (f : GroupHom G H) (z : BG G .carrier)
  (p : Id (BG H .carrier) (shape H) (hom_function G H f z)) : Type
  ≔ Σ (Id (BG G .carrier) (shape G) z)
      (g ↦ Id (Id (BG H .carrier) (shape H) (hom_function G H f z)) p
        (concat (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_function G H f z) (hom_point G H f)
          (refl (hom_function G H f) g)))

def abstract_kernel_gset (G H : Group) (f : GroupHom G H) : GSet G
  ≔ z ↦ (Σ (Id (BG H .carrier) (shape H) (hom_function G H f z)) (p ↦ Mere (AbstractKernelWitness G H f z p)),
         sigma_set (Id (BG H .carrier) (shape H) (hom_function G H f z)) (p ↦ Mere (AbstractKernelWitness G H f z p))
           (bg_groupoid H (shape H) (hom_function G H f z))
           (p ↦ prop_is_set (Mere (AbstractKernelWitness G H f z p)) (mere_isprop (AbstractKernelWitness G H f z p))))

def abstract_kernel_point (G H : Group) (f : GroupHom G H) : gset_underlying G (abstract_kernel_gset G H f)
  ≔ let B ≔ BG H .carrier in let b ≔ hom_function G H f (shape G) in
    (hom_point G H f,
     mere (AbstractKernelWitness G H f (shape G) (hom_point G H f))
       (refl (shape G), inverse (Id B (shape H) b) (concat B (shape H) b b (hom_point G H f) (refl b)) (hom_point G H f)
         (concat_p1 B (shape H) b (hom_point G H f))))

{` Fiberwise, X(f)(z) is the orbit of Bf_pt in f^*P_H: ∃_g (p = g · Bf_pt) is
   ‖(sh_G, Bf_pt) = (z, p)‖. `}
def abstract_kernel_orbit_equiv (G H : Group) (f : GroupHom G H) (z : BG G .carrier)
  : Equiv (abstract_kernel_gset G H f z .fst)
      (orbit_gset G (kernel_gset G H f) (shape G, hom_point G H f) z .fst)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in
    let X ≔ kernel_gset G H f in
    let u : ActionType G X ≔ (shape G, hom_point G H f) in
    family_equiv (Id B (shape H) (Bf z))
      (p ↦ Mere (AbstractKernelWitness G H f z p))
      (p ↦ Mere (Id (ActionType G X) u (z, p)))
      (p ↦ iff_equiv (Mere (AbstractKernelWitness G H f z p)) (Mere (Id (ActionType G X) u (z, p)))
        (mere_isprop (AbstractKernelWitness G H f z p)) (mere_isprop (Id (ActionType G X) u (z, p)))
        (mere_rec (AbstractKernelWitness G H f z p) (Mere (Id (ActionType G X) u (z, p))) (mere_isprop (Id (ActionType G X) u (z, p)))
          (w ↦ mere (Id (ActionType G X) u (z, p)) (equiv_inverse_map (Id (ActionType G X) u (z, p)) (ActionTypePath G X u (z, p))
            (action_type_path_equiv G X u (z, p))
            (w .fst, concat (Id B (shape H) (Bf z)) (gset_act G X (shape G) z (w .fst) (hom_point G H f))
              (concat B (shape H) (Bf (shape G)) (Bf z) (hom_point G H f) (refl Bf (w .fst))) p
              (ch9w2_transport_ap_path A B Bf (shape H) (shape G) z (w .fst) (hom_point G H f))
              (inverse (Id B (shape H) (Bf z)) p (concat B (shape H) (Bf (shape G)) (Bf z) (hom_point G H f) (refl Bf (w .fst))) (w .snd))))))
        (mere_rec (Id (ActionType G X) u (z, p)) (Mere (AbstractKernelWitness G H f z p)) (mere_isprop (AbstractKernelWitness G H f z p))
          (q ↦ let w ≔ action_type_path_equiv G X u (z, p) .map q in
            mere (AbstractKernelWitness G H f z p)
              (w .fst, concat (Id B (shape H) (Bf z)) p (gset_act G X (shape G) z (w .fst) (hom_point G H f))
                (concat B (shape H) (Bf (shape G)) (Bf z) (hom_point G H f) (refl Bf (w .fst)))
                (inverse (Id B (shape H) (Bf z)) (gset_act G X (shape G) z (w .fst) (hom_point G H f)) p (w .snd))
                (ch9w2_transport_ap_path A B Bf (shape H) (shape G) z (w .fst) (hom_point G H f))))))

def abstract_kernel_orbit_path (G H : Group) (f : GroupHom G H)
  : Id (GSet G) (abstract_kernel_gset G H f) (orbit_gset G (kernel_gset G H f) (shape G, hom_point G H f))
  ≔ gset_path_from_equivs G (abstract_kernel_gset G H f) (orbit_gset G (kernel_gset G H f) (shape G, hom_point G H f))
      (abstract_kernel_orbit_equiv G H f)

def abstract_kernel_transitive (G H : Group) (f : GroupHom G H) : IsTransitive G (abstract_kernel_gset G H f)
  ≔ transport (GSet G) (IsTransitive G) (orbit_gset G (kernel_gset G H f) (shape G, hom_point G H f)) (abstract_kernel_gset G H f)
      (inverse (GSet G) (abstract_kernel_gset G H f) (orbit_gset G (kernel_gset G H f) (shape G, hom_point G H f))
        (abstract_kernel_orbit_path G H f))
      (orbit_gset_transitive G (kernel_gset G H f) (shape G, hom_point G H f))

{` X(f) : Sub(G). `}
def abstract_kernel_subgroup (G H : Group) (f : GroupHom G H) : Subgroups G
  ≔ (abstract_kernel_gset G H f, abstract_kernel_point G H f, abstract_kernel_transitive G H f)

{` X(f) = E(ker f) in Sub(G): both are the orbit of Bf_pt in f^*P_H
   (stabilizer_subgroup_path of module 508; ker f is the stabilizer mono). `}
def abstract_kernel_path (G H : Group) (f : GroupHom G H)
  : Id (Subgroups G) (abstract_kernel_subgroup G H f) (mono_to_subgroup G (kernel G H f))
  ≔ let X ≔ kernel_gset G H f in let x ≔ hom_point G H f in
    concat (Subgroups G) (abstract_kernel_subgroup G H f) (orbit_subgroup G X x) (mono_to_subgroup G (kernel G H f))
      (subgroup_path G (abstract_kernel_subgroup G H f) (orbit_subgroup G X x)
        (pointed_gset_path G (abstract_kernel_gset G H f) (orbit_gset G X (shape G, x)) (abstract_kernel_point G H f)
          (orbit_subgroup G X x .point) (abstract_kernel_orbit_equiv G H f)
          (subtype_equal (Id (BG H .carrier) (shape H) (hom_function G H f (shape G)))
            (p ↦ Mere (Id (ActionType G X) (shape G, x) (shape G, p))) (p ↦ mere_isprop (Id (ActionType G X) (shape G, x) (shape G, p)))
            (abstract_kernel_orbit_equiv G H f (shape G) .map (abstract_kernel_point G H f)) (orbit_subgroup G X x .point)
            (refl x))))
      (inverse (Subgroups G) (mono_to_subgroup G (stabilizer_mono G X x)) (orbit_subgroup G X x) (stabilizer_subgroup_path G X x))

{` If f is an epimorphism (here: Bf has connected fibers, lem:epi-surj
   (3')), X(f) simplifies to z ↦ (sh_H = Bf(z)): the existential is always
   inhabited. `}
def abstract_kernel_epi_equiv (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f) (z : BG G .carrier)
  : Equiv (abstract_kernel_gset G H f z .fst) (Id (BG H .carrier) (shape H) (hom_function G H f z))
  ≔ let X ≔ kernel_gset G H f in let u : ActionType G X ≔ (shape G, hom_point G H f) in
    let B ≔ BG H .carrier in
    compose_equiv (abstract_kernel_gset G H f z .fst) (orbit_gset G X u z .fst) (Id B (shape H) (hom_function G H f z))
      (abstract_kernel_orbit_equiv G H f z)
      (quasi_inverse_equiv (orbit_gset G X u z .fst) (Id B (shape H) (hom_function G H f z))
        (w ↦ w .fst) (p ↦ (p, c (shape H) .snd u (z, p)))
        (w ↦ (refl (w .fst), mere_isprop (Id (ActionType G X) u (z, w .fst)) (c (shape H) .snd u (z, w .fst)) (w .snd))) (p ↦ refl p))

def abstract_kernel_epi_path (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (GSet G) (abstract_kernel_gset G H f) (kernel_gset G H f)
  ≔ gset_path_from_equivs G (abstract_kernel_gset G H f) (kernel_gset G H f) (abstract_kernel_epi_equiv G H f c)
