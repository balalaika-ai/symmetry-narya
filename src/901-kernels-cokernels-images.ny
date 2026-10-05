export "900-group-monos-epis"

{` Chapter 9 (subgroups.tex), sec:ker: def:kernel, def:cokernel,
   lem:isTrans(coker), rem:imageandcokernel, def:Im(grphom), the image
   factorization of the classifying maps and the projection/inclusion
   homomorphisms (xca:p-epi-i-mono, first part), def:image (the explicit
   automorphism-group form).

   Conventions: the preimage (Bf)⁻¹(w) is BookFiber BG BH Bf w
   = Σ_{z:BG} (w = Bf z), the book's orientation. `}

{` The fiber of Bf at w. `}
def HomFiber (G H : Group) (f : GroupHom G H) (w : BG H .carrier) : Type
  ≔ BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w

def hom_fiber_groupoid (G H : Group) (f : GroupHom G H) (w : BG H .carrier) : isGroupoid (HomFiber G H f w)
  ≔ action_type_groupoid G (gset_restrict G H f (gset_paths H w))

{` Set truncation commutes with transport. `}
def ch9_set_trunc_transport (B : Type) (P : B → Type) (w w' : B) (p : Id B w w') (x : P w)
  : Id (SetTrunc (P w')) (transport B (v ↦ SetTrunc (P v)) w w' p (set_trunc (P w) x))
      (set_trunc (P w') (transport B P w w' p x))
  ≔ J B w (w' p ↦ Id (SetTrunc (P w')) (transport B (v ↦ SetTrunc (P v)) w w' p (set_trunc (P w) x))
            (set_trunc (P w') (transport B P w w' p x)))
      (calc
        transport B (v ↦ SetTrunc (P v)) w w (refl w) (set_trunc (P w) x)
        = set_trunc (P w) x by transport_refl B (v ↦ SetTrunc (P v)) w (set_trunc (P w) x)
        = set_trunc (P w) (transport B P w w (refl w) x)
          by refl (set_trunc (P w)) (inverse (P w) (transport B P w w (refl w) x) x (transport_refl B P w x)) ∎)
      w' p

{` def:kernel. The kernel group Ker(f) ≔ Aut_{(Bf)⁻¹(sh_H)}(sh_G, Bf_pt).
   As in the footnote, (Bf)⁻¹(sh_H) is (judgmentally) the action type of
   the restriction f^*P_H of the principal H-torsor, and Ker(f) is
   (judgmentally) the stabilizer group of f^*P_H at Bf_pt (chapter 5's
   stabilizer_group); the kernel map is the first projection, pointed by
   reflexivity, a monomorphism (stabilizer_inclusion_mono). `}
def kernel_gset (G H : Group) (f : GroupHom G H) : GSet G ≔ gset_restrict G H f (principal_gset H)

def kernel_shape (G H : Group) (f : GroupHom G H) : HomFiber G H f (shape H) ≔ (shape G, hom_point G H f)

def kernel_fiber_action_type (G H : Group) (f : GroupHom G H)
  : Id Type (HomFiber G H f (shape H)) (ActionType G (kernel_gset G H f))
  ≔ refl (HomFiber G H f (shape H))

def kernel_group (G H : Group) (f : GroupHom G H) : Group
  ≔ stabilizer_group G (kernel_gset G H f) (hom_point G H f)

def kernel_group_aut (G H : Group) (f : GroupHom G H)
  : Id Group (kernel_group G H f)
      (automorphism_group (HomFiber G H f (shape H)) (hom_fiber_groupoid G H f (shape H)) (kernel_shape G H f))
  ≔ refl (kernel_group G H f)

def kernel_group_classifying (G H : Group) (f : GroupHom G H)
  : Id Type (BG (kernel_group G H f) .carrier) (NativeComponent (HomFiber G H f (shape H)) (kernel_shape G H f))
  ≔ refl (BG (kernel_group G H f) .carrier)

def kernel_inclusion (G H : Group) (f : GroupHom G H) : GroupHom (kernel_group G H f) G
  ≔ stabilizer_inclusion G (kernel_gset G H f) (hom_point G H f)

def kernel_inclusion_function (G H : Group) (f : GroupHom G H) (u : BG (kernel_group G H f) .carrier)
  : Id (BG G .carrier) (hom_function (kernel_group G H f) G (kernel_inclusion G H f) u) (u .fst .fst)
  ≔ refl (u .fst .fst)

def kernel_inclusion_mono (G H : Group) (f : GroupHom G H)
  : IsGroupMono (kernel_group G H f) G (kernel_inclusion G H f)
  ≔ stabilizer_inclusion_mono G (kernel_gset G H f) (hom_point G H f)

{` ker : Hom(G, H) → Mono(G). `}
def kernel (G H : Group) (f : GroupHom G H) : GroupMonos G
  ≔ (kernel_group G H f, (kernel_inclusion G H f, kernel_inclusion_mono G H f))

{` "The symmetries of the shape of the kernel are those g : USym G with
   g · Bf_pt = Bf_pt, i.e. USym f (g) = refl." First the action of f^*P_H on
   Bf_pt is Bf_pt · ap_{Bf}(g); then g · Bf_pt = Bf_pt iff
   USym f (g) = Bf_pt · ap_{Bf}(g) · Bf_pt⁻¹ = refl. `}
def kernel_usym_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (USym (kernel_group G H f))
      (Σ (USym G) (g ↦ Id (gset_underlying G (kernel_gset G H f))
        (gset_usym_act G (kernel_gset G H f) g (hom_point G H f)) (hom_point G H f)))
  ≔ let X ≔ kernel_gset G H f in
    let T ≔ ActionType G X in
    let c ≔ component_point T (shape G, hom_point G H f) in
    compose_equiv (Id (NativeComponent T (shape G, hom_point G H f)) c c) (Id T (shape G, hom_point G H f) (shape G, hom_point G H f))
      (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g (hom_point G H f)) (hom_point G H f)))
      (component_path_equiv T (shape G, hom_point G H f) c c)
      (action_type_path_equiv G X (shape G, hom_point G H f) (shape G, hom_point G H f))

{` def:cokernel. coker(f) : BH → Set, w ↦ ‖(Bf)⁻¹(w)‖₀. `}
def cokernel (G H : Group) (f : GroupHom G H) : GSet H
  ≔ w ↦ (SetTrunc (HomFiber G H f w), set_trunc_set (HomFiber G H f w))

def cokernel_point (G H : Group) (f : GroupHom G H) : gset_underlying H (cokernel G H f)
  ≔ set_trunc (HomFiber G H f (shape H)) (kernel_shape G H f)

{` The action type of the cokernel is (judgmentally) the set image
   im₀(Bf) = Σ_{w:BH} ‖(Bf)⁻¹(w)‖₀ (ZeroImage, module 106; the footnote of
   def:Im(grphom)). `}
def cokernel_action_type (G H : Group) (f : GroupHom G H)
  : Id Type (ActionType H (cokernel G H f)) (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ refl (ActionType H (cokernel G H f))

{` lem:isTrans(coker). The proof is the second one of rem:imageandcokernel
   (lem:conistrans): BG is connected, so is its set image
   Σ_{w:BH} ‖(Bf)⁻¹(w)‖₀ (zero_image_connected, module 116), which is the
   action type of coker(f). `}
def cokernel_action_type_connected (G H : Group) (f : GroupHom G H) : Connected (ActionType H (cokernel G H f))
  ≔ zero_image_connected (BG G .carrier) (BG H .carrier) (hom_function G H f) (bg_connected G)

def cokernel_transitive (G H : Group) (f : GroupHom G H) : IsTransitive H (cokernel G H f)
  ≔ connected_action_type_transitive H (cokernel G H f) (cokernel_action_type_connected G H f)

{` rem:imageandcokernel: (coker(f), |(sh_G, Bf_pt)|₀, !) : Sub(H). `}
def image_subgroup (G H : Group) (f : GroupHom G H) : Subgroups H
  ≔ (cokernel G H f, cokernel_point G H f, cokernel_transitive G H f)

{` def:Im(grphom). Img(f) ≔ mkgroup(im₀(Bf), (sh_H, |(sh_G, Bf_pt)|₀)); it is
   (judgmentally) the underlying group of the subgroup image_subgroup. `}
def image_group (G H : Group) (f : GroupHom G H) : Group ≔ subgroup_group H (image_subgroup G H f)

def image_group_classifying (G H : Group) (f : GroupHom G H)
  : Id Pointed (BG (image_group G H f))
      (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f), (shape H, cokernel_point G H f))
  ≔ refl (BG (image_group G H f))

{` Bi(f) ≔ fst, pointed by reflexivity: a monomorphism. `}
def image_inclusion (G H : Group) (f : GroupHom G H) : GroupHom (image_group G H f) H
  ≔ subgroup_inclusion H (image_subgroup G H f)

def image_inclusion_mono (G H : Group) (f : GroupHom G H)
  : IsGroupMono (image_group G H f) H (image_inclusion G H f)
  ≔ subgroup_inclusion_mono H (image_subgroup G H f)

{` img : Hom(G, H) → Mono(H). `}
def image_mono (G H : Group) (f : GroupHom G H) : GroupMonos H
  ≔ (image_group G H f, (image_inclusion G H f, image_inclusion_mono G H f))

{` Bp(f)(z) ≔ (Bf(z), |(z, refl)|₀), with the pointing path asked for in
   xca:p-epi-i-mono: (Bf_pt, the transport of |(sh_G, Bf_pt)|₀ along Bf_pt,
   which is |(sh_G, Bf_pt⁻¹ · Bf_pt)|₀ = |(sh_G, refl)|₀). `}
def ch9_fiber_transport (A B : Type) (f : A → B) (w w' : B) (p : Id B w w') (a : A) (q : Id B w (f a))
  : Id (BookFiber A B f w') (transport B (v ↦ BookFiber A B f v) w w' p (a, q)) (a, concat B w' w (f a) (inverse B w w' p) q)
  ≔ J B w (w' p ↦ Id (BookFiber A B f w') (transport B (v ↦ BookFiber A B f v) w w' p (a, q))
            (a, concat B w' w (f a) (inverse B w w' p) q))
      (calc
        transport B (v ↦ BookFiber A B f v) w w (refl w) (a, q)
        = (a, q) by transport_refl B (v ↦ BookFiber A B f v) w (a, q)
        = (a, concat B w w (f a) (refl w) q)
          by refl ((r ↦ (a, r)) : Id B w (f a) → BookFiber A B f w) (inverse (Id B w (f a)) (concat B w w (f a) (refl w) q) q (concat_1p B w (f a) q))
        = (a, concat B w w (f a) (inverse B w w (refl w)) q)
          by refl ((r ↦ (a, concat B w w (f a) r q)) : Id B w w → BookFiber A B f w) (inverse (Id B w w) (inverse B w w (refl w)) (refl w) (inverse_refl B w)) ∎)
      w' p

def image_projection_point (G H : Group) (f : GroupHom G H)
  : Id (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f)) (shape H, cokernel_point G H f)
      (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G))
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in
    let p ≔ hom_point G H f in
    let F : B → Type ≔ w ↦ SetTrunc (BookFiber A B Bf w) in
    (p, pathover_of_eq B F (shape H) (Bf (shape G)) p (cokernel_point G H f)
          (set_trunc (BookFiber A B Bf (Bf (shape G))) (shape G, refl (Bf (shape G))))
      (calc
        transport B F (shape H) (Bf (shape G)) p (set_trunc (BookFiber A B Bf (shape H)) (shape G, p))
        = set_trunc (BookFiber A B Bf (Bf (shape G))) (transport B (v ↦ BookFiber A B Bf v) (shape H) (Bf (shape G)) p (shape G, p))
          by ch9_set_trunc_transport B (v ↦ BookFiber A B Bf v) (shape H) (Bf (shape G)) p (shape G, p)
        = set_trunc (BookFiber A B Bf (Bf (shape G))) (shape G, concat B (Bf (shape G)) (shape H) (Bf (shape G)) (inverse B (shape H) (Bf (shape G)) p) p)
          by refl (set_trunc (BookFiber A B Bf (Bf (shape G)))) (ch9_fiber_transport A B Bf (shape H) (Bf (shape G)) p (shape G) p)
        = set_trunc (BookFiber A B Bf (Bf (shape G))) (shape G, refl (Bf (shape G)))
          by refl ((r ↦ set_trunc (BookFiber A B Bf (Bf (shape G))) (shape G, r)) : Id B (Bf (shape G)) (Bf (shape G)) → F (Bf (shape G)))
               (concat_inverse_left B (shape H) (Bf (shape G)) p) ∎))

def image_projection (G H : Group) (f : GroupHom G H) : GroupHom G (image_group G H f)
  ≔ mkhom G (image_group G H f)
      (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f), image_projection_point G H f)

{` "Under these definitions we have Bf ≡ Bi(f) ∘ Bp(f) for the unpointed
   maps": judgmental. `}
def image_factorization_function (G H : Group) (f : GroupHom G H)
  : Id (BG G .carrier → BG H .carrier) (hom_function G H f)
      (z ↦ hom_function (image_group G H f) H (image_inclusion G H f)
        (hom_function G (image_group G H f) (image_projection G H f) z))
  ≔ refl (hom_function G H f)

{` xca:p-epi-i-mono, first part: with this pointing of Bp(f), f = i(f) ∘ p(f)
   as pointed maps (the pointing of the composite is refl · Bf_pt). `}
def image_factorization_path (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G H) f (group_hom_compose G (image_group G H f) H (image_projection G H f) (image_inclusion G H f))
  ≔ let B ≔ BG H .carrier in let p ≔ hom_point G H f in let b ≔ hom_function G H f (shape G) in
    ch9_hom_path G H f (group_hom_compose G (image_group G H f) H (image_projection G H f) (image_inclusion G H f))
      ((z ↦ refl (hom_function G H f z)),
       calc
         concat B (shape H) b b p (refl b)
         = p by concat_p1 B (shape H) b p
         = concat B (shape H) (shape H) b (refl (shape H)) p by inverse (Id B (shape H) b) (concat B (shape H) (shape H) b (refl (shape H)) p) p (concat_1p B (shape H) b p) ∎)

{` xca:p-epi-i-mono, second part: Bp(f) has connected fibers (it is the
   0-connected factor of the 0-image factorization, module 106); that p(f)
   is an epimorphism follows with lem:epi-surj (module 938), and i(f) is a
   monomorphism (image_inclusion_mono). `}
def image_projection_connected_fibers (G H : Group) (f : GroupHom G H)
  : ConnectedFibers (BG G .carrier) (BG (image_group G H f) .carrier) (hom_function G (image_group G H f) (image_projection G H f))
  ≔ zero_image_factor_connected_fibers (BG G .carrier) (BG H .carrier) (hom_function G H f)

{` def:image. The book's explicit form Img(f) ≔ Aut_{Σ_{w:BH} coker(f)(w)}(sh_H, |(sh_G, Bf_pt)|₀)
   uses the component of the (connected) action type of the cokernel; it is
   identified with Img(f) of def:Im(grphom) by the pointed equivalence
   "first projection" from the component. `}
{` The first projection from the component of a point of a connected type
   is an equivalence (as alternating_component_equiv of module 459, which is
   not imported here). `}
def ch9_component_equiv (X : Type) (x : X) (h : Connected X) : Equiv (NativeComponent X x) X
  ≔ quasi_inverse_equiv (NativeComponent X x) X (u ↦ u .fst) (y ↦ (y, h .snd x y))
      (u ↦ component_path X x (u .fst, h .snd x (u .fst)) u (refl (u .fst)))
      (y ↦ refl y)

def image_group_aut (G H : Group) (f : GroupHom G H) : Group
  ≔ automorphism_group (ActionType H (cokernel G H f)) (action_type_groupoid H (cokernel G H f))
      (shape H, cokernel_point G H f)

def image_group_aut_path (G H : Group) (f : GroupHom G H) : Id Group (image_group_aut G H f) (image_group G H f)
  ≔ let X ≔ ActionType H (cokernel G H f) in let x : X ≔ (shape H, cokernel_point G H f) in
    group_path_from_pointed_equiv (image_group_aut G H f) (image_group G H f)
      (((u ↦ u .fst), refl x),
       book_equivalence (NativeComponent X x) X (ch9_component_equiv X x (cokernel_action_type_connected G H f)) .equiv)
