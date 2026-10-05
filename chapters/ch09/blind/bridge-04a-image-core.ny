export "bridge-01-epi-mono"
export "../../../src/941-image-consequences"
export "../../../src/990-image-ua-identifications"

{` Bridges for subgroups.tex, sec:image (blind file 04-images), part 1: infrastructure.
   The blind def:Im(grphom) group BlindImg differs from our image_group only in the connectedness proof, and the
   blind pointing of Bp(f) (blind_zero_image_path, built by J and transport) equals ours (image_projection_point)
   because paths in the 0-image are determined by their first components. The blind def:image group BlindImage is
   our image_group_aut; it is related to image_group by the isomorphism "first projection". Both blind image
   operations (group, projection, inclusion, mono proof) are identified with ours, so every blind statement about
   them is transported from ours. `}

{` Paths in Σ A P with P set-valued are determined by their first components. `}
def bridge9_sigma_set_path_eq (A : Type) (P : A → Type) (hP : (x : A) → isSet (P x)) (u v : Σ A P)
  (α β : Id (Σ A P) u v) (r : Id (Id A (u .fst) (v .fst)) (α .fst) (β .fst))
  : Id (Id (Σ A P) u v) α β
  ≔ let Q ≔ (p ↦ Id P p (u .snd) (v .snd)) : Id A (u .fst) (v .fst) → Type in
    let hQ : (p : Id A (u .fst) (v .fst)) → isProp (Q p)
      ≔ p ↦ J A (u .fst) (y q ↦ (b : P y) → isProp (Id P q (u .snd) b)) (b ↦ hP (u .fst) (u .snd) b) (v .fst) p (v .snd) in
    refl ((t ↦ (t .fst, t .snd)) : Σ (Id A (u .fst) (v .fst)) Q → Id (Σ A P) u v)
      (subtype_equal (Id A (u .fst) (v .fst)) Q hQ (α .fst, α .snd) (β .fst, β .snd) r)

{` The first component of the blind pointing path of Bp(f) is the pointing path q itself. `}
def bridge9_aux_fst (A B : Type) (f : A → B) (a : A) (w : B) (r : Id B (f a) w)
  : Id (Id B w (f a)) (blind_zero_image_path_aux A B f a w r .fst) (inverse B (f a) w r)
  ≔ let ZI ≔ ZeroImage A B f in
    let PA ≔ (w' r' ↦ Id ZI (w', set_trunc (BookFiber A B f w') (a, inverse B (f a) w' r'))
                 (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a)))) : (w' : B) → Id B (f a) w' → Type in
    let bA : PA (f a) (refl (f a))
      ≔ (refl (f a), refl ((x ↦ set_trunc (BookFiber A B f (f a)) (a, x)) : Id B (f a) (f a) → SetTrunc (BookFiber A B f (f a)))
                     (inverse_refl B (f a))) in
    let jt ≔ J B (f a) PA bA (f a) (refl (f a)) in
    J B (f a) (w' r' ↦ Id (Id B w' (f a)) (blind_zero_image_path_aux A B f a w' r' .fst) (inverse B (f a) w' r'))
      (concat (Id B (f a) (f a)) (jt .fst) (refl (f a)) (inverse B (f a) (f a) (refl (f a)))
        (map_path (PA (f a) (refl (f a))) (Id B (f a) (f a)) (t ↦ t .fst) jt bA
          (inverse (PA (f a) (refl (f a))) bA jt (Jβ B (f a) PA bA)))
        (inverse (Id B (f a) (f a)) (inverse B (f a) (f a) (refl (f a))) (refl (f a)) (inverse_refl B (f a))))
      w r

def bridge9_transport_fst (A B : Type) (f : A → B) (b : B) (a : A) (x y : Id B b (f a)) (s : Id (Id B b (f a)) x y)
  (α : Id (ZeroImage A B f) (b, set_trunc (BookFiber A B f b) (a, x)) (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a))))
  : Id (Id B b (f a))
      (transport (Id B b (f a))
        (x' ↦ Id (ZeroImage A B f) (b, set_trunc (BookFiber A B f b) (a, x')) (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a))))
        x y s α .fst)
      (α .fst)
  ≔ let Fam ≔ (x' ↦ Id (ZeroImage A B f) (b, set_trunc (BookFiber A B f b) (a, x')) (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a))))
        : Id B b (f a) → Type in
    J (Id B b (f a)) x (y' s' ↦ Id (Id B b (f a)) (transport (Id B b (f a)) Fam x y' s' α .fst) (α .fst))
      (map_path (Fam x) (Id B b (f a)) (t ↦ t .fst) (transport (Id B b (f a)) Fam x x (refl x) α) α
        (transport_refl (Id B b (f a)) Fam x α))
      y s

def bridge9_zip_fst (A B : Type) (f : A → B) (b : B) (a : A) (q : Id B b (f a))
  : Id (Id B b (f a)) (blind_zero_image_path A B f b a q .fst) q
  ≔ let iq ≔ inverse B b (f a) q in
    let iiq ≔ inverse B (f a) b iq in
    let α ≔ blind_zero_image_path_aux A B f a b iq in
    concat (Id B b (f a)) (blind_zero_image_path A B f b a q .fst) (α .fst) q
      (bridge9_transport_fst A B f b a iiq q (inverse_inverse B b (f a) q) α)
      (concat (Id B b (f a)) (α .fst) iiq q (bridge9_aux_fst A B f a b iq) (inverse_inverse B b (f a) q))

{` The blind pointing of Bp(f) is ours. `}
def bridge9_proj_point_path (G H : Group) (f : GroupHom G H)
  : Id (Id (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f)) (shape H, cokernel_point G H f)
         (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G)))
      (blind_im_proj_point G H f) (image_projection_point G H f)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in
    bridge9_sigma_set_path_eq B (w ↦ SetTrunc (BookFiber A B Bf w)) (w ↦ set_trunc_set (BookFiber A B Bf w))
      (shape H, cokernel_point G H f) (zero_image_factor A B Bf (shape G))
      (blind_im_proj_point G H f) (image_projection_point G H f)
      (bridge9_zip_fst A B Bf (shape H) (shape G) (hom_point G H f))

{` Image triples (Z, p : G → Z, i : Z → G') and their identification along an isomorphism. `}
def bridge9_ImgTriple (G G' : Group) : Type ≔ Σ Group (Z ↦ Product (GroupHom G Z) (GroupHom Z G'))

def bridge9_triple_motive (G G' Z : Group) (p : GroupHom G Z) (i : GroupHom Z G') (u : Σ Group (K ↦ GroupIso Z K)) : Type
  ≔ (p' : GroupHom G (u .fst)) (i' : GroupHom (u .fst) G')
    → Id (GroupHom G (u .fst)) (group_hom_compose G Z (u .fst) p (u .snd .fst)) p'
    → Id (GroupHom Z G') i (group_hom_compose Z (u .fst) G' (u .snd .fst) i')
    → Id (bridge9_ImgTriple G G') (Z, (p, i)) (u .fst, (p', i'))

def bridge9_triple_path (G G' Z Z' : Group) (Q : GroupIso Z Z') (p : GroupHom G Z) (i : GroupHom Z G')
  (p' : GroupHom G Z') (i' : GroupHom Z' G')
  (cp : Id (GroupHom G Z') (group_hom_compose G Z Z' p (Q .fst)) p')
  (ci : Id (GroupHom Z G') i (group_hom_compose Z Z' G' (Q .fst) i'))
  : Id (bridge9_ImgTriple G G') (Z, (p, i)) (Z', (p', i'))
  ≔ let T ≔ Σ Group (K ↦ GroupIso Z K) in
    transport T (bridge9_triple_motive G G' Z p i) (Z, group_iso_id Z) (Z', Q)
      (contractible_prop T (group_iso_total_contractible Z) (Z, group_iso_id Z) (Z', Q))
      (p0 i0 c0 d0 ↦
        (refl Z,
         (concat (GroupHom G Z) p (group_hom_compose G Z Z p (group_hom_id Z)) p0
            (inverse (GroupHom G Z) (group_hom_compose G Z Z p (group_hom_id Z)) p (group_hom_compose_id G Z p)) c0,
          concat (GroupHom Z G') i (group_hom_compose Z Z G' (group_hom_id Z) i0) i0 d0 (group_hom_id_compose Z G' i0))))
      p' i' cp ci

{` Image operations with their mono proofs. `}
def bridge9_ImgOp : Type ≔ (G G' : Group) (f : GroupHom G G') → bridge9_ImgTriple G G'

def bridge9_OpMono (T : bridge9_ImgOp) : Type
  ≔ (G G' : Group) (f : GroupHom G G') → IsGroupMono (T G G' f .fst) G' (T G G' f .snd .snd)

def bridge9_ImgOpM : Type ≔ Σ bridge9_ImgOp bridge9_OpMono

def bridge9_op_mono_prop (T : bridge9_ImgOp) : isProp (bridge9_OpMono T)
  ≔ pi_prop Group (G ↦ (G' : Group) (f : GroupHom G G') → IsGroupMono (T G G' f .fst) G' (T G G' f .snd .snd))
      (G ↦ pi_prop Group (G' ↦ (f : GroupHom G G') → IsGroupMono (T G G' f .fst) G' (T G G' f .snd .snd))
        (G' ↦ pi_prop (GroupHom G G') (f ↦ IsGroupMono (T G G' f .fst) G' (T G G' f .snd .snd))
          (f ↦ is_group_mono_prop (T G G' f .fst) G' (T G G' f .snd .snd))))

def bridge9_opm_path (a b : bridge9_ImgOpM)
  (h : (G G' : Group) (f : GroupHom G G') → Id (bridge9_ImgTriple G G') (a .fst G G' f) (b .fst G G' f))
  : Id bridge9_ImgOpM a b
  ≔ subtype_equal bridge9_ImgOp bridge9_OpMono bridge9_op_mono_prop a b
      (funext Group (G ↦ (G' : Group) (f : GroupHom G G') → bridge9_ImgTriple G G') (a .fst) (b .fst)
        (G ↦ funext Group (G' ↦ (f : GroupHom G G') → bridge9_ImgTriple G G') (a .fst G) (b .fst G)
          (G' ↦ funext (GroupHom G G') (_ ↦ bridge9_ImgTriple G G') (a .fst G G') (b .fst G G') (h G G'))))

def bridge9_our_op : bridge9_ImgOpM
  ≔ ((G G' f ↦ (image_group G G' f, (image_projection G G' f, image_inclusion G G' f))),
     (G G' f ↦ image_inclusion_mono G G' f))

def bridge9_img_op : bridge9_ImgOpM
  ≔ ((G G' f ↦ (BlindImg G G' f, (blind_im_proj G G' f, blind_im_incl G G' f))),
     (G G' f ↦ blind_im_incl_mono G G' f))

def bridge9_aut_op : bridge9_ImgOpM
  ≔ ((G G' f ↦ (BlindImage G G' f, (blind_image_prj G G' f, blind_image_incl G G' f))),
     (G G' f ↦ blind_image_incl_mono G G' f))

{` def:Im(grphom): BlindImg ≅ image_group by the identity of im₀(Bf). `}
def bridge9_img_iso (G H : Group) (f : GroupHom G H) : GroupIso (BlindImg G H f) (image_group G H f)
  ≔ (mkhom (BlindImg G H f) (image_group G H f) (identity (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f)),
       refl (shape (image_group G H f))),
     identity_book_equiv (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f)) .equiv)

def bridge9_img_triple (G H : Group) (f : GroupHom G H)
  : Id (bridge9_ImgTriple G H) (bridge9_img_op .fst G H f) (bridge9_our_op .fst G H f)
  ≔ let Z ≔ BlindImg G H f in let I ≔ image_group G H f in
    let ZI ≔ ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f) in
    let c ≔ shape I in let d ≔ zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G) in
    bridge9_triple_path G H Z I (bridge9_img_iso G H f) (blind_im_proj G H f) (blind_im_incl G H f)
      (image_projection G H f) (image_inclusion G H f)
      (ch9_hom_path G I (group_hom_compose G Z I (blind_im_proj G H f) (bridge9_img_iso G H f .fst)) (image_projection G H f)
        ((z ↦ refl (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) z)),
         calc
           concat ZI c d d (concat ZI c c d (refl c) (blind_im_proj_point G H f)) (refl d)
           = concat ZI c c d (refl c) (blind_im_proj_point G H f) by concat_p1 ZI c d (concat ZI c c d (refl c) (blind_im_proj_point G H f))
           = blind_im_proj_point G H f by concat_1p ZI c d (blind_im_proj_point G H f)
           = image_projection_point G H f by bridge9_proj_point_path G H f ∎))
      (ch9_hom_path Z H (blind_im_incl G H f) (group_hom_compose Z I H (bridge9_img_iso G H f .fst) (image_inclusion G H f))
        ((u ↦ refl (u .fst)),
         calc
           concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))
           = refl (shape H) by concat_1p (BG H .carrier) (shape H) (shape H) (refl (shape H))
           = concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))
             by inverse (Id (BG H .carrier) (shape H) (shape H))
                  (concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))) (refl (shape H))
                  (concat_1p (BG H .carrier) (shape H) (shape H) (refl (shape H))) ∎))

def bridge9_img_op_path : Id bridge9_ImgOpM bridge9_img_op bridge9_our_op
  ≔ bridge9_opm_path bridge9_img_op bridge9_our_op bridge9_img_triple

{` def:image: BlindImage = Aut_{im₀}(…) ≅ image_group by the first projection of the component. `}
def bridge9_aut_iso (G H : Group) (f : GroupHom G H) : GroupIso (BlindImage G H f) (image_group G H f)
  ≔ let X ≔ ActionType H (cokernel G H f) in let x : X ≔ (shape H, cokernel_point G H f) in
    (mkhom (BlindImage G H f) (image_group G H f) ((u ↦ u .fst), refl x),
     book_equivalence (NativeComponent X x) X (ch9_component_equiv X x (cokernel_action_type_connected G H f)) .equiv)

def bridge9_aut_triple (G H : Group) (f : GroupHom G H)
  : Id (bridge9_ImgTriple G H) (bridge9_aut_op .fst G H f) (bridge9_our_op .fst G H f)
  ≔ let Z ≔ BlindImage G H f in let I ≔ image_group G H f in
    let X ≔ ActionType H (cokernel G H f) in let x : X ≔ (shape H, cokernel_point G H f) in
    let d ≔ zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G) in
    let k ≔ blind_image_prj G H f in
    let kp ≔ hom_point G Z k in
    bridge9_triple_path G H Z I (bridge9_aut_iso G H f) k (blind_image_incl G H f)
      (image_projection G H f) (image_inclusion G H f)
      (ch9_hom_path G I (group_hom_compose G Z I k (bridge9_aut_iso G H f .fst)) (image_projection G H f)
        ((z ↦ refl (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) z)),
         calc
           concat X x d d (concat X x x d (refl x) (refl ((u ↦ u .fst) : NativeComponent X x → X) kp)) (refl d)
           = concat X x x d (refl x) (refl ((u ↦ u .fst) : NativeComponent X x → X) kp)
             by concat_p1 X x d (concat X x x d (refl x) (refl ((u ↦ u .fst) : NativeComponent X x → X) kp))
           = refl ((u ↦ u .fst) : NativeComponent X x → X) kp by concat_1p X x d (refl ((u ↦ u .fst) : NativeComponent X x → X) kp)
           = blind_im_proj_point G H f
             by equiv_counit (Id (NativeComponent X x) (component_point X x) (hom_function G Z k (shape G))) (Id X x d)
                  (component_path_equiv X x (component_point X x) (hom_function G Z k (shape G))) (blind_im_proj_point G H f)
           = image_projection_point G H f by bridge9_proj_point_path G H f ∎))
      (ch9_hom_path Z H (blind_image_incl G H f) (group_hom_compose Z I H (bridge9_aut_iso G H f .fst) (image_inclusion G H f))
        ((u ↦ refl (u .fst .fst)),
         calc
           concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))
           = refl (shape H) by concat_1p (BG H .carrier) (shape H) (shape H) (refl (shape H))
           = concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))
             by inverse (Id (BG H .carrier) (shape H) (shape H))
                  (concat (BG H .carrier) (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))) (refl (shape H))
                  (concat_1p (BG H .carrier) (shape H) (shape H) (refl (shape H))) ∎))

def bridge9_aut_op_path : Id bridge9_ImgOpM bridge9_aut_op bridge9_our_op
  ≔ bridge9_opm_path bridge9_aut_op bridge9_our_op bridge9_aut_triple

{` Transport of a statement about an image operation from ours to a blind one. `}
def bridge9_op_transport (S : bridge9_ImgOpM → Type) (b : bridge9_ImgOpM) (e : Id bridge9_ImgOpM b bridge9_our_op)
  (h : S bridge9_our_op) : S b
  ≔ transport bridge9_ImgOpM S bridge9_our_op b (inverse bridge9_ImgOpM b bridge9_our_op e) h
