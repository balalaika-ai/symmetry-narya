{` Blind statements for chapter 9 (subgroups.tex), section "The image of a homomorphism of groups". `}
export "02-kernels"
export "../../../src/116-images-preserve-connectedness"

{` Helper: a path q : b = f(a) gives (b, |(a,q)|₀) = (f(a), |(a, refl)|₀) in im₀(f) = Σ_{b:B} ‖f^{-1}(b)‖₀. `}
def blind_zero_image_path_aux (A B : Type) (f : A → B) (a : A) (w : B) (r : Id B (f a) w)
  : Id (ZeroImage A B f) (w, set_trunc (BookFiber A B f w) (a, inverse B (f a) w r))
      (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a)))
  ≔ J B (f a) (w' r' ↦ Id (ZeroImage A B f) (w', set_trunc (BookFiber A B f w') (a, inverse B (f a) w' r'))
                 (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a))))
      (refl (f a), refl ((x ↦ set_trunc (BookFiber A B f (f a)) (a, x)) : Id B (f a) (f a) → SetTrunc (BookFiber A B f (f a)))
                     (inverse_refl B (f a)))
      w r

def blind_zero_image_path (A B : Type) (f : A → B) (b : B) (a : A) (q : Id B b (f a))
  : Id (ZeroImage A B f) (b, set_trunc (BookFiber A B f b) (a, q)) (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a)))
  ≔ transport (Id B b (f a))
      (x ↦ Id (ZeroImage A B f) (b, set_trunc (BookFiber A B f b) (a, x)) (f a, set_trunc (BookFiber A B f (f a)) (a, refl (f a))))
      (inverse B (f a) b (inverse B b (f a) q)) q (inverse_inverse B b (f a) q)
      (blind_zero_image_path_aux A B f a b (inverse B b (f a) q))

{` def:Im(grphom). Img(f) ≔ mkgroup(im₀(Bf), (sh_H, |(sh_G, Bf_pt)|₀)), im₀(Bf) ≔ Σ_{w:BH} ‖(Bf)^{-1}(w)‖₀
   (connected and a groupoid: the proofs required by mkgroup). `}
def BlindImg (G H : Group) (f : GroupHom G H) : Group
  ≔ mkgroup (ZeroImage (BG G .carrier) (BG H .carrier) (hom_function G H f),
      (shape H, blind_coker_point G H f),
      zero_image_connected (BG G .carrier) (BG H .carrier) (hom_function G H f) (bg_connected G),
      action_type_groupoid H (blind_coker G H f))

{` Bp(f)(z) ≔ (Bf(z), |(z, refl)|₀), with a pointing path (xca:p-epi-i-mono asks for one). `}
def blind_im_proj_point (G H : Group) (f : GroupHom G H)
  : Id (BG (BlindImg G H f) .carrier) (shape (BlindImg G H f))
      (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G))
  ≔ blind_zero_image_path (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape H) (shape G) (hom_point G H f)

def blind_im_proj (G H : Group) (f : GroupHom G H) : GroupHom G (BlindImg G H f)
  ≔ mkhom G (BlindImg G H f) (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f), blind_im_proj_point G H f)

{` Bi(f) ≔ fst, pointed by reflexivity. `}
def blind_im_incl (G H : Group) (f : GroupHom G H) : GroupHom (BlindImg G H f) H
  ≔ mkhom (BlindImg G H f) H ((u ↦ u .fst), refl (shape H))

{` i(f) is a monomorphism in the sense of def:typeofmono (fst is a covering); used for the element of Mono(H). `}
def blind_im_incl_mono (G H : Group) (f : GroupHom G H) : IsGroupMono (BlindImg G H f) H (blind_im_incl G H f)
  ≔ covering_group_mono (BlindImg G H f) H (blind_im_incl G H f) (action_type_projection_covering H (blind_coker G H f))

{` def:Im(grphom) text: Bf ≡ Bi(f) ∘ Bp(f) for the unpointed maps. `}
def blind_im_unpointed_factorization : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Id (BG G .carrier → BG H .carrier) (hom_function G H f)
        (z ↦ hom_function (BlindImg G H f) H (blind_im_incl G H f) (hom_function G (BlindImg G H f) (blind_im_proj G H f) z))

{` xca:p-epi-i-mono. There is a pointing of Bp(f) with Bf = Bi(f) ∘ Bp(f) as pointed maps, making p(f) an
   epimorphism; i(f) is a monomorphism. `}
def blind_p_epi_i_mono : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Product
        (Σ (Id (BG (BlindImg G H f) .carrier) (shape (BlindImg G H f))
              (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape G))) (pt ↦
          Product
            (Id (BookPointedMap (BG G) (BG H)) (hom_B G H f)
              (book_pointed_compose (BG G) (BG (BlindImg G H f)) (BG H)
                (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f), pt)
                ((u ↦ u .fst), refl (shape H))))
            (BlindIsEpi G (BlindImg G H f)
              (mkhom G (BlindImg G H f) (zero_image_factor (BG G .carrier) (BG H .carrier) (hom_function G H f), pt)))))
        (BlindIsMono (BlindImg G H f) H (blind_im_incl G H f))

{` The pointing chosen above satisfies the triangle (so p(f), i(f) below factor f as homomorphisms). `}
def blind_im_factorization : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Id (GroupHom G H) f (group_hom_compose G (BlindImg G H f) H (blind_im_proj G H f) (blind_im_incl G H f))

def blind_im_proj_epi : Type
  ≔ (G H : Group) (f : GroupHom G H) → BlindIsEpi G (BlindImg G H f) (blind_im_proj G H f)

{` The type Epi(G) ×_Group Mono(H) ≔ Σ_{(Z,p):Epi(G)} Σ_{(Z',i):Mono(H)} (Z = Z'). `}
def BlindEpiMonoPullback (G H : Group) : Type
  ≔ Σ (BlindEpi G) (e ↦ Σ (GroupMonos H) (m ↦ Id Group (e .fst) (m .fst)))

{` The proofs "!" that p(f) is an epimorphism are a parameter of the definition (xca:p-epi-i-mono). `}
def BlindImProjEpi (G H : Group) : Type ≔ (f : GroupHom G H) → BlindIsEpi G (BlindImg G H f) (blind_im_proj G H f)

{` def:Im-fact. Imfact(f) ≔ ((Img(f), p(f)), (Img(f), i(f)), refl_{Img(f)}). `}
def blind_imfact (G H : Group) (hp : BlindImProjEpi G H) (f : GroupHom G H) : BlindEpiMonoPullback G H
  ≔ ((BlindImg G H f, (blind_im_proj G H f, hp f)),
     ((BlindImg G H f, (blind_im_incl G H f, blind_im_incl_mono G H f)), refl (BlindImg G H f)))

{` lem:Im-fact-unique. Imfact is an equivalence (for the proofs hp; isepi is a proposition). `}
def blind_im_fact_unique : Type
  ≔ (G H : Group) (hp : BlindImProjEpi G H)
    → BookIsEquiv (GroupHom G H) (BlindEpiMonoPullback G H) (blind_imfact G H hp)

{` lem:Im-fact-unique, proof: the inverse is composition ((Z,p),(Z',j),α) ↦ j ∘ ptoe(α) ∘ p. `}
def blind_epimono_compose (G H : Group) (t : BlindEpiMonoPullback G H) : GroupHom G H
  ≔ group_hom_compose G (t .snd .fst .fst) H
      (group_hom_compose G (t .fst .fst) (t .snd .fst .fst) (t .fst .snd .fst)
        (group_path_iso_equiv (t .fst .fst) (t .snd .fst .fst) .map (t .snd .snd) .fst))
      (t .snd .fst .snd .fst)

def blind_im_fact_inverse : Type
  ≔ (G H : Group) (hp : BlindImProjEpi G H)
    → Product ((f : GroupHom G H) → Id (GroupHom G H) (blind_epimono_compose G H (blind_imfact G H hp f)) f)
        ((t : BlindEpiMonoPullback G H) → Id (BlindEpiMonoPullback G H) (blind_imfact G H hp (blind_epimono_compose G H t)) t)

{` rem:n-im-ptd-map. Fact_*(f) ≔ Σ_{Y:U_*} Σ_{p:X→*Y} Σ_{i:Y→*Z} (f = i p). `}
def BlindPtdFact (X Z : Pointed) (f : BookPointedMap X Z) : Type
  ≔ Σ Pointed (Y ↦ Σ (BookPointedMap X Y) (p ↦ Σ (BookPointedMap Y Z) (i ↦
      Id (BookPointedMap X Z) f (book_pointed_compose X Y Z p i))))

{` Fact^n_* for n = k - 1 ≥ -1: n-connected p (‖fibers‖_n contractible, Trunc k) and n-truncated i
   (fibers of h-level n + 2 = k + 1). `}
def BlindPtdFactN (k : Nat) (X Z : Pointed) (f : BookPointedMap X Z) : Type
  ≔ Σ (BlindPtdFact X Z f) (c ↦
      Product (NConnectedMap k (X .carrier) (c .fst .carrier) (c .snd .fst .fst))
        (TruncatedMap (suc. k) (c .fst .carrier) (Z .carrier) (c .snd .snd .fst .fst)))

{` rem:n-im-ptd-map: Fact^n_* is contractible (n ≥ -1). `}
def blind_ptd_n_image_contractible : Type
  ≔ (k : Nat) (X Z : Pointed) (f : BookPointedMap X Z) → BookIsContr (BlindPtdFactN k X Z f)

{` rem:n-im-ptd-map, case n = -2: every map is (-2)-connected and the (-2)-truncated maps are equivalences. `}
def BlindPtdFactMinusTwo (X Z : Pointed) (f : BookPointedMap X Z) : Type
  ≔ Σ (BlindPtdFact X Z f) (c ↦
      Product (MinusTwoConnectedMap (X .carrier) (c .fst .carrier) (c .snd .fst .fst))
        (TruncatedMap zero. (c .fst .carrier) (Z .carrier) (c .snd .snd .fst .fst)))

def blind_ptd_minus_two_image_contractible : Type
  ≔ (X Z : Pointed) (f : BookPointedMap X Z) → BookIsContr (BlindPtdFactMinusTwo X Z f)

{` rem:n-im-ptd-map: x ↦ (f(x), |(x, refl)|_n) is n-connected and fst is n-truncated. `}
def blind_n_image_factor_props : Type
  ≔ (k : Nat) (A B : Type) (f : A → B)
    → Product (NConnectedMap k A (NImage k A B f) (n_image_factor k A B f))
        (TruncatedMap (suc. k) (NImage k A B f) B (n_image_include k A B f))

{` rem:n-im-ptd-map: for h : f = i p with p n-connected and i n-truncated, ‖f^{-1}(z)‖_n ≃ i^{-1}(z). `}
def blind_n_image_fiber_equiv : Type
  ≔ (k : Nat) (X Y Z : Type) (f : X → Z) (p : X → Y) (i : Y → Z) (h : Id (X → Z) f (x ↦ i (p x)))
    → NConnectedMap k X Y p → TruncatedMap (suc. k) Y Z i
    → (z : Z) → BookEquiv (Trunc k (BookFiber X Z f z)) (BookFiber Y Z i z)

{` rem:n-im-ptd-map: if X and Z are connected groupoids, so is Σ_{z:Z} ‖f^{-1}(z)‖_n. `}
def blind_n_image_connected_groupoid : Type
  ≔ (k : Nat) (X Z : Type) (f : X → Z)
    → Connected X → isGroupoid X → Connected Z → isGroupoid Z
    → Product (Connected (NImage k X Z f)) (isGroupoid (NImage k X Z f))

{` Helper: a pointed map out of a connected type lands in the component of the image of the point. `}
def blind_into_component (A : Type) (hA : Connected A) (a : A) (B : Type) (b : B) (k : A → B) (kp : Id B b (k a))
  : BookPointedMap (A, a) (NativeComponent B b, component_point B b)
  ≔ ((x ↦ (k x,
        mere_rec (Id A a x) (Mere (Id B b (k x))) (mere_isprop (Id B b (k x)))
          (p ↦ mere (Id B b (k x)) (concat B b (k a) (k x) kp (refl k p))) (hA .snd a x))),
     component_path B b (component_point B b)
       (k a, mere_rec (Id A a a) (Mere (Id B b (k a))) (mere_isprop (Id B b (k a)))
          (p ↦ mere (Id B b (k a)) (concat B b (k a) (k a) kp (refl k p))) (hA .snd a a))
       kp)

{` def:image. Img(f) ≔ Aut_{Σ_{z:BG'} coker(f)(z)}(sh_{G'}, |(sh_G, Bf_pt)|₀). `}
def BlindImage (G G' : Group) (f : GroupHom G G') : Group
  ≔ automorphism_group (ActionType G' (blind_coker G G' f)) (action_type_groupoid G' (blind_coker G G' f))
      (shape G', blind_coker_point G G' f)

{` def:image. B incl_{img(f)} ≔ fst : BImg(f) → BG'. `}
def blind_image_incl (G G' : Group) (f : GroupHom G G') : GroupHom (BlindImage G G' f) G'
  ≔ mkhom (BlindImage G G' f) G' ((u ↦ u .fst .fst), refl (shape G'))

def blind_image_incl_mono (G G' : Group) (f : GroupHom G G') : IsGroupMono (BlindImage G G' f) G' (blind_image_incl G G' f)
  ≔ stabilizer_inclusion_mono G' (blind_coker G G' f) (blind_coker_point G G' f)

{` def:image. B prj_{img(f)}(x) ≔ (Bf(x), |(x, refl)|₀) (in the component; pointed as for Bp(f)). `}
def blind_image_prj (G G' : Group) (f : GroupHom G G') : GroupHom G (BlindImage G G' f)
  ≔ mkhom G (BlindImage G G' f)
      (blind_into_component (BG G .carrier) (bg_connected G) (shape G)
        (ActionType G' (blind_coker G G' f)) (shape G', blind_coker_point G G' f)
        (zero_image_factor (BG G .carrier) (BG G' .carrier) (hom_function G G' f))
        (blind_zero_image_path (BG G .carrier) (BG G' .carrier) (hom_function G G' f) (shape G') (shape G) (hom_point G G' f)))

{` def:image. img : Hom(G,G') → Mono(G'), img(f) ≔ (Img(f), incl_{img(f)}, !). `}
def blind_img (G G' : Group) (f : GroupHom G G') : GroupMonos G'
  ≔ (BlindImage G G' f, (blind_image_incl G G' f, blind_image_incl_mono G G' f))

{` The proofs that prj_{img(f)} is an epimorphism, as a parameter. `}
def BlindImageEpiProofs : Type
  ≔ (G G' : Group) (f : GroupHom G G') → BlindIsEpi G (BlindImage G G' f) (blind_image_prj G G' f)

{` def:image. prjim : Hom(G,G') → Epi(G), prjim(f) ≔ (Img(f), prj_{img(f)}, !). `}
def blind_prjim (hp : BlindImageEpiProofs) (G G' : Group) (f : GroupHom G G') : BlindEpi G
  ≔ (BlindImage G G' f, (blind_image_prj G G' f, hp G G' f))

{` def:image. ∘^{-1}(f) ≔ ((Img(f), prj, !), (Img(f), incl, !), refl). `}
def blind_image_factorization (hp : BlindImageEpiProofs) (G G' : Group) (f : GroupHom G G') : BlindEpiMonoPullback G G'
  ≔ (blind_prjim hp G G' f, (blind_img G G' f, refl (BlindImage G G' f)))

{` def:image ("as before the image group is"): the two definitions of the image group agree. `}
def blind_image_defs_agree : Type
  ≔ (G G' : Group) (f : GroupHom G G') → Id Group (BlindImg G G' f) (BlindImage G G' f)

{` def:image: prj_{img(f)} is an epimorphism and incl ∘ prj = f. `}
def blind_image_prj_epi : Type ≔ BlindImageEpiProofs

def blind_image_factorizes : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Id (GroupHom G G') f (group_hom_compose G (BlindImage G G' f) G' (blind_image_prj G G' f) (blind_image_incl G G' f))

{` ex:charsurinj (1). f epi ⇔ USym f surjective ⇔ coker(f) contractible ⇔ incl_{img(f)} iso. `}
def blind_charsurinj_epi : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Product (BlindIff (BlindIsEpi G G' f) (Surjective (USym G) (USym G') (usym_hom G G' f)))
        (Product (BlindIff (BlindIsEpi G G' f) (BookIsContr (gset_underlying G' (blind_coker G G' f))))
                 (BlindIff (BlindIsEpi G G' f) (IsGroupIso (BlindImage G G' f) G' (blind_image_incl G G' f))))

{` ex:charsurinj (2). f mono ⇔ USym f injective ⇔ Ker(f) trivial ⇔ Bf covering ⇔ prj_{img(f)} iso. `}
def blind_charsurinj_mono : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Product (BlindIff (BlindIsMono G G' f) (IsEmbedding (USym G) (USym G') (usym_hom G G' f)))
        (Product (BlindIff (BlindIsMono G G' f) (IsTrivialGroup (BlindKer G G' f)))
          (Product (BlindIff (BlindIsMono G G' f) (IsCovering (BG G .carrier) (BG G' .carrier) (hom_function G G' f)))
                   (BlindIff (BlindIsMono G G' f) (IsGroupIso G (BlindImage G G' f) (blind_image_prj G G' f)))))

{` Lemma (subgroups.tex:1045): with g ≔ prj_{img(f2)} incl_{img(f1)} : Hom(Img(f1), Img(f2)),
   img(f2 f1) = (Img(g), incl_{img(f2)} incl_{img(g)}, !) in Mono(G2) and
   prjim(f2 f1) = (Img(g), prj_{img(g)} prj_{img(f1)}, !) in Epi(G0). `}
def blind_image_g (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (BlindImage G0 G1 f1) (BlindImage G1 G2 f2)
  ≔ group_hom_compose (BlindImage G0 G1 f1) G1 (BlindImage G1 G2 f2) (blind_image_incl G0 G1 f1) (blind_image_prj G1 G2 f2)

def blind_image_composite_mono : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let g ≔ blind_image_g G0 G1 G2 f1 f2 in
      let I ≔ BlindImage (BlindImage G0 G1 f1) (BlindImage G1 G2 f2) g in
      let j ≔ group_hom_compose I (BlindImage G1 G2 f2) G2
                (blind_image_incl (BlindImage G0 G1 f1) (BlindImage G1 G2 f2) g) (blind_image_incl G1 G2 f2) in
      Σ (IsGroupMono I G2 j) (m ↦ Id (GroupMonos G2) (blind_img G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (I, (j, m)))

def blind_image_composite_epi : Type
  ≔ (hp : BlindImageEpiProofs) (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let g ≔ blind_image_g G0 G1 G2 f1 f2 in
      let I ≔ BlindImage (BlindImage G0 G1 f1) (BlindImage G1 G2 f2) g in
      let q ≔ group_hom_compose G0 (BlindImage G0 G1 f1) I
                (blind_image_prj G0 G1 f1) (blind_image_prj (BlindImage G0 G1 f1) (BlindImage G1 G2 f2) g) in
      Σ (BlindIsEpi G0 I q) (e ↦ Id (BlindEpi G0) (blind_prjim hp G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (I, (q, e)))

{` lem:kerandcoker. ker(prj_{img(f)}) = ker(f) in Mono(G). `}
def blind_kerandcoker : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Id (GroupMonos G) (blind_ker G (BlindImage G G' f) (blind_image_prj G G' f)) (blind_ker G G' f)

{` xca (subgroups.tex:1160) (1). For (G, f, !) : Mono(G'), ua(prj_{img(f)}) : (G, f, !) = img(f) in Mono(G'). `}
def blind_mono_is_own_image : Type
  ≔ (G' : Group) (m : GroupMonos G')
    → Σ (IsGroupIso (m .fst) (BlindImage (m .fst) G' (m .snd .fst)) (blind_image_prj (m .fst) G' (m .snd .fst))) (hiso ↦
      Σ (Id (GroupMonos G') m (blind_img (m .fst) G' (m .snd .fst))) (e ↦
        Id (Id Group (m .fst) (BlindImage (m .fst) G' (m .snd .fst))) (e .fst)
          (group_path_from_iso (m .fst) (BlindImage (m .fst) G' (m .snd .fst))
            (blind_image_prj (m .fst) G' (m .snd .fst), hiso))))

{` xca (subgroups.tex:1160) (2). For (G', f, !) : Epi(G), ua(incl_{img(f)}) : (G', f, !) = prjim(f) in Epi(G)
   (the group component is the inverse of ua(incl), as incl goes Img(f) → G'). `}
def blind_epi_is_own_image : Type
  ≔ (hp : BlindImageEpiProofs) (G : Group) (e0 : BlindEpi G)
    → Σ (IsGroupIso (BlindImage G (e0 .fst) (e0 .snd .fst)) (e0 .fst) (blind_image_incl G (e0 .fst) (e0 .snd .fst))) (hiso ↦
      Σ (Id (BlindEpi G) e0 (blind_prjim hp G (e0 .fst) (e0 .snd .fst))) (e ↦
        Id (Id Group (e0 .fst) (BlindImage G (e0 .fst) (e0 .snd .fst))) (e .fst)
          (inverse Group (BlindImage G (e0 .fst) (e0 .snd .fst)) (e0 .fst)
            (group_path_from_iso (BlindImage G (e0 .fst) (e0 .snd .fst)) (e0 .fst)
              (blind_image_incl G (e0 .fst) (e0 .snd .fst), hiso)))))
