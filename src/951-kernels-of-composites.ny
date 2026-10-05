export "950-fibers-of-composites"
export "903-normal-subgroups"

{` Chapter 9 (subgroups.tex 486-560): cor:cokermaps, items 1-4 and 6
   (fig:kernelsofcomposites). Items 5 and 7 and the footnote lemmas of the
   proof are in module 952.

   Setting: f1 : Hom(G0, G1), f2 : Hom(G1, G2), f2 f1 = group_hom_compose
   G0 G1 G2 f1 f2 (its classifying map is judgmentally z ↦ Bf2(Bf1 z),
   pointed by f2(p1)p2). The kernels are the automorphism groups of the
   components of the fibers at the kernel shapes (def:kernel, module 901);
   all maps of fig:kernelsofcomposites are the maps of
   fig:fibersofcomposites (module 950) induced on components
   (ft:cmpnt:UUp->UUp). `}

{` ft:cmpnt:UUp->UUp. A map f : A → B with p : b = f(a) induces a map of
   components A_(a) → B_(b), pointed by (the component path over) p, hence
   a homomorphism Aut_A(a) → Aut_B(b). `}
def ch9w2_component_map (A B : Type) (f : A → B) (a : A) (b : B) (p : Id B b (f a)) (u : NativeComponent A a)
  : NativeComponent B b
  ≔ (f (u .fst), mere_rec (Id A a (u .fst)) (Mere (Id B b (f (u .fst)))) (mere_isprop (Id B b (f (u .fst))))
      (q ↦ mere (Id B b (f (u .fst))) (concat B b (f a) (f (u .fst)) p (refl f q))) (u .snd))

def ch9w2_component_map_point (A B : Type) (f : A → B) (a : A) (b : B) (p : Id B b (f a))
  : Id (NativeComponent B b) (component_point B b) (ch9w2_component_map A B f a b p (component_point A a))
  ≔ component_path B b (component_point B b) (ch9w2_component_map A B f a b p (component_point A a)) p

def ch9w2_aut_hom (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (f : A → B) (a : A) (b : B) (p : Id B b (f a))
  : GroupHom (automorphism_group A hA a) (automorphism_group B hB b)
  ≔ mkhom (automorphism_group A hA a) (automorphism_group B hB b)
      (ch9w2_component_map A B f a b p, ch9w2_component_map_point A B f a b p)

{` An equivalence induces an equivalence of components. `}
def ch9w2_component_equiv (A B : Type) (e : Equiv A B) (a : A)
  : Equiv (NativeComponent A a) (NativeComponent B (e .map a))
  ≔ let g ≔ equiv_inverse_map A B e in
    let inv : NativeComponent B (e .map a) → NativeComponent A a
      ≔ v ↦ (g (v .fst), mere_rec (Id B (e .map a) (v .fst)) (Mere (Id A a (g (v .fst)))) (mere_isprop (Id A a (g (v .fst))))
          (q ↦ mere (Id A a (g (v .fst))) (concat A a (g (e .map a)) (g (v .fst))
            (inverse A (g (e .map a)) a (equiv_retraction A B e a)) (refl g q))) (v .snd)) in
    let fwd ≔ ch9w2_component_map A B (e .map) a (e .map a) (refl (e .map a)) in
    quasi_inverse_equiv (NativeComponent A a) (NativeComponent B (e .map a)) fwd inv
      (u ↦ component_path A a (inv (fwd u)) u (equiv_retraction A B e (u .fst)))
      (v ↦ component_path B (e .map a) (fwd (inv v)) v (equiv_counit A B e (v .fst)))

{` Components of a subtype by a family of propositions. `}
def ch9w2_subtype_component_map (A : Type) (P : A → Type) (a : A) (p : P a)
  (u : NativeComponent (Σ A P) (a, p)) : NativeComponent A a
  ≔ (u .fst .fst, mere_rec (Id (Σ A P) (a, p) (u .fst)) (Mere (Id A a (u .fst .fst))) (mere_isprop (Id A a (u .fst .fst)))
      (q ↦ mere (Id A a (u .fst .fst)) (q .fst)) (u .snd))

def ch9w2_subtype_component_equiv (A : Type) (P : A → Type) (hP : (x : A) → isProp (P x)) (a : A) (p : P a)
  : Equiv (NativeComponent (Σ A P) (a, p)) (NativeComponent A a)
  ≔ let inv : NativeComponent A a → NativeComponent (Σ A P) (a, p)
      ≔ v ↦
        let px : P (v .fst) ≔ mere_rec (Id A a (v .fst)) (P (v .fst)) (hP (v .fst)) (q ↦ transport A P a (v .fst) q p) (v .snd) in
        ((v .fst, px),
         mere_rec (Id A a (v .fst)) (Mere (Id (Σ A P) (a, p) (v .fst, px))) (mere_isprop (Id (Σ A P) (a, p) (v .fst, px)))
           (q ↦ mere (Id (Σ A P) (a, p) (v .fst, px)) (subtype_equal A P hP (a, p) (v .fst, px) q)) (v .snd)) in
    quasi_inverse_equiv (NativeComponent (Σ A P) (a, p)) (NativeComponent A a)
      (ch9w2_subtype_component_map A P a p) inv
      (u ↦ component_path (Σ A P) (a, p) (inv (ch9w2_subtype_component_map A P a p u)) u
        (subtype_equal A P hP (inv (ch9w2_subtype_component_map A P a p u) .fst) (u .fst) (refl (u .fst .fst))))
      (v ↦ component_path A a (ch9w2_subtype_component_map A P a p (inv v)) v (refl (v .fst)))

{` The fiber of an induced map of components over v is the subtype of the
   fiber of f over v.1 cut out by "lies in the component of a". `}
def ch9w2_component_fiber_equiv (A B : Type) (f : A → B) (a : A) (b : B) (p : Id B b (f a)) (v : NativeComponent B b)
  : Equiv (BookFiber (NativeComponent A a) (NativeComponent B b) (ch9w2_component_map A B f a b p) v)
      (Σ (BookFiber A B f (v .fst)) (w ↦ Mere (Id A a (w .fst))))
  ≔ let cm ≔ ch9w2_component_map A B f a b p in
    let C ≔ NativeComponent B b in
    quasi_inverse_equiv (BookFiber (NativeComponent A a) C cm v) (Σ (BookFiber A B f (v .fst)) (w ↦ Mere (Id A a (w .fst))))
      (t ↦ ((t .fst .fst, t .snd .fst), t .fst .snd))
      (s ↦ ((s .fst .fst, s .snd), component_path B b v (cm (s .fst .fst, s .snd)) (s .fst .snd)))
      (t ↦ (refl (t .fst),
            equivalence_injective (Id C v (cm (t .fst))) (Id B (v .fst) (cm (t .fst) .fst))
              (component_path_equiv B b v (cm (t .fst)))
              (component_path B b v (cm (t .fst)) (t .snd .fst)) (t .snd) (refl (t .snd .fst))))
      (s ↦ refl s)

{` If f is an embedding, the induced map of components is an equivalence. `}
def ch9w2_component_map_embedding_equiv (A B : Type) (f : A → B) (a : A) (b : B) (p : Id B b (f a))
  (hf : IsEmbedding A B f)
  : BookIsEquiv (NativeComponent A a) (NativeComponent B b) (ch9w2_component_map A B f a b p)
  ≔ v ↦
    let F ≔ BookFiber (NativeComponent A a) (NativeComponent B b) (ch9w2_component_map A B f a b p) v in
    let S ≔ Σ (BookFiber A B f (v .fst)) (w ↦ Mere (Id A a (w .fst))) in
    let e ≔ ch9w2_component_fiber_equiv A B f a b p v in
    let hS : isProp S ≔ sigma_prop (BookFiber A B f (v .fst)) (w ↦ Mere (Id A a (w .fst))) (hf (v .fst))
      (w ↦ mere_isprop (Id A a (w .fst))) in
    let hF : isProp F ≔ x y ↦ equivalence_injective F S e x y (hS (e .map x) (e .map y)) in
    let s : S ≔ mere_rec (Id B b (v .fst)) S hS
      (q ↦ ((a, concat B (v .fst) b (f a) (inverse B b (v .fst) q) p), mere (Id A a a) (refl a))) (v .snd) in
    let c : F ≔ equiv_inverse_map F S e s in
    (c, y ↦ hF c y)

{` The kernel triangle of cor:cokermaps. `}
def kc_compose (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : GroupHom G0 G2
  ≔ group_hom_compose G0 G1 G2 f1 f2

{` The pointing path (p1, pathpair(p1, refl)) of F1. `}
def kc_F1_point (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (HomFiber G1 G2 f2 (shape G2)) (kernel_shape G1 G2 f2)
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2)
        (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)))
  ≔ (hom_point G0 G1 f1,
     fibcomp_pathover (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2)
       (shape G1) (shape G2) (hom_point G1 G2 f2) (shape G0) (hom_point G0 G1 f1))

{` cor:cokermaps (2): F1 : Hom(Ker(f2 f1), Ker(f2)). `}
def kc_F1 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2)
  ≔ ch9w2_aut_hom (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (HomFiber G1 G2 f2 (shape G2))
      (hom_fiber_groupoid G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (hom_fiber_groupoid G1 G2 f2 (shape G2))
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2))
      (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_shape G1 G2 f2) (kc_F1_point G0 G1 G2 f1 f2)

{` cor:cokermaps (3): F2 : Hom(Ker(f1), Ker(f2 f1)), pointed by refl
   (F2(sh_G0, p1) ≡ (sh_G0, f2(p1)p2) is the kernel shape of f2 f1). `}
def kc_F2 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2))
  ≔ ch9w2_aut_hom (HomFiber G0 G1 f1 (shape G1)) (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))
      (hom_fiber_groupoid G0 G1 f1 (shape G1)) (hom_fiber_groupoid G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))
      (fibcomp_F2 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2)
        (shape G1) (shape G2) (hom_point G1 G2 f2))
      (kernel_shape G0 G1 f1) (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2))
      (refl (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)))

{` The lower square of fig:kernelsofcomposites: f1 ∘ ker(f2 f1) = ker(f2) ∘ F1. `}
def kc_lower_square (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G1)
      (group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0 G1
        (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
      (group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) G1
        (kc_F1 G0 G1 G2 f1 f2) (kernel_inclusion G1 G2 f2))
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let X1 ≔ BG G1 .carrier in let x1 ≔ shape G1 in
    let y ≔ hom_function G0 G1 f1 (shape G0) in
    let p1 ≔ hom_point G0 G1 f1 in
    ch9_hom_path K G1
      (group_hom_compose K G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
      (group_hom_compose K (kernel_group G1 G2 f2) G1 (kc_F1 G0 G1 G2 f1 f2) (kernel_inclusion G1 G2 f2))
      ((u ↦ refl (hom_function G0 G1 f1 (u .fst .fst))),
       calc
         concat X1 x1 y y (concat X1 x1 y y p1 (refl y)) (refl y)
         = concat X1 x1 y y p1 (refl y) by concat_p1 X1 x1 y (concat X1 x1 y y p1 (refl y))
         = p1 by concat_p1 X1 x1 y p1
         = concat X1 x1 x1 y (refl x1) p1 by inverse (Id X1 x1 y) (concat X1 x1 x1 y (refl x1) p1) p1 (concat_1p X1 x1 y p1) ∎)

{` cor:cokermaps (2), uniqueness: F1 is the unique homomorphism with
   f1 ∘ ker(f2 f1) = ker(f2) ∘ F1 (ker(f2) is a monomorphism). `}
def kc_F1_unique (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : BookIsContr (BookFiber (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2))
      (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G1)
      (k ↦ group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) G1 k (kernel_inclusion G1 G2 f2))
      (group_hom_compose (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1))
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let m ≔ usym_injective_group_mono (kernel_group G1 G2 f2) G1 (kernel_inclusion G1 G2 f2) (kernel_inclusion_mono G1 G2 f2) in
    ((kc_F1 G0 G1 G2 f1 f2, kc_lower_square G0 G1 G2 f1 f2),
     y ↦ m K (group_hom_compose K G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
       (kc_F1 G0 G1 G2 f1 f2, kc_lower_square G0 G1 G2 f1 f2) y)

{` The upper-right triangle: ker(f1) = ker(f2 f1) ∘ F2. `}
def kc_upper_right (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G1 f1) G0) (kernel_inclusion G0 G1 f1)
      (group_hom_compose (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0
        (kc_F2 G0 G1 G2 f1 f2) (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)))
  ≔ let X0 ≔ BG G0 .carrier in let x0 ≔ shape G0 in
    ch9_hom_path (kernel_group G0 G1 f1) G0 (kernel_inclusion G0 G1 f1)
      (group_hom_compose (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0
        (kc_F2 G0 G1 G2 f1 f2) (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      ((u ↦ refl (u .fst .fst)), refl (concat X0 x0 x0 x0 (refl x0) (refl x0)))

{` cor:cokermaps (3): F2 is a monomorphism (ker(f2 f1) ∘ F2 = ker(f1) is
   one, xca:mono1st-epi2nd) and the unique homomorphism with
   ker(f1) = ker(f2 f1) ∘ F2. `}
def kc_F2_monomorphism (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : IsGroupMonomorphism (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kc_F2 G0 G1 G2 f1 f2)
  ≔ let K1 ≔ kernel_group G0 G1 f1 in let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    group_monomorphism_cancel K1 K G0 (kc_F2 G0 G1 G2 f1 f2) (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2))
      (transport (GroupHom K1 G0) (IsGroupMonomorphism K1 G0) (kernel_inclusion G0 G1 f1)
        (group_hom_compose K1 K G0 (kc_F2 G0 G1 G2 f1 f2) (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)))
        (kc_upper_right G0 G1 G2 f1 f2)
        (usym_injective_group_mono K1 G0 (kernel_inclusion G0 G1 f1) (kernel_inclusion_mono G0 G1 f1)))

def kc_F2_mono (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : IsGroupMono (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kc_F2 G0 G1 G2 f1 f2)
  ≔ group_mono_usym_injective (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kc_F2 G0 G1 G2 f1 f2)
      (kc_F2_monomorphism G0 G1 G2 f1 f2)

def kc_F2_unique (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : BookIsContr (BookFiber (GroupHom (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (GroupHom (kernel_group G0 G1 f1) G0)
      (k ↦ group_hom_compose (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) G0 k
        (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (kernel_inclusion G0 G1 f1))
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let m ≔ usym_injective_group_mono K G0 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2))
      (kernel_inclusion_mono G0 G2 (kc_compose G0 G1 G2 f1 f2)) in
    ((kc_F2 G0 G1 G2 f1 f2, kc_upper_right G0 G1 G2 f1 f2),
     y ↦ m (kernel_group G0 G1 f1) (kernel_inclusion G0 G1 f1) (kc_F2 G0 G1 G2 f1 f2, kc_upper_right G0 G1 G2 f1 f2) y)

{` cor:cokermaps (1). The fiber of BF1 at the shape of Ker(f2): H ∘ strip,
   strip((c, !), e) ≔ (c, e.1) : F1⁻¹(x1, p2). `}
def kc_D (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : Type
  ≔ HomFiber (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2)
      (shape (kernel_group G1 G2 f2))

def kc_H_fun (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (w : kc_D G0 G1 G2 f1 f2)
  : HomFiber G0 G1 f1 (shape G1)
  ≔ fibcomp_H (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2)
      (shape G1) (shape G2) (hom_point G1 G2 f2) (w .fst .fst, w .snd .fst)

{` H, pointed by reflexivity, induces Ker(F1) → Ker(f1). `}
def kc_H (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
      (kernel_group G0 G1 f1)
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in let K2 ≔ kernel_group G1 G2 f2 in
    ch9w2_aut_hom (kc_D G0 G1 G2 f1 f2) (HomFiber G0 G1 f1 (shape G1))
      (hom_fiber_groupoid K K2 (kc_F1 G0 G1 G2 f1 f2) (shape K2)) (hom_fiber_groupoid G0 G1 f1 (shape G1))
      (kc_H_fun G0 G1 G2 f1 f2) (kernel_shape K K2 (kc_F1 G0 G1 G2 f1 f2)) (kernel_shape G0 G1 f1)
      (refl (kernel_shape G0 G1 f1))

{` The underlying function of BH, as an equivalence: the fiber of BF1 is
   the subtype of F1⁻¹(x1,p2) of elements in the component of the kernel
   shape (ch9w2_component_fiber_equiv), components of a subtype are
   components (ch9w2_subtype_component_equiv), and H is an equivalence. `}
def kc_H_equiv (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Equiv (BG (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2)) .carrier)
      (BG (kernel_group G0 G1 f1) .carrier)
  ≔ let X0 ≔ BG G0 .carrier in let X1 ≔ BG G1 .carrier in let X2 ≔ BG G2 .carrier in
    let Bf1 ≔ hom_function G0 G1 f1 in let Bf2 ≔ hom_function G1 G2 f2 in
    let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in let K2 ≔ kernel_group G1 G2 f2 in
    let T ≔ HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2) in
    let t0 ≔ kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let S ≔ HomFiber G1 G2 f2 (shape G2) in let s0 ≔ kernel_shape G1 G2 f2 in
    let D ≔ kc_D G0 G1 G2 f1 f2 in
    let ks ≔ kernel_shape K K2 (kc_F1 G0 G1 G2 f1 f2) in
    let FF ≔ FibcompF1Fiber X0 X1 X2 Bf1 Bf2 (shape G1) (shape G2) (hom_point G1 G2 f2) in
    let P : FF → Type ≔ w ↦ Mere (Id T t0 (w .fst)) in
    let L ≔ ch9w2_component_fiber_equiv T S
      (fibcomp_F1 X0 X1 X2 Bf1 Bf2 (shape G2)) t0 s0 (kc_F1_point G0 G1 G2 f1 f2) (component_point S s0) in
    let Lks ≔ L .map ks in
    compose_equiv (NativeComponent D ks) (NativeComponent (Σ FF P) Lks) (NativeComponent (HomFiber G0 G1 f1 (shape G1)) (kernel_shape G0 G1 f1))
      (ch9w2_component_equiv D (Σ FF P) L ks)
      (compose_equiv (NativeComponent (Σ FF P) Lks) (NativeComponent FF (Lks .fst))
        (NativeComponent (HomFiber G0 G1 f1 (shape G1)) (kernel_shape G0 G1 f1))
        (ch9w2_subtype_component_equiv FF P (w ↦ mere_isprop (Id T t0 (w .fst))) (Lks .fst) (Lks .snd))
        (ch9w2_component_equiv FF (HomFiber G0 G1 f1 (shape G1))
          (fibcomp_H_equiv X0 X1 X2 Bf1 Bf2 (shape G1) (shape G2) (hom_point G1 G2 f2)) (Lks .fst)))

{` cor:cokermaps (1): H is an isomorphism Ker(F1) ≅ Ker(f1). `}
def kc_H_iso (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : IsGroupIso (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
      (kernel_group G0 G1 f1) (kc_H G0 G1 G2 f1 f2)
  ≔ let KF ≔ kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2) in
    let K1 ≔ kernel_group G0 G1 f1 in
    let e ≔ kc_H_equiv G0 G1 G2 f1 f2 in
    book_equivalence (BG KF .carrier) (BG K1 .carrier)
      (equiv_change_map (BG KF .carrier) (BG K1 .carrier) e (hom_function KF K1 (kc_H G0 G1 G2 f1 f2))
        (u ↦ component_path (HomFiber G0 G1 f1 (shape G1)) (kernel_shape G0 G1 f1) (e .map u)
          (hom_function KF K1 (kc_H G0 G1 G2 f1 f2) u) (refl (e .map u .fst)))) .equiv

def kc_H_group_iso (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupIso (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
      (kernel_group G0 G1 f1)
  ≔ (kc_H G0 G1 G2 f1 f2, kc_H_iso G0 G1 G2 f1 f2)

{` Pointed homotopies between pointed maps into a component are pointed
   homotopies of the first components. `}
def ch9w2_component_homotopy (X : Pointed) (A : Type) (a : A)
  (f g : BookPointedMap X (NativeComponent A a, component_point A a))
  (h : (x : X .carrier) → Id A (f .fst x .fst) (g .fst x .fst))
  (c : Id (Id A a (g .fst (X .point) .fst))
        (concat A a (f .fst (X .point) .fst) (g .fst (X .point) .fst) (refl ((u ↦ u .fst) : NativeComponent A a → A) (f .snd))
          (h (X .point)))
        (refl ((u ↦ u .fst) : NativeComponent A a → A) (g .snd)))
  : PointedHomotopy X (NativeComponent A a, component_point A a) f g
  ≔ let C ≔ NativeComponent A a in let pt ≔ X .point in
    let fst : C → A ≔ u ↦ u .fst in
    let k ≔ component_path A a (f .fst pt) (g .fst pt) (h pt) in
    ((x ↦ component_path A a (f .fst x) (g .fst x) (h x)),
     equivalence_injective (Id C (component_point A a) (g .fst pt)) (Id A a (g .fst pt .fst))
       (component_path_equiv A a (component_point A a) (g .fst pt))
       (concat C (component_point A a) (f .fst pt) (g .fst pt) (f .snd) k) (g .snd)
       (concat (Id A a (g .fst pt .fst))
          (refl fst (concat C (component_point A a) (f .fst pt) (g .fst pt) (f .snd) k))
          (concat A a (f .fst pt .fst) (g .fst pt .fst) (refl fst (f .snd)) (h pt))
          (refl fst (g .snd))
          (map_path_concat C A fst (component_point A a) (f .fst pt) (g .fst pt) (f .snd) k)
          c))

{` The upper-left triangle of fig:kernelsofcomposites: F2 ∘ H = ker(F1). `}
def kc_upper_left (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
        (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (group_hom_compose (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
        (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kc_H G0 G1 G2 f1 f2) (kc_F2 G0 G1 G2 f1 f2))
      (kernel_inclusion (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2))
  ≔ let X0 ≔ BG G0 .carrier in let X1 ≔ BG G1 .carrier in let X2 ≔ BG G2 .carrier in
    let Bf1 ≔ hom_function G0 G1 f1 in let Bf2 ≔ hom_function G1 G2 f2 in
    let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in let K2 ≔ kernel_group G1 G2 f2 in
    let K1 ≔ kernel_group G0 G1 f1 in
    let KF ≔ kernel_group K K2 (kc_F1 G0 G1 G2 f1 f2) in
    let T ≔ HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2) in
    let t0 ≔ kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let C ≔ NativeComponent T t0 in
    let fst : C → T ≔ u ↦ u .fst in
    let comp ≔ group_hom_compose KF K1 K (kc_H G0 G1 G2 f1 f2) (kc_F2 G0 G1 G2 f1 f2) in
    let ki ≔ kernel_inclusion K K2 (kc_F1 G0 G1 G2 f1 f2) in
    let ks ≔ shape KF in
    let tri ≔ fibcomp_triangle_point X0 X1 X2 Bf1 Bf2 (shape G1) (shape G2) (hom_point G1 G2 f2) in
    let F2snd ≔ hom_point K1 K (kc_F2 G0 G1 G2 f1 f2) in
    let Hsnd ≔ hom_point KF K1 (kc_H G0 G1 G2 f1 f2) in
    let BF2 ≔ hom_function K1 K (kc_F2 G0 G1 G2 f1 f2) in
    let c0 ≔ shape K in let c1 ≔ BF2 (shape K1) in let c2 ≔ BF2 (hom_function KF K1 (kc_H G0 G1 G2 f1 f2) ks) in
    ch9_hom_path KF K comp ki
      (ch9w2_component_homotopy (BG KF) T t0 (hom_B KF K comp) (hom_B KF K ki)
        (u ↦ tri (u .fst .fst .fst, u .fst .snd .fst))
        (calc
          concat T t0 t0 t0 (refl fst (concat C c0 c1 c2 F2snd (refl BF2 Hsnd))) (tri (ks .fst .fst .fst, ks .fst .snd .fst))
          = concat T t0 t0 t0 (concat T t0 t0 t0 (refl fst F2snd) (refl fst (refl BF2 Hsnd))) (tri (ks .fst .fst .fst, ks .fst .snd .fst))
            by refl ((r ↦ concat T t0 t0 t0 r (tri (ks .fst .fst .fst, ks .fst .snd .fst))) : Id T t0 t0 → Id T t0 t0)
                 (map_path_concat C T fst c0 c1 c2 F2snd (refl BF2 Hsnd))
          = concat T t0 t0 t0 (concat T t0 t0 t0 (refl t0) (refl t0)) (refl t0)
            by refl (concat T t0 t0 t0 (concat T t0 t0 t0 (refl t0) (refl t0)))
                 (fibcomp_triangle_point_base X0 X1 X2 Bf1 Bf2 (shape G0) (shape G1) (shape G2) (hom_point G0 G1 f1) (hom_point G1 G2 f2))
          = concat T t0 t0 t0 (refl t0) (refl t0) by concat_p1 T t0 t0 (concat T t0 t0 t0 (refl t0) (refl t0))
          = refl t0 by concat_1p T t0 t0 (refl t0) ∎))

{` Two monomorphisms related by an isomorphism of their domains are equal
   in Mono(L) (as module 803, sdp_group_monos_path_from_iso). `}
def ch9w2_monos_path_base (L K : Group) (i : GroupHom K L) (m : IsGroupMono K L i)
  (i' : GroupHom K L) (m' : IsGroupMono K L i')
  (c : Id (GroupHom K L) (group_hom_compose K K L (group_hom_id K) i') i)
  : Id (GroupMonos L) (K, (i, m)) (K, (i', m'))
  ≔ (refl K,
     subtype_equal (GroupHom K L) (IsGroupMono K L) (is_group_mono_prop K L) (i, m) (i', m')
       (concat (GroupHom K L) i (group_hom_compose K K L (group_hom_id K) i') i'
         (inverse (GroupHom K L) (group_hom_compose K K L (group_hom_id K) i') i c)
         (group_hom_id_compose K L i')))

def ch9w2_monos_path_motive (L K : Group) (i : GroupHom K L) (m : IsGroupMono K L i)
  (u : Σ Group (K' ↦ GroupIso K K')) : Type
  ≔ (i' : GroupHom (u .fst) L) (m' : IsGroupMono (u .fst) L i')
      → Id (GroupHom K L) (group_hom_compose K (u .fst) L (u .snd .fst) i') i
      → Id (GroupMonos L) (K, (i, m)) (u .fst, (i', m'))

def ch9w2_monos_path_from_iso (L K K' : Group) (e : GroupIso K K') (i : GroupHom K L) (m : IsGroupMono K L i)
  (i' : GroupHom K' L) (m' : IsGroupMono K' L i')
  (c : Id (GroupHom K L) (group_hom_compose K K' L (e .fst) i') i)
  : Id (GroupMonos L) (K, (i, m)) (K', (i', m'))
  ≔ transport (Σ Group (K' ↦ GroupIso K K')) (ch9w2_monos_path_motive L K i m) (K, group_iso_id K) (K', e)
      (contractible_prop (Σ Group (K' ↦ GroupIso K K')) (group_iso_total_contractible K)
        (K, group_iso_id K) (K', e))
      (i' m' c ↦ ch9w2_monos_path_base L K i m i' m' c) i' m' c

{` cor:cokermaps (4): (Ker(f1), F2) = (Ker(F1), ker(F1)) in Mono(Ker(f2 f1)). `}
def kc_monos_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupMonos (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (kernel_group G0 G1 f1, (kc_F2 G0 G1 G2 f1 f2, kc_F2_mono G0 G1 G2 f1 f2))
      (kernel_group (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2),
       (kernel_inclusion (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2),
        kernel_inclusion_mono (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2) (kc_F1 G0 G1 G2 f1 f2)))
  ≔ let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in let K2 ≔ kernel_group G1 G2 f2 in
    let K1 ≔ kernel_group G0 G1 f1 in let KF ≔ kernel_group K K2 (kc_F1 G0 G1 G2 f1 f2) in
    inverse (GroupMonos K)
      (KF, (kernel_inclusion K K2 (kc_F1 G0 G1 G2 f1 f2), kernel_inclusion_mono K K2 (kc_F1 G0 G1 G2 f1 f2)))
      (K1, (kc_F2 G0 G1 G2 f1 f2, kc_F2_mono G0 G1 G2 f1 f2))
      (ch9w2_monos_path_from_iso K KF K1 (kc_H_group_iso G0 G1 G2 f1 f2)
        (kernel_inclusion K K2 (kc_F1 G0 G1 G2 f1 f2)) (kernel_inclusion_mono K K2 (kc_F1 G0 G1 G2 f1 f2))
        (kc_F2 G0 G1 G2 f1 f2) (kc_F2_mono G0 G1 G2 f1 f2) (kc_upper_left G0 G1 G2 f1 f2))

{` cor:cokermaps (6): if f2 is a monomorphism, F2 is an isomorphism. Bf2
   is then injective on paths (usym_injective_ap_embedding), so F2 is an
   embedding (fiberwise: p ↦ f2(p)p2), and the induced map of components
   of an embedding is an equivalence. `}
def kc_F2_embedding (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (m : IsGroupMono G1 G2 f2)
  : IsEmbedding (HomFiber G0 G1 f1 (shape G1)) (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))
      (fibcomp_F2 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2)
        (shape G1) (shape G2) (hom_point G1 G2 f2))
  ≔ let X0 ≔ BG G0 .carrier in let X1 ≔ BG G1 .carrier in let X2 ≔ BG G2 .carrier in
    let Bf1 ≔ hom_function G0 G1 f1 in let Bf2 ≔ hom_function G1 G2 f2 in
    let x1 ≔ shape G1 in let x2 ≔ shape G2 in let p2 ≔ hom_point G1 G2 f2 in
    let P : X0 → Type ≔ x ↦ Id X1 x1 (Bf1 x) in
    let Q : X0 → Type ≔ x ↦ Id X2 x2 (Bf2 (Bf1 x)) in
    let k : (x : X0) → P x → Q x ≔ x p ↦ concat X2 x2 (Bf2 x1) (Bf2 (Bf1 x)) p2 (map_path X1 X2 Bf2 x1 (Bf1 x) p) in
    let emb : (x : X0) → IsEmbedding (P x) (Q x) (k x)
      ≔ x ↦ path_reflecting_set_embedding (P x) (Q x) (bg_groupoid G2 x2 (Bf2 (Bf1 x))) (k x)
          (q q' s ↦ embedding_reflects_paths (P x) (Id X2 (Bf2 x1) (Bf2 (Bf1 x))) (map_path X1 X2 Bf2 x1 (Bf1 x))
            (usym_injective_ap_embedding G1 G2 f2 m x1 (Bf1 x)) q q'
            (concat_cancel_left X2 x2 (Bf2 x1) (Bf2 (Bf1 x)) p2 (map_path X1 X2 Bf2 x1 (Bf1 x) q) (map_path X1 X2 Bf2 x1 (Bf1 x) q') s)) in
    let tm ≔ fiberwise_truncated_total (suc. zero.) X0 P Q k
      (x w ↦ prop_to_hlevel_one (BookFiber (P x) (Q x) (k x) w) (emb x w)) in
    w ↦ hlevel_one_to_prop (BookFiber (Σ X0 P) (Σ X0 Q) (totalize X0 P Q k) w) (tm w)

def kc_F2_iso_of_mono (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (m : IsGroupMonomorphism G1 G2 f2)
  : IsGroupIso (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kc_F2 G0 G1 G2 f1 f2)
  ≔ ch9w2_component_map_embedding_equiv (HomFiber G0 G1 f1 (shape G1)) (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2))
      (fibcomp_F2 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2)
        (shape G1) (shape G2) (hom_point G1 G2 f2))
      (kernel_shape G0 G1 f1) (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2))
      (refl (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (kc_F2_embedding G0 G1 G2 f1 f2 (group_mono_usym_injective G1 G2 f2 m))
