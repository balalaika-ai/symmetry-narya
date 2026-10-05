export "1331-pointed-map-identifications"
export "604-wild-pointed-types"

{` Chapter 13 (fields.tex 383-424): the wild functor O A ≔ (S¹ →* A).
   The circle is an arbitrary CircleSignature C (circle_pointed C = (S¹, base)).

   Narya deviation: the pointed composite f ∘ cst of def:pointedtypes
   (book_pointed_compose) is pointed by concat f_pt (ap_f refl) ≡
   concat f_pt refl, which is not judgmentally f_pt. So O(pt_{OA}) is
   cst_*(f(pt_A), f_pt·refl) and the path (f_pt, ρ_{f_pt}) in
   Σ (x : B) (pt_B = x) of the book ends at (f(pt_A), concat f_pt refl);
   its second component is defined by path induction on f_pt (as the book's
   ρ_{f_pt}), with value ρ'⁻¹ = (concat_p1 refl)⁻¹ at refl. `}

{` def:O-functor: O A ≔ (S¹ →* A), pointed at the constant map. `}
def circle_pointed_maps (C : CircleSignature) (A : Pointed) : Pointed
  ≔ (BookPointedMap (circle_pointed C) A, book_pointed_constant (circle_pointed C) A)

def o_point_pathover (B : Type) (b y : B) (v : Id B b y)
  : Id ((x ↦ Id B b x) : B → Type) v (refl b) (concat B b y y v (refl y))
  ≔ J B b (y v ↦ Id ((x ↦ Id B b x) : B → Type) v (refl b) (concat B b y y v (refl y)))
      (inverse (Id B b b) (concat B b b b (refl b) (refl b)) (refl b) (concat_p1 B b b (refl b))) y v

{` The path (f_pt, ρ_{f_pt}) in the contractible type Σ (x : B) (pt_B = x). `}
def o_point_path (B : Type) (b y : B) (v : Id B b y)
  : Id (Σ B (x ↦ Id B b x)) (b, refl b) (y, concat B b y y v (refl y))
  ≔ (v, o_point_pathover B b y v)

{` def:O-functor: O(f) ≔ (g ↦ f ∘ g) pointed by O(f)_pt ≔ ap_{cst_*}(f_pt, ρ_{f_pt}). `}
def o_functor_map (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B)
  ≔ ((g ↦ book_pointed_compose (circle_pointed C) A B g f),
     refl (pointed_constant_at (circle_pointed C) B) (o_point_path (B .carrier) (B .point) (f .fst (A .point)) (f .snd)))

{` Any two paths between pointed constant maps that are images of cst_* of
   paths in the contractible Σ (x : B) (pt_B = x) agree. `}
def o_constant_paths_agree (C : CircleSignature) (B : Pointed) (y : B .carrier) (p : Id (B .carrier) (B .point) y)
  (u u' : Id (Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x)) (B .point, refl (B .point)) (y, p))
  : Id (Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
        (pointed_constant_at (circle_pointed C) B (y, p)))
      (refl (pointed_constant_at (circle_pointed C) B) u) (refl (pointed_constant_at (circle_pointed C) B) u')
  ≔ let Σb ≔ Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x) in
    refl ((w ↦ refl (pointed_constant_at (circle_pointed C) B) w)
        : Id Σb (B .point, refl (B .point)) (y, p)
          → Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
              (pointed_constant_at (circle_pointed C) B (y, p)))
      (prop_is_set Σb (contractible_prop Σb (iscontr_idfrom (B .carrier) (B .point)))
        (B .point, refl (B .point)) (y, p) u u')

{` Paths of pointed constant maps with refl first component are images of cst_*. `}
def o_constant_refl_path (C : CircleSignature) (B : Pointed) (y : B .carrier) (p q : Id (B .carrier) (B .point) y)
  (θ : Id (Id (B .carrier) (B .point) y) p q)
  : Id (Id (BookPointedMap (circle_pointed C) B) (pointed_constant_at (circle_pointed C) B (y, p))
        (pointed_constant_at (circle_pointed C) B (y, q)))
      (refl (constant (C .carrier) (B .carrier) y), θ)
      (refl (pointed_constant_at (circle_pointed C) B) ((refl y, θ)
        : Id (Σ (B .carrier) (x ↦ Id (B .carrier) (B .point) x)) (y, p) (y, q)))
  ≔ refl (refl (constant (C .carrier) (B .carrier) y), θ)

{` xca:O-functor, identity law: O(id_A) = id_{O A} as pointed maps. `}
def o_functor_map_id (C : CircleSignature) (A : Pointed)
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C A))
      (o_functor_map C A A (book_pointed_identity A)) (book_pointed_identity (circle_pointed_maps C A))
  ≔ let S ≔ circle_pointed C in let X ≔ A .carrier in let a ≔ A .point in
    let OA ≔ circle_pointed_maps C A in
    let M ≔ BookPointedMap S A in
    let Σa ≔ Σ X (x ↦ Id X a x) in
    let F ≔ pointed_constant_at S A in
    let cst ≔ book_pointed_constant S A in
    let raa ≔ concat X a a a (refl a) (refl a) in
    let u ≔ o_point_path X a a (refl a) in
    let u' ≔ (refl a, concat_1p X a a (refl a)) : Id Σa (a, raa) (a, refl a) in
    let kpt : Id (Id M cst cst) (concat M cst (F (a, raa)) cst (refl F u) (pointed_wild_lu S A cst)) (refl cst)
      ≔ calc
          concat M cst (F (a, raa)) cst (refl F u) (pointed_wild_lu S A cst)
            = concat M cst (F (a, raa)) cst (refl F u) (refl F u')
            by refl (concat M cst (F (a, raa)) cst (refl F u)) (o_constant_refl_path C A a raa (refl a) (concat_1p X a a (refl a)))
          = refl F (concat Σa (a, refl a) (a, raa) (a, refl a) u u')
            by inverse (Id M cst cst) (refl F (concat Σa (a, refl a) (a, raa) (a, refl a) u u'))
              (concat M cst (F (a, raa)) cst (refl F u) (refl F u'))
              (map_path_concat Σa M F (a, refl a) (a, raa) (a, refl a) u u')
          = refl F (refl ((a, refl a) : Σa))
            by o_constant_paths_agree C A a (refl a) (concat Σa (a, refl a) (a, raa) (a, refl a) u u') (refl ((a, refl a) : Σa)) ∎ in
    equiv_inverse_map (Id (BookPointedMap OA OA) (o_functor_map C A A (book_pointed_identity A)) (book_pointed_identity OA))
      (PointedHomotopy OA OA (o_functor_map C A A (book_pointed_identity A)) (book_pointed_identity OA))
      (pointed_map_path_equiv OA OA (o_functor_map C A A (book_pointed_identity A)) (book_pointed_identity OA))
      ((g ↦ pointed_wild_lu S A g), kpt)

{` xca:O-functor, composition law: O(g ∘ f) = O(g) ∘ O(f) as pointed maps. `}
def o_functor_map_comp (C : CircleSignature) (A B D : Pointed) (f : BookPointedMap A B) (g : BookPointedMap B D)
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C D))
      (o_functor_map C A D (book_pointed_compose A B D f g))
      (book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C B) (circle_pointed_maps C D)
        (o_functor_map C A B f) (o_functor_map C B D g))
  ≔ let S ≔ circle_pointed C in
    let Y ≔ B .carrier in let Z ≔ D .carrier in
    let a ≔ A .point in let b ≔ B .point in let d ≔ D .point in
    let OA ≔ circle_pointed_maps C A in let OD ≔ circle_pointed_maps C D in
    let M ≔ BookPointedMap S D in
    let Σb ≔ Σ Y (x ↦ Id Y b x) in let Σd ≔ Σ Z (x ↦ Id Z d x) in
    let FB ≔ pointed_constant_at S B in let FD ≔ pointed_constant_at S D in
    let cstA ≔ book_pointed_constant S A in let cst ≔ book_pointed_constant S D in
    let fa ≔ f .fst a in let gfa ≔ g .fst fa in
    let gf ≔ book_pointed_compose A B D f g in
    let gfp ≔ concat Z d (g .fst b) gfa (g .snd) (refl (g .fst) (f .snd)) in
    let p1 ≔ concat Z d gfa gfa gfp (refl gfa) in
    let p2 ≔ concat Z d (g .fst b) gfa (g .snd) (refl (g .fst) (concat Y b fa fa (f .snd) (refl fa))) in
    let G ≔ (w ↦ (g .fst (w .fst), concat Z d (g .fst b) (g .fst (w .fst)) (g .snd) (refl (g .fst) (w .snd)))) : Σb → Σd in
    let u1 ≔ o_point_path Z d gfa gfp in
    let assoc0 ≔ pointed_wild_assoc S A B D cstA f g in
    let θ : Id (Id Z d gfa) p2 p1 ≔ assoc0 .snd in
    let w ≔ (refl gfa, θ) : Id Σd (gfa, p2) (gfa, p1) in
    let u2 ≔ o_point_path Z d (g .fst b) (g .snd) in
    let u3 ≔ o_point_path Y b fa (f .snd) in
    let kpt : Id (Id M cst (FD (gfa, p2)))
        (concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (inverse M (FD (gfa, p2)) (FD (gfa, p1)) assoc0))
        (concat M cst (FD (g .fst b, concat Z d (g .fst b) (g .fst b) (g .snd) (refl (g .fst b)))) (FD (gfa, p2))
          (refl FD u2) (refl FD (refl G u3)))
      ≔ calc
          concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (inverse M (FD (gfa, p2)) (FD (gfa, p1)) assoc0)
            = concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (inverse M (FD (gfa, p2)) (FD (gfa, p1)) (refl FD w))
            by refl ((z ↦ concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (inverse M (FD (gfa, p2)) (FD (gfa, p1)) z))
                : Id M (FD (gfa, p2)) (FD (gfa, p1)) → Id M cst (FD (gfa, p2)))
              (o_constant_refl_path C D gfa p2 p1 θ)
          = concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (refl FD (inverse Σd (gfa, p2) (gfa, p1) w))
            by refl (concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1))
              (inverse (Id M (FD (gfa, p1)) (FD (gfa, p2))) (refl FD (inverse Σd (gfa, p2) (gfa, p1) w))
                (inverse M (FD (gfa, p2)) (FD (gfa, p1)) (refl FD w))
                (map_path_inverse Σd M FD (gfa, p2) (gfa, p1) w))
          = refl FD (concat Σd (d, refl d) (gfa, p1) (gfa, p2) u1 (inverse Σd (gfa, p2) (gfa, p1) w))
            by inverse (Id M cst (FD (gfa, p2))) (refl FD (concat Σd (d, refl d) (gfa, p1) (gfa, p2) u1 (inverse Σd (gfa, p2) (gfa, p1) w)))
              (concat M cst (FD (gfa, p1)) (FD (gfa, p2)) (refl FD u1) (refl FD (inverse Σd (gfa, p2) (gfa, p1) w)))
              (map_path_concat Σd M FD (d, refl d) (gfa, p1) (gfa, p2) u1 (inverse Σd (gfa, p2) (gfa, p1) w))
          = refl FD (concat Σd (d, refl d) (G (b, refl b)) (gfa, p2) u2 (refl G u3))
            by o_constant_paths_agree C D gfa p2
              (concat Σd (d, refl d) (gfa, p1) (gfa, p2) u1 (inverse Σd (gfa, p2) (gfa, p1) w))
              (concat Σd (d, refl d) (G (b, refl b)) (gfa, p2) u2 (refl G u3))
          = concat M cst (FD (G (b, refl b))) (FD (gfa, p2)) (refl FD u2) (refl FD (refl G u3))
            by map_path_concat Σd M FD (d, refl d) (G (b, refl b)) (gfa, p2) u2 (refl G u3) ∎ in
    equiv_inverse_map
      (Id (BookPointedMap OA OD) (o_functor_map C A D gf)
        (book_pointed_compose OA (circle_pointed_maps C B) OD (o_functor_map C A B f) (o_functor_map C B D g)))
      (PointedHomotopy OA OD (o_functor_map C A D gf)
        (book_pointed_compose OA (circle_pointed_maps C B) OD (o_functor_map C A B f) (o_functor_map C B D g)))
      (pointed_map_path_equiv OA OD (o_functor_map C A D gf)
        (book_pointed_compose OA (circle_pointed_maps C B) OD (o_functor_map C A B f) (o_functor_map C B D g)))
      ((h ↦ inverse M (book_pointed_compose S B D (book_pointed_compose S A B h f) g) (book_pointed_compose S A D h gf)
          (pointed_wild_assoc S A B D h f g)), kpt)

{` xca:O-functor: O is a wild functor U_* → U_* (cats.tex def:functor). `}
def o_wild_functor (C : CircleSignature) : WildFunctor PointedWild PointedWild
  ≔ (obj ≔ A ↦ circle_pointed_maps C A,
     mor ≔ A B f ↦ o_functor_map C A B f,
     map_id ≔ A ↦ o_functor_map_id C A,
     map_comp ≔ A B D f g ↦ o_functor_map_comp C A B D f g)

{` Running text after def:O-functor: if f_pt ≡ refl then O(f)_pt is a
   reflexivity path; in Narya the endpoint is cst_*(f pt, refl·refl), and
   O(f)_pt is the image of the unit law (refl, (concat_p1 refl)⁻¹). `}
def o_functor_point_refl (C : CircleSignature) (A : Pointed) (Y : Type) (f : A .carrier → Y)
  : Id (Id (BookPointedMap (circle_pointed C) (Y, f (A .point))) (book_pointed_constant (circle_pointed C) (Y, f (A .point)))
        (pointed_constant_at (circle_pointed C) (Y, f (A .point))
          (f (A .point), concat Y (f (A .point)) (f (A .point)) (f (A .point)) (refl (f (A .point))) (refl (f (A .point))))))
      (o_functor_map C A (Y, f (A .point)) (f, refl (f (A .point))) .snd)
      (refl (constant (C .carrier) Y (f (A .point))),
        inverse (Id Y (f (A .point)) (f (A .point))) (concat Y (f (A .point)) (f (A .point)) (f (A .point)) (refl (f (A .point))) (refl (f (A .point))))
          (refl (f (A .point))) (concat_p1 Y (f (A .point)) (f (A .point)) (refl (f (A .point)))))
  ≔ let y ≔ f (A .point) in let ryy ≔ concat Y y y y (refl y) (refl y) in
    o_constant_paths_agree C (Y, y) y ryy (o_point_path Y y y (refl y))
      ((refl y, inverse (Id Y y y) ryy (refl y) (concat_p1 Y y y (refl y))) : Id (Σ Y (x ↦ Id Y y x)) (y, refl y) (y, ryy))

{` Transport in the first endpoint: (b ↦ (b = v)) along e sends w to e⁻¹·w. `}
def first_endpoint_transport (T : Type) (u u' v : T) (e : Id T u u') (w : Id T u v)
  : Id (Id T u' v) (refl ((b ↦ Id T b v) : T → Type) e .trr w) (concat T u' u v (inverse T u u' e) w)
  ≔ J T u (u' e ↦ Id (Id T u' v) (refl ((b ↦ Id T b v) : T → Type) e .trr w) (concat T u' u v (inverse T u u' e) w))
      (calc
        concat T u v v w (refl v) = w by concat_p1 T u v w
        = concat T u u v (refl u) w by inverse (Id T u v) (concat T u u v (refl u) w) w (concat_1p T u v w)
        = concat T u u v (inverse T u u (refl u)) w
          by refl ((z ↦ concat T u u v z w) : Id T u u → Id T u v) (inverse (Id T u u) (inverse T u u (refl u)) (refl u) (inverse_refl T u)) ∎)
      u' e

{` The pathover-to-transport map over refl is w ↦ transport_refl(u)·w. `}
def pathover_transport_refl_map (A : Type) (B : A → Type) (x : A) (u v : B x) (w : Id (B x) u v)
  : Id (Id (B x) (transport A B x x (refl x) u) v)
      (pathover_transport_equiv A B x x (refl x) u v .map w)
      (concat (B x) (transport A B x x (refl x) u) u v (transport_refl A B x u) w)
  ≔ let M : (y : A) → Id A x y → Type
      ≔ y p ↦ (v : B y) → Id Type (Id B p u v) (Id (B y) (transport A B x y p u) v) in
    let base : M x (refl x)
      ≔ v ↦ refl ((b ↦ Id (B x) b v) : B x → Type)
        (inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u)) in
    let tu ≔ transport A B x x (refl x) u in
    let e ≔ inverse (B x) tu u (transport_refl A B x u) in
    let T ≔ Id (B x) tu v in
    calc
      pathover_transport_equiv A B x x (refl x) u v .map w
        = pathover_transport_type A B x x (refl x) u v .trr w
        by id_to_equiv_transport (Id (B x) u v) T (pathover_transport_type A B x x (refl x) u v) w
      = base v .trr w
        by inverse T (base v .trr w) (pathover_transport_type A B x x (refl x) u v .trr w)
          (refl ((φ ↦ φ v .trr w) : M x (refl x) → T) (Jβ A x M base))
      = concat (B x) tu u v (inverse (B x) u tu e) w by first_endpoint_transport (B x) u tu v e w
      = concat (B x) tu u v (transport_refl A B x u) w
        by refl ((z ↦ concat (B x) tu u v z w) : Id (B x) tu u → T)
          (inverse_inverse (B x) tu u (transport_refl A B x u)) ∎

def o_point_pathover_refl (X : Type) (b : X)
  : Id (Id (Id X b b) (refl b) (concat X b b b (refl b) (refl b))) (o_point_pathover X b b (refl b))
      (inverse (Id X b b) (concat X b b b (refl b) (refl b)) (refl b) (concat_p1 X b b (refl b)))
  ≔ let sq0 ≔ inverse (Id X b b) (concat X b b b (refl b) (refl b)) (refl b) (concat_p1 X b b (refl b)) in
    inverse (Id (Id X b b) (refl b) (concat X b b b (refl b) (refl b))) sq0 (o_point_pathover X b b (refl b))
      (Jβ X b (y v ↦ Id ((x ↦ Id X b x) : X → Type) v (refl b) (concat X b y y v (refl y))) sq0)

{` The pair (cst_{f_pt}, ρ_{f_pt}) : H(pt_{OB}, O(f)(pt_{OA})); its pointing
   component ρ' : refl·f_pt = f_pt·refl (Narya form of ρ_{f_pt}). `}
def o_point_homotopy (C : CircleSignature) (B : Pointed) (y : B .carrier) (v : Id (B .carrier) (B .point) y)
  : PointedHomotopy (circle_pointed C) B (book_pointed_constant (circle_pointed C) B)
      (pointed_constant_at (circle_pointed C) B (y, concat (B .carrier) (B .point) y y v (refl y)))
  ≔ let X ≔ B .carrier in let b ≔ B .point in
    ((_ ↦ v), concat (Id X b y) (concat X b b y (refl b) v) v (concat X b y y v (refl y))
       (concat_1p X b y v) (inverse (Id X b y) (concat X b y y v (refl y)) v (concat_p1 X b y v)))

def o_point_ptw (C : CircleSignature) (B : Pointed) (y : B .carrier) (v : Id (B .carrier) (B .point) y)
  : Id (PointedHomotopy (circle_pointed C) B (book_pointed_constant (circle_pointed C) B)
        (pointed_constant_at (circle_pointed C) B (y, concat (B .carrier) (B .point) y y v (refl y))))
      (pointed_map_path_equiv (circle_pointed C) B (book_pointed_constant (circle_pointed C) B)
        (pointed_constant_at (circle_pointed C) B (y, concat (B .carrier) (B .point) y y v (refl y)))
        .map (refl (pointed_constant_at (circle_pointed C) B) (o_point_path (B .carrier) (B .point) y v)))
      (o_point_homotopy C B y v)
  ≔ let S ≔ circle_pointed C in let X ≔ B .carrier in let b ≔ B .point in
    let F ≔ pointed_constant_at S B in let cst ≔ book_pointed_constant S B in
    let T : (C .carrier → X) → Type ≔ k ↦ Id X b (k (C .base)) in
    let rbb ≔ concat X b b b (refl b) (refl b) in
    let Hb ≔ PointedHomotopy S B cst (F (b, rbb)) in
    let sq0 ≔ inverse (Id X b b) rbb (refl b) (concat_p1 X b b (refl b)) in
    J X b (y v ↦ Id (PointedHomotopy S B cst (F (y, concat X b y y v (refl y))))
        (pointed_map_path_equiv S B cst (F (y, concat X b y y v (refl y))) .map (refl F (o_point_path X b y v)))
        (o_point_homotopy C B y v))
      (calc
        pointed_map_path_equiv S B cst (F (b, rbb)) .map (refl F (o_point_path X b b (refl b)))
          = ((_ ↦ refl b), pathover_transport_equiv (C .carrier → X) T (cst .fst) (cst .fst) (refl (cst .fst)) (refl b) rbb
              .map (o_point_pathover X b b (refl b)))
          by pointed_map_path_equiv_ptw S B cst (F (b, rbb)) (refl F (o_point_path X b b (refl b)))
        = ((_ ↦ refl b), concat (Id X b b) rbb (refl b) rbb (concat_p1 X b b (refl b)) (o_point_pathover X b b (refl b)))
          by (refl ((_ ↦ refl b) : Homotopy (C .carrier) (_ ↦ X) (cst .fst) (cst .fst)),
              pathover_transport_refl_map (C .carrier → X) T (cst .fst) (refl b) rbb (o_point_pathover X b b (refl b)))
        = ((_ ↦ refl b), concat (Id X b b) rbb (refl b) rbb (concat_p1 X b b (refl b)) sq0)
          by (refl ((_ ↦ refl b) : Homotopy (C .carrier) (_ ↦ X) (cst .fst) (cst .fst)),
              refl (concat (Id X b b) rbb (refl b) rbb (concat_p1 X b b (refl b)))
                (o_point_pathover_refl X b))
        = o_point_homotopy C B b (refl b)
          by (refl ((_ ↦ refl b) : Homotopy (C .carrier) (_ ↦ X) (cst .fst) (cst .fst)),
              refl ((z ↦ concat (Id X b b) rbb (refl b) rbb z sq0) : Id (Id X b b) rbb (refl b) → Id (Id X b b) rbb rbb)
                (concat_p1_1p_refl X b)) ∎)
      y v

{` xca:O-functor, second part: O(f)_pt = ptw_*⁻¹(cst_{f_pt}, ρ_{f_pt}). `}
def o_functor_point_ptw (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
        (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f))
      (o_functor_map C A B f .snd)
      (equiv_inverse_map
        (Id (BookPointedMap (circle_pointed C) B) (book_pointed_constant (circle_pointed C) B)
          (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f))
        (PointedHomotopy (circle_pointed C) B (book_pointed_constant (circle_pointed C) B)
          (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f))
        (pointed_map_path_equiv (circle_pointed C) B (book_pointed_constant (circle_pointed C) B)
          (book_pointed_compose (circle_pointed C) A B (book_pointed_constant (circle_pointed C) A) f))
        (o_point_homotopy C B (f .fst (A .point)) (f .snd)))
  ≔ let S ≔ circle_pointed C in
    let cst ≔ book_pointed_constant S B in
    let tgt ≔ book_pointed_compose S A B (book_pointed_constant S A) f in
    let Pm ≔ Id (BookPointedMap S B) cst tgt in
    let Ph ≔ PointedHomotopy S B cst tgt in
    let e ≔ pointed_map_path_equiv S B cst tgt in
    concat Pm (o_functor_map C A B f .snd) (equiv_inverse_map Pm Ph e (e .map (o_functor_map C A B f .snd)))
      (equiv_inverse_map Pm Ph e (o_point_homotopy C B (f .fst (A .point)) (f .snd)))
      (equiv_unit Pm Ph e (o_functor_map C A B f .snd))
      (refl (equiv_inverse_map Pm Ph e) (o_point_ptw C B (f .fst (A .point)) (f .snd)))
