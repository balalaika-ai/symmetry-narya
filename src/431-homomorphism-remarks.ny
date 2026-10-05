export "403-abstract-groups"
export "406-symmetric-group-three"

{` Chapter 4, section "Homomorphisms" (group.tex 932-1239): remarks and
   examples around def:grouphomomorphism. `}

{` rem:homom-eqs. "Without loss of generality" pt_BH ≡ k(pt_BG) and
   k_pt ≡ refl: given a group G, a connected groupoid B and k : BG÷ → B,
   the group H ≔ mkgroup (B, k(sh_G)) has shape k(sh_G) judgmentally, and
   f ≔ ap_k : USym G → USym H is defined. `}
def homom_eqs_target (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B)
  (k : BG G .carrier → B) : Group
  ≔ mkgroup (B, k (shape G), conn, grpd)

def homom_eqs_shape (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  : Id B (shape (homom_eqs_target G B conn grpd k)) (k (shape G))
  ≔ refl (k (shape G))

def homom_eqs_ap (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  : USym G → USym (homom_eqs_target G B conn grpd k)
  ≔ g ↦ refl k g

{` f(refl) = refl holds by definition (refl, as in the book). `}
def homom_eqs_unit (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  : Id (USym (homom_eqs_target G B conn grpd k)) (homom_eqs_ap G B conn grpd k (usym_unit G))
      (usym_unit (homom_eqs_target G B conn grpd k))
  ≔ refl (refl (k (shape G)))

{` f(g⁻¹) = f(g)⁻¹ and f(g'·g) = f(g')·f(g), by lem:apcomp. `}
def homom_eqs_inv (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  (g : USym G)
  : Id (USym (homom_eqs_target G B conn grpd k)) (homom_eqs_ap G B conn grpd k (usym_inv G g))
      (usym_inv (homom_eqs_target G B conn grpd k) (homom_eqs_ap G B conn grpd k g))
  ≔ map_path_inverse (BG G .carrier) B k (shape G) (shape G) g

def homom_eqs_mul (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  (g' g : USym G)
  : Id (USym (homom_eqs_target G B conn grpd k)) (homom_eqs_ap G B conn grpd k (usym_mul G g' g))
      (usym_mul (homom_eqs_target G B conn grpd k) (homom_eqs_ap G B conn grpd k g')
        (homom_eqs_ap G B conn grpd k g))
  ≔ map_path_concat (BG G .carrier) B k (shape G) (shape G) (shape G) g g'

{` "These identities entitle one to call f a homomorphism of abstract
   groups". `}
def homom_eqs_abstract_hom (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B)
  (k : BG G .carrier → B)
  : IsAbstractHom (abstr G) (abstr (homom_eqs_target G B conn grpd k)) (homom_eqs_ap G B conn grpd k)
  ≔ s s' ↦ homom_eqs_mul G B conn grpd k s s'

{` The homomorphism classified by (k, refl), whose USym is ap_k
   (rem:loops-map). `}
def homom_eqs_hom (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  : GroupHom G (homom_eqs_target G B conn grpd k)
  ≔ mkhom G (homom_eqs_target G B conn grpd k) (k, refl (k (shape G)))

def homom_eqs_usym_hom (G : Group) (B : Type) (conn : Connected B) (grpd : isGroupoid B) (k : BG G .carrier → B)
  : Id (USym G → USym (homom_eqs_target G B conn grpd k))
      (usym_hom G (homom_eqs_target G B conn grpd k) (homom_eqs_hom G B conn grpd k))
      (homom_eqs_ap G B conn grpd k)
  ≔ loops_map_refl_pointing (BG G .carrier) B k (shape G)

{` ap of a conjugated loop is the conjugate of the ap (lem:apcomp). `}
def map_path_loop_conjugate (A B : Type) (f : A → B) (a x : A) (p : Id A a x) (l : Id A x x)
  : Id (Id B (f a) (f a)) (refl f (pointed_loop_conjugate A a x p l))
      (pointed_loop_conjugate B (f a) (f x) (refl f p) (refl f l))
  ≔ calc
      refl f (pointed_loop_conjugate A a x p l)
      = concat B (f a) (f x) (f a) (refl f p) (refl f (concat A x x a l (inverse A a x p)))
        by map_path_concat A B f a x a p (concat A x x a l (inverse A a x p))
      = concat B (f a) (f x) (f a) (refl f p) (concat B (f x) (f x) (f a) (refl f l) (refl f (inverse A a x p)))
        by refl (concat B (f a) (f x) (f a) (refl f p)) (map_path_concat A B f x x a l (inverse A a x p))
      = pointed_loop_conjugate B (f a) (f x) (refl f p) (refl f l)
        by refl (concat B (f a) (f x) (f a) (refl f p))
          (refl (concat B (f x) (f x) (f a) (refl f l)) (map_path_inverse A B f a x p)) ∎

{` For k pointed by refl and a type family π on the codomain, π applied to
   Ω k(g) is π ∘ k applied to g (rem:loops-map, at the level of Type). `}
def loops_map_refl_family (X Y : Type) (k : X → Y) (x0 : X) (pi : Y → Type) (g : Id X x0 x0)
  : Id (Id Type (pi (k x0)) (pi (k x0))) (refl pi (loops_map (X, x0) (Y, k x0) (k, refl (k x0)) g))
      (refl ((u ↦ pi (k u)) : X → Type) g)
  ≔ concat (Id Type (pi (k x0)) (pi (k x0))) (refl pi (loops_map (X, x0) (Y, k x0) (k, refl (k x0)) g))
      (pointed_loop_conjugate Type (pi (k x0)) (pi (k x0)) (refl (pi (k x0))) (refl pi (refl k g)))
      (refl ((u ↦ pi (k u)) : X → Type) g)
      (map_path_loop_conjugate Y Type pi (k x0) (k x0) (refl (k x0)) (refl k g))
      (loop_conjugate_at_refl Type (pi (k x0)) (refl pi (refl k g)))

{` rem:first-abs-hom: USym f preserves the neutral element, products and
   inverses of the abstract groups abstr(G), abstr(H). `}
def usym_hom_abstract_equations (G H : Group) (f : GroupHom G H)
  : Product (Id (USym H) (usym_hom G H f (abstr G .unit)) (abstr H .unit))
      (Product ((g g' : USym G) → Id (USym H) (usym_hom G H f (abstr G .mul g g'))
                  (abstr H .mul (usym_hom G H f g) (usym_hom G H f g')))
               ((g : USym G) → Id (USym H) (usym_hom G H f (abstr G .inv g)) (abstr H .inv (usym_hom G H f g))))
  ≔ (usym_hom_unit G H f, (g g' ↦ usym_hom_mul G H f g g', g ↦ usym_hom_inv G H f g))

{` rem:Bf-convention: to define φ : Π(f : Hom(G,H)) T(f) it suffices to
   treat f ≡ mkhom(Bf); with the one-field record this is eta, and the
   computation rule holds judgmentally. `}
def group_hom_induction (G H : Group) (T : GroupHom G H → Type)
  (φ : (k : BookPointedMap (BG G) (BG H)) → T (mkhom G H k)) (f : GroupHom G H) : T f
  ≔ φ (hom_B G H f)

def group_hom_induction_beta (G H : Group) (T : GroupHom G H → Type)
  (φ : (k : BookPointedMap (BG G) (BG H)) → T (mkhom G H k)) (k : BookPointedMap (BG G) (BG H))
  : Id (T (mkhom G H k)) (group_hom_induction G H T φ (mkhom G H k)) (φ k)
  ≔ refl (φ k)

{` The paragraph before lem:hom-is-set, literally: f = f' is equivalent
   to pairs of an identification h : Bf÷ = Bf'÷ of unpointed maps and an
   identification h(sh_G) · Bf_pt = Bf'_pt (book order; concat Bf_pt h(sh_G)
   here). The core's group_hom_path_equiv uses homotopies instead of h;
   this is the composite with function extensionality. `}
def GroupHomPathData (G H : Group) (f f' : GroupHom G H) : Type
  ≔ Σ (Id (BG G .carrier → BG H .carrier) (hom_function G H f) (hom_function G H f'))
      (h ↦ Id (Id (BG H .carrier) (shape H) (hom_function G H f' (shape G)))
        (concat (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_function G H f' (shape G))
          (hom_point G H f) (h (refl (shape G))))
        (hom_point G H f'))

def group_hom_path_data_equiv (G H : Group) (f f' : GroupHom G H)
  : Equiv (Id (GroupHom G H) f f') (GroupHomPathData G H f f')
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in
    let E ≔ Id (A → B) (hom_function G H f) (hom_function G H f') in
    let Hm ≔ Homotopy A (_ ↦ B) (hom_function G H f) (hom_function G H f') in
    let P : Hm → Type ≔ h ↦ Id (Id B (shape H) (hom_function G H f' (shape G)))
      (concat B (shape H) (hom_function G H f (shape G)) (hom_function G H f' (shape G))
        (hom_point G H f) (h (shape G))) (hom_point G H f') in
    compose_equiv (Id (GroupHom G H) f f') (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
      (GroupHomPathData G H f f')
      (group_hom_path_equiv G H f f')
      (canonical_inverse_equiv (GroupHomPathData G H f f') (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
        (sigma_pullback_equiv E Hm (function_extensionality A (_ ↦ B) (hom_function G H f) (hom_function G H f')) P))

{` ex:groups-morphisms, item 2. Homomorphisms into a group with
   contractible classifying type, and out of one, form contractible types
   (the latter by contractible_domain_pointed_maps of module 98, the
   lem:contract-away / lem:univ-cover-of-groupoid argument). The centers are
   the homomorphisms of the book. `}
def prop_book_contractible (A : Type) (h : isProp A) (a : A) : BookIsContr A ≔ (a, b ↦ h a b)

def group_hom_into_contractible_prop (G H : Group) (hH : BookIsContr (BG H .carrier)) : isProp (GroupHom G H)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in
    let pB : isProp B ≔ contractible_prop B (native_contraction B hH) in
    let pM : isProp (BookPointedMap (BG G) (BG H))
      ≔ sigma_prop (A → B) (k ↦ Id B (shape H) (k (shape G))) (pi_prop A (_ ↦ B) (_ ↦ pB))
          (k ↦ prop_is_set B pB (shape H) (k (shape G))) in
    f f' ↦ refl (mkhom G H) (pM (hom_B G H f) (hom_B G H f'))

def group_hom_into_contractible (G H : Group) (hH : BookIsContr (BG H .carrier)) : BookIsContr (GroupHom G H)
  ≔ prop_book_contractible (GroupHom G H) (group_hom_into_contractible_prop G H hH)
      (mkhom G H (_ ↦ shape H, refl (shape H)))

def group_hom_from_contractible (G H : Group) (hG : BookIsContr (BG G .carrier)) : BookIsContr (GroupHom G H)
  ≔ book_contractibility_equiv (BookPointedMap (BG G) (BG H)) (GroupHom G H)
      (canonical_inverse_equiv (GroupHom G H) (BookPointedMap (BG G) (BG H)) (group_hom_classifying_equiv G H))
      .map (contractible_domain_pointed_maps (BG G) (BG H) hG)

def group_hom_to_unit_unique (G : Group) : BookIsContr (GroupHom G unit_group)
  ≔ prop_book_contractible (GroupHom G unit_group)
      (group_hom_into_contractible_prop G unit_group unit_contraction) (group_hom_to_unit G)

def group_hom_from_unit_unique (G : Group) : BookIsContr (GroupHom unit_group G)
  ≔ (group_hom_from_unit G,
     f ↦ contractible_prop (GroupHom unit_group G)
       (native_contraction (GroupHom unit_group G) (group_hom_from_contractible unit_group G unit_contraction))
       (group_hom_from_unit G) f)

{` The same for the book's trivial group Aut_Prop(true), whose classifying
   type is a connected set, hence contractible. `}
def trivial_group_classifying_contractible : BookIsContr (BG trivial_group .carrier)
  ≔ connected_set_contractible native_truncation (BG trivial_group .carrier) (bg_connected trivial_group)
      (hlevel_two_to_set (BG trivial_group .carrier)
        (subtype_hlevel (suc. zero.) PropTypes (x ↦ Mere (Id PropTypes true_proposition x))
          (set_to_hlevel_two PropTypes propositions_set) (x ↦ mere_isprop (Id PropTypes true_proposition x))))

def group_hom_to_trivial_unique (G : Group) : BookIsContr (GroupHom G trivial_group)
  ≔ group_hom_into_contractible G trivial_group trivial_group_classifying_contractible

def group_hom_from_trivial_unique (G : Group) : BookIsContr (GroupHom trivial_group G)
  ≔ group_hom_from_contractible trivial_group G trivial_group_classifying_contractible

{` The book's literal trivial group with classifying type bn 1 = Fin 1,
   pointed at its unique element. `}
def fin_one_contraction : BookIsContr (Fin (suc. zero.))
  ≔ (inr. star., [ inl. e ↦ match e [] | inr. u ↦ inr. (unit_prop star. u) ])

def fin_one_group : Group ≔ contractible_group (Fin (suc. zero.)) (inr. star.) fin_one_contraction

def group_hom_to_fin_one_unique (G : Group) : BookIsContr (GroupHom G fin_one_group)
  ≔ group_hom_into_contractible G fin_one_group fin_one_contraction

def group_hom_from_fin_one_unique (G : Group) : BookIsContr (GroupHom fin_one_group G)
  ≔ group_hom_from_contractible fin_one_group G fin_one_contraction

{` ex:groups-morphisms, item 3 (litmus): the projections and inclusions
   of module 404 act on symmetries as projections and inclusions. `}
def product_group_proj1_usym (G H : Group) (r : USym (product_group G H))
  : Id (USym G) (usym_hom (product_group G H) G (product_group_proj1 G H) r) (r .fst)
  ≔ happly (USym (product_group G H)) (_ ↦ USym G)
      (usym_hom (product_group G H) G (product_group_proj1 G H)) (l ↦ refl ((t ↦ t .fst) : Product (BG G .carrier) (BG H .carrier) → BG G .carrier) l)
      (loops_map_refl_pointing (Product (BG G .carrier) (BG H .carrier)) (BG G .carrier) (t ↦ t .fst) (shape G, shape H)) r

def product_group_incl1_usym (G H : Group) (g : USym G)
  : Id (USym (product_group G H)) (usym_hom G (product_group G H) (product_group_incl1 G H) g) (g, refl (shape H))
  ≔ happly (USym G) (_ ↦ USym (product_group G H))
      (usym_hom G (product_group G H) (product_group_incl1 G H)) (l ↦ refl ((z ↦ (z, shape H)) : BG G .carrier → Product (BG G .carrier) (BG H .carrier)) l)
      (loops_map_refl_pointing (BG G .carrier) (Product (BG G .carrier) (BG H .carrier)) (z ↦ (z, shape H)) (shape G)) g

{` The remark at group.tex 1202, convention: a map f : A → B of groupoids
   induces the homomorphism Aut_A(a) → Aut_B(f(a)) classified by f on
   components, pointed by refl (judgmentally). `}
def native_component_map (A B : Type) (f : A → B) (a : A) (u : NativeComponent A a) : NativeComponent B (f a)
  ≔ (f (u .fst), mere_rec (Id A a (u .fst)) (Mere (Id B (f a) (f (u .fst)))) (mere_isprop (Id B (f a) (f (u .fst))))
      (p ↦ mere (Id B (f a) (f (u .fst))) (refl f p)) (u .snd))

def automorphism_group_map_hom (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (f : A → B) (a : A)
  : GroupHom (automorphism_group A hA a) (automorphism_group B hB (f a))
  ≔ mkhom (automorphism_group A hA a) (automorphism_group B hB (f a))
      (native_component_map A B f a, refl (component_point B (f a)))

{` Its action on symmetries is ap_f on first components. `}
def automorphism_group_map_usym (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (f : A → B) (a : A)
  (g : USym (automorphism_group A hA a))
  : Id (Id B (f a) (f a))
      (usym_hom (automorphism_group A hA a) (automorphism_group B hB (f a)) (automorphism_group_map_hom A B hA hB f a) g .fst)
      (refl f (g .fst))
  ≔ refl ((r ↦ r .fst) : Id (NativeComponent B (f a)) (component_point B (f a)) (component_point B (f a)) → Id B (f a) (f a))
      (happly (USym (automorphism_group A hA a)) (_ ↦ USym (automorphism_group B hB (f a)))
        (usym_hom (automorphism_group A hA a) (automorphism_group B hB (f a)) (automorphism_group_map_hom A B hA hB f a))
        (l ↦ refl (native_component_map A B f a) l)
        (loops_map_refl_pointing (NativeComponent A a) (NativeComponent B (f a)) (native_component_map A B f a)
          (component_point A a)) g)

{` The remark at group.tex 1202: (id, refl) and (id, τ) are different
   elements of Hom(Σ_3, Σ_3), τ = (0 1). Ω(id, τ)(g) is τ⁻¹·g·τ in the
   book's notation, judgmentally. `}
def sigma3_tilde_tau : GroupHom (symmetric_group three) (symmetric_group three)
  ≔ mkhom (symmetric_group three) (symmetric_group three)
      (identity (BG (symmetric_group three) .carrier), sigma3_tau)

def sigma3_tilde_tau_usym (g : USym (symmetric_group three))
  : Id (USym (symmetric_group three)) (usym_hom (symmetric_group three) (symmetric_group three) sigma3_tilde_tau g)
      (usym_mul (symmetric_group three)
        (usym_mul (symmetric_group three) (usym_inv (symmetric_group three) sigma3_tau) g) sigma3_tau)
  ≔ refl (usym_hom (symmetric_group three) (symmetric_group three) sigma3_tilde_tau g)

{` If h⁻¹·g·h = g then g and h commute (path algebra in a loop space). `}
def loop_conjugate_fixed_commutes (A : Type) (a : A) (g h : Id A a a)
  (e : Id (Id A a a) (concat A a a a h (concat A a a a g (inverse A a a h))) g)
  : Id (Id A a a) (concat A a a a g h) (concat A a a a h g)
  ≔ let L ≔ Id A a a in
    calc
      concat A a a a g h
      = concat A a a a (concat A a a a h (concat A a a a g (inverse A a a h))) h
        by refl ((q ↦ concat A a a a q h) : L → L) (inverse L (concat A a a a h (concat A a a a g (inverse A a a h))) g e)
      = concat A a a a h (concat A a a a (concat A a a a g (inverse A a a h)) h)
        by concat_assoc A a a a a h (concat A a a a g (inverse A a a h)) h
      = concat A a a a h (concat A a a a g (concat A a a a (inverse A a a h) h))
        by refl (concat A a a a h) (concat_assoc A a a a a g (inverse A a a h) h)
      = concat A a a a h (concat A a a a g (refl a))
        by refl (concat A a a a h) (refl (concat A a a a g) (concat_inverse_left A a a h))
      = concat A a a a h g
        by refl (concat A a a a h) (concat_p1 A a a g) ∎

{` If (id, refl) = (id, τ) then τ commutes with every symmetry of Σ_3
   ("so τ commutes with every other element"). `}
def sigma3_tilde_tau_commutes
  (h : Id (GroupHom (symmetric_group three) (symmetric_group three)) (group_hom_id (symmetric_group three)) sigma3_tilde_tau)
  (g : USym (symmetric_group three))
  : Id (USym (symmetric_group three)) (usym_mul (symmetric_group three) sigma3_tau g)
      (usym_mul (symmetric_group three) g sigma3_tau)
  ≔ let S ≔ symmetric_group three in let A ≔ BG S .carrier in let a ≔ shape S in
    loop_conjugate_fixed_commutes A a g sigma3_tau
      (concat (USym S) (usym_hom S S sigma3_tilde_tau g) (usym_hom S S (group_hom_id S) g) g
        (inverse (USym S) (usym_hom S S (group_hom_id S) g) (usym_hom S S sigma3_tilde_tau g)
          (refl ((f ↦ usym_hom S S f g) : GroupHom S S → USym S) h))
        (usym_hom_id S g))

def sigma3_two_homs_differ
  (h : Id (GroupHom (symmetric_group three) (symmetric_group three)) (group_hom_id (symmetric_group three)) sigma3_tilde_tau)
  : Empty
  ≔ let S ≔ symmetric_group three in
    sigma3_tau_sigma_noncommuting
      (inverse (USym S) (usym_mul S sigma3_tau sigma3_sigma) (usym_mul S sigma3_sigma sigma3_tau)
        (sigma3_tilde_tau_commutes h sigma3_sigma))
