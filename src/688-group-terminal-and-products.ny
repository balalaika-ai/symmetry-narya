export "686-category-of-groups"
export "607-terminal-initial-objects"
export "665-products-and-coproducts"
export "431-homomorphism-remarks"

{` Chapter 6 (cats.tex), running-text claims about the category of groups
   GroupCat (module 686): the trivial group TG is terminal (line 454) and
   initial (line 464), and the product G × H of ex:productofgroups with the
   projection homomorphisms is a product cone (line 1449). TG is the book's
   trivial_group = Aut_Prop(true) of module 404; unit_group (classifying
   type Unit) is treated as well. The uniqueness of homomorphisms into and
   out of a group with contractible classifying type is module 431. `}

{` cats.tex 454: "the trivial group TG is a terminal object in the
   category of groups"; cats.tex 464: "the trivial group TG is initial in
   the category of groups". `}
def trivial_group_terminal : IsTerminalObj (GroupCat .wild) trivial_group ≔ group_hom_to_trivial_unique

def trivial_group_initial : IsInitialObj (GroupCat .wild) trivial_group ≔ group_hom_from_trivial_unique

def trivial_group_zero_object
  : Product (IsTerminalObj (GroupCat .wild) trivial_group) (IsInitialObj (GroupCat .wild) trivial_group)
  ≔ (trivial_group_terminal, trivial_group_initial)

def unit_group_terminal : IsTerminalObj (GroupCat .wild) unit_group ≔ group_hom_to_unit_unique

def unit_group_initial : IsInitialObj (GroupCat .wild) unit_group ≔ group_hom_from_unit_unique

{` Since GroupCat is univalent, the types of terminal and of initial
   objects are contractible (xca:terminal-prop), with center TG; in
   particular TG = 1 as groups. `}
def group_cat_terminal_contractible : BookIsContr (TerminalObj (GroupCat .wild))
  ≔ (center ≔ (trivial_group, trivial_group_terminal),
     contract ≔ t ↦ terminal_objects_prop (GroupCat .wild) (GroupCat .univalent) (trivial_group, trivial_group_terminal) t)

def group_cat_initial_contractible : BookIsContr (InitialObj (GroupCat .wild))
  ≔ (center ≔ (trivial_group, trivial_group_initial),
     contract ≔ t ↦ initial_objects_prop (GroupCat .wild) (GroupCat .univalent) (trivial_group, trivial_group_initial) t)

def trivial_group_unit_group_path : Id Group trivial_group unit_group
  ≔ terminal_objects_prop (GroupCat .wild) (GroupCat .univalent)
      (trivial_group, trivial_group_terminal) (unit_group, unit_group_terminal) .fst

{` Litmus checks: the unique homomorphism Σ_3 → 1 is the one of
   ex:groups-morphisms; Σ_3 is neither terminal nor initial (Hom(Σ_3, Σ_3)
   contains the two different homomorphisms (id, refl) and (id, τ) of
   module 431). `}
def unit_group_terminal_map_check
  : Id (GroupHom (symmetric_group three) unit_group)
      (unit_group_terminal (symmetric_group three) .center) (group_hom_to_unit (symmetric_group three))
  ≔ refl (group_hom_to_unit (symmetric_group three))

def sigma3_endomorphisms_not_contractible
  (c : BookIsContr (GroupHom (symmetric_group three) (symmetric_group three))) : Empty
  ≔ sigma3_two_homs_differ
      (book_contractible_paths (GroupHom (symmetric_group three) (symmetric_group three)) c
        (group_hom_id (symmetric_group three)) sigma3_tilde_tau)

def sigma3_not_terminal (h : IsTerminalObj (GroupCat .wild) (symmetric_group three)) : Empty
  ≔ sigma3_endomorphisms_not_contractible (h (symmetric_group three))

def sigma3_not_initial (h : IsInitialObj (GroupCat .wild) (symmetric_group three)) : Empty
  ≔ sigma3_endomorphisms_not_contractible (h (symmetric_group three))

{` cats.tex 1449: "in the category of groups, the product G × H from
   ex:productofgroups forms a product cone when equipped with the
   projection homomorphisms". A homomorphism K → G × H is the same as a
   pair of homomorphisms (its composites with the projections): the
   inverse pairs the classifying maps and their pointing paths. `}
def group_product_cone (G H : Group) : CatCone (GroupCat .wild) G H
  ≔ (product_group G H, (product_group_proj1 G H, product_group_proj2 G H))

def group_product_legs (G H K : Group) (f : GroupHom K (product_group G H))
  : Product (GroupHom K G) (GroupHom K H)
  ≔ (group_hom_compose K (product_group G H) G f (product_group_proj1 G H),
     group_hom_compose K (product_group G H) H f (product_group_proj2 G H))

def group_product_pairing (G H K : Group) (t : Product (GroupHom K G) (GroupHom K H))
  : GroupHom K (product_group G H)
  ≔ mkhom K (product_group G H)
      (x ↦ (hom_function K G (t .fst) x, hom_function K H (t .snd) x),
       (hom_point K G (t .fst), hom_point K H (t .snd)))

def group_product_legs_pairing (G H K : Group) (t : Product (GroupHom K G) (GroupHom K H))
  : Id (Product (GroupHom K G) (GroupHom K H)) (group_product_legs G H K (group_product_pairing G H K t)) t
  ≔ let P ≔ product_group G H in let s ≔ group_product_pairing G H K t in
    (refl (mkhom K G)
       ((refl (hom_function K G (t .fst)),
         concat_1p (BG G .carrier) (shape G) (hom_function K G (t .fst) (shape K)) (hom_point K G (t .fst)))
        : Id (BookPointedMap (BG K) (BG G))
            (hom_B K G (group_hom_compose K P G s (product_group_proj1 G H))) (hom_B K G (t .fst))),
     refl (mkhom K H)
       ((refl (hom_function K H (t .snd)),
         concat_1p (BG H .carrier) (shape H) (hom_function K H (t .snd) (shape K)) (hom_point K H (t .snd)))
        : Id (BookPointedMap (BG K) (BG H))
            (hom_B K H (group_hom_compose K P H s (product_group_proj2 G H))) (hom_B K H (t .snd))))

def group_product_pair_path (A B : Type) (a a' : A) (b b' : B) (p : Id A a a') (q : Id B b b')
  : Id (Product A B) (a, b) (a', b')
  ≔ (p, q)

def group_product_pairing_legs (G H K : Group) (f : GroupHom K (product_group G H))
  : Id (GroupHom K (product_group G H)) (group_product_pairing G H K (group_product_legs G H K f)) f
  ≔ let P ≔ product_group G H in
    let A ≔ BG G .carrier in let B ≔ BG H .carrier in
    let u ≔ hom_function K P f (shape K) in
    let fpt ≔ hom_point K P f in
    refl (mkhom K P)
      ((refl (hom_function K P f),
        refl (group_product_pair_path A B (shape G) (u .fst) (shape H) (u .snd))
          (concat_1p A (shape G) (u .fst) (fpt .fst)) (concat_1p B (shape H) (u .snd) (fpt .snd)))
       : Id (BookPointedMap (BG K) (BG P))
           (hom_B K P (group_product_pairing G H K (group_product_legs G H K f))) (hom_B K P f))

def group_product_legs_equiv (G H K : Group)
  : Equiv (GroupHom K (product_group G H)) (Product (GroupHom K G) (GroupHom K H))
  ≔ quasi_inverse_equiv (GroupHom K (product_group G H)) (Product (GroupHom K G) (GroupHom K H))
      (group_product_legs G H K) (group_product_pairing G H K)
      (group_product_pairing_legs G H K) (group_product_legs_pairing G H K)

{` The factorizations of a cone (K, x₁, x₂) through (G × H, p₁, p₂) are
   the (book) fiber of the equivalence above over (x₁, x₂). `}
def group_product_cone_is_product (G H : Group) : IsProductCone (GroupCat .wild) G H (group_product_cone G H)
  ≔ X ↦
    let K ≔ X .fst in
    let L ≔ Product (GroupHom K G) (GroupHom K H) in
    contractible_retract (BookFiber (GroupHom K (product_group G H)) L (group_product_legs G H K) (X .snd))
      (ConeFactorization (GroupCat .wild) G H X (group_product_cone G H))
      (native_contraction (BookFiber (GroupHom K (product_group G H)) L (group_product_legs G H K) (X .snd))
        (book_equivalence (GroupHom K (product_group G H)) L (group_product_legs_equiv G H K) .equiv (X .snd)))
      (t ↦ (t .fst, (t .snd .fst, t .snd .snd)))
      (s ↦ (s .fst, (s .snd .fst, s .snd .snd)))
      (s ↦ refl s)

def group_product_cone_product (G H : Group) : ProductCone (GroupCat .wild) G H
  ≔ (group_product_cone G H, group_product_cone_is_product G H)

{` "The category of groups has binary products", and every product cone
   on G, H is (G × H, p₁, p₂) (xca:product-cone-prop, GroupCat univalent). `}
def group_cat_has_binary_products : HasBinaryProducts (GroupCat .wild) ≔ group_product_cone_product

def group_product_cone_unique (G H : Group) (P : ProductCone (GroupCat .wild) G H)
  : Id (ProductCone (GroupCat .wild) G H) P (group_product_cone_product G H)
  ≔ product_cone_prop (GroupCat .wild) (GroupCat .univalent) G H P (group_product_cone_product G H)

{` Litmus: the factorization of the cone (Σ_3, id, id) through
   Σ_3 × Σ_3 is the diagonal x ↦ (x, x). `}
def sigma3_diagonal_cone : CatCone (GroupCat .wild) (symmetric_group three) (symmetric_group three)
  ≔ (symmetric_group three, (group_hom_id (symmetric_group three), group_hom_id (symmetric_group three)))

def sigma3_diagonal_factorization_check (x : BG (symmetric_group three) .carrier)
  : Id (BG (product_group (symmetric_group three) (symmetric_group three)) .carrier)
      (hom_function (symmetric_group three) (product_group (symmetric_group three) (symmetric_group three))
        (group_product_cone_is_product (symmetric_group three) (symmetric_group three) sigma3_diagonal_cone
          .center .fst) x)
      (x, x)
  ≔ refl ((x, x) : BG (product_group (symmetric_group three) (symmetric_group three)) .carrier)
