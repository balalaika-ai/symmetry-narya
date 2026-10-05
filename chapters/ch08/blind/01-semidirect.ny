{` Blind statements for chapter 8 (congp.tex), sections "Semidirect products"
   (general part) and "Wreath products". `}
export "../../../src/502-subgroups"
export "../../../src/407-group-family-products"

{` Helper: a Σ-type of groupoids over a groupoid is a groupoid (lem:level-n-utils). `}
def blind_sigma_groupoid (A : Type) (B : A → Type) (hA : isGroupoid A) (hB : (a : A) → isGroupoid (B a))
  : isGroupoid (Σ A B)
  ≔ hlevel_to_groupoid (Σ A B)
      (hlevel_sigma (suc. (suc. (suc. zero.))) A B (groupoid_to_hlevel A hA) (a ↦ groupoid_to_hlevel (B a) (hB a)))

{` def:semidirect-product. G ⋉ H ≔ mkgroup(Σ_{t:BG} BH(t)) at (sh_G, sh_{H(sh_G)}).
   Connectedness (xca:connected-trivia-1) and groupoid-ness (footnote) are proved. `}
def BlindSemidirectCarrier (G : Group) (H : BG G .carrier → Group) : Type
  ≔ Σ (BG G .carrier) (t ↦ BG (H t) .carrier)

def blind_semidirect (G : Group) (H : BG G .carrier → Group) : Group
  ≔ mkgroup (BlindSemidirectCarrier G H, (shape G, shape (H (shape G))),
      connected_sigma native_truncation (BG G .carrier) (t ↦ BG (H t) .carrier) (bg_connected G) (t ↦ bg_connected (H t)),
      blind_sigma_groupoid (BG G .carrier) (t ↦ BG (H t) .carrier) (bg_groupoid G) (t ↦ bg_groupoid (H t)))

{` lem:pathpairsection. The book's equivalence, read backwards: (p, q) ↦ e, where
   e first runs along q inside the fibre over x and then along the section over p.
   For p = refl x it is ap_{y ↦ (x,y)}(q), as in the book's proof (by induction on p). `}
def blind_pathpair (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (pq : Product (Id X x x') (Id (Y x) (f x) (f x))) : Id (Σ X Y) (x, f x) (x', f x')
  ≔ concat (Σ X Y) (x, f x) (x, f x) (x', f x')
      (map_path (Y x) (Σ X Y) (y ↦ (x, y)) (f x) (f x) (pq .snd))
      (map_path X (Σ X Y) (z ↦ (z, f z)) x x' (pq .fst))

def blind_lem_pathpairsection : Type
  ≔ (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
    → BookEquiv (Id (Σ X Y) (x, f x) (x', f x')) (Product (Id X x x') (Id (Y x) (f x) (f x)))

{` The same lemma with the equivalence named (its inverse is blind_pathpair). `}
def blind_lem_pathpairsection_map : Type
  ≔ (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
    → BookIsEquiv (Product (Id X x x') (Id (Y x) (f x) (f x))) (Id (Σ X Y) (x, f x) (x', f x'))
        (blind_pathpair X Y f x x')

{` def:pathsectionaction. q' ↦ q'^p : (f x' = f x') → (f x = f x), by induction on p with q'^{refl} ≔ q'. `}
def blind_path_section_action (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : Id (Y x') (f x') (f x') → Id (Y x) (f x) (f x)
  ≔ J X x (z p ↦ Id (Y z) (f z) (f z) → Id (Y x) (f x) (f x)) (q ↦ q) x' p

{` def:pathsectionactionassoc. (q^{p'})^p = q^{p' · p}; the book's p' · p (p first) is concat p p'. `}
def blind_lem_pathsectionactionassoc : Type
  ≔ (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X) (p : Id X x x') (p' : Id X x' x'')
    (q : Id (Y x'') (f x'') (f x''))
    → Id (Id (Y x) (f x) (f x))
        (blind_path_section_action X Y f x x' p (blind_path_section_action X Y f x' x'' p' q))
        (blind_path_section_action X Y f x x'' (concat X x x' x'' p p') q)

{` lem:pathpairsectionmult. If e ↔ (p, q) and e' ↔ (p', q') then e' · e ↔ (p' · p, q'^p · q).
   Book composition e' · e (e first) is concat e e'; q'^p · q is concat q (q'^p). `}
def blind_lem_pathpairsectionmult : Type
  ≔ (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' x'' : X)
    (p : Id X x x') (q : Id (Y x) (f x) (f x)) (p' : Id X x' x'') (q' : Id (Y x') (f x') (f x'))
    → Id (Id (Σ X Y) (x, f x) (x'', f x''))
        (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'')
          (blind_pathpair X Y f x x' (p, q)) (blind_pathpair X Y f x' x'' (p', q')))
        (blind_pathpair X Y f x x''
          (concat X x x' x'' p p', concat (Y x) (f x) (f x) (f x) q (blind_path_section_action X Y f x x' p q')))

{` The homomorphisms p, s, j of the text before the unnamed lemma (all pointed by refl). `}
def blind_semidirect_proj (G : Group) (H : BG G .carrier → Group) : GroupHom (blind_semidirect G H) G
  ≔ mkhom (blind_semidirect G H) G (u ↦ u .fst, refl (shape G))

def blind_semidirect_section (G : Group) (H : BG G .carrier → Group) : GroupHom G (blind_semidirect G H)
  ≔ mkhom G (blind_semidirect G H) (t ↦ (t, shape (H t)), refl (shape G, shape (H (shape G))))

def blind_semidirect_incl (G : Group) (H : BG G .carrier → Group) : GroupHom (H (shape G)) (blind_semidirect G H)
  ≔ mkhom (H (shape G)) (blind_semidirect G H) (u ↦ (shape G, u), refl (shape G, shape (H (shape G))))

{` def:kernel (chapter 9, needed here): Ker(f) ≔ Aut_{(Bf)⁻¹(sh_{G'})}(sh_G, Bf_pt), with the first projection. `}
def BlindKerCarrier (G G' : Group) (f : GroupHom G G') : Type
  ≔ BookFiber (BG G .carrier) (BG G' .carrier) (hom_function G G' f) (shape G')

def blind_ker_groupoid (G G' : Group) (f : GroupHom G G') : isGroupoid (BlindKerCarrier G G' f)
  ≔ blind_sigma_groupoid (BG G .carrier) (z ↦ Id (BG G' .carrier) (shape G') (hom_function G G' f z))
      (bg_groupoid G) (z ↦ set_is_groupoid (Id (BG G' .carrier) (shape G') (hom_function G G' f z))
                             (bg_groupoid G' (shape G') (hom_function G G' f z)))

def blind_ker_group (G G' : Group) (f : GroupHom G G') : Group
  ≔ automorphism_group (BlindKerCarrier G G' f) (blind_ker_groupoid G G' f) (shape G, hom_point G G' f)

def blind_ker_map (G G' : Group) (f : GroupHom G G') : GroupHom (blind_ker_group G G' f) G
  ≔ mkhom (blind_ker_group G G' f) G (c ↦ c .fst .fst, refl (shape G))

{` congp.tex:291 (unnamed lemma). j is a monomorphism, and (H, j) is the same monomorphism into
   G ⋉ H̃ as ker p: an isomorphism φ : H ≅ Ker p with ker_p ∘ φ = j. (Normality is not stated.) `}
def blind_lem_semidirect_kernel : Type
  ≔ (G : Group) (H : BG G .carrier → Group)
    → Product (IsGroupMono (H (shape G)) (blind_semidirect G H) (blind_semidirect_incl G H))
        (Σ (GroupIso (H (shape G)) (blind_ker_group (blind_semidirect G H) G (blind_semidirect_proj G H))) (phi ↦
           Id (GroupHom (H (shape G)) (blind_semidirect G H))
             (group_hom_compose (H (shape G)) (blind_ker_group (blind_semidirect G H) G (blind_semidirect_proj G H))
                (blind_semidirect G H) (phi .fst)
                (blind_ker_map (blind_semidirect G H) G (blind_semidirect_proj G H)))
             (blind_semidirect_incl G H)))

{` Wreath products: H^X(z) ≔ Aut_{X(z) → BH}(_ ↦ sh_H) and H ≀_X G ≔ G ⋉ H^X (congp.tex:328). `}
def blind_power_action (G H : Group) (X : GSet G) : BG G .carrier → Group
  ≔ z ↦ automorphism_group (X z .fst → BG H .carrier)
          (groupoid_pi (X z .fst) (_ ↦ BG H .carrier) (_ ↦ bg_groupoid H)) (_ ↦ shape H)

def blind_wreath (G H : Group) (X : GSet G) : Group ≔ blind_semidirect G (blind_power_action G H X)
