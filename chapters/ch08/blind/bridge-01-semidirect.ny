export "01-semidirect"
export "../../../src/803-semidirect-kernel"
export "../../../src/810-wreath-products"

{` Bridges for congp.tex, semidirect products (general part) and
   wreath products. The blind semidirect product, kernel group, path-section
   action and wreath product are ours by refl (same Σ-type, same base point,
   same proof terms after unfolding). The blind form of lem:pathpairsection
   names the inverse map Ψ(p, q) = ap_{(x,-)}(q) · ap_{(-,f -)}(p); it is a
   section of our Φ = path_pair_section_map, hence an equivalence, and
   lem:pathpairsectionmult in the Ψ form follows from our Φ form because Φ
   is injective. `}

def bridge_def_semidirect (G : Group) (H : BG G .carrier → Group)
  : Id Group (blind_semidirect G H) (semidirect_product G H)
  ≔ refl (semidirect_product G H)

def bridge_def_ker_group (G G' : Group) (f : GroupHom G G')
  : Id Group (blind_ker_group G G' f) (fiber_kernel_group G G' f)
  ≔ refl (fiber_kernel_group G G' f)

def bridge_def_ker_map (G G' : Group) (f : GroupHom G G')
  : Id (GroupHom (fiber_kernel_group G G' f) G) (blind_ker_map G G' f) (fiber_kernel_inclusion G G' f)
  ≔ refl (fiber_kernel_inclusion G G' f)

def bridge_def_semidirect_maps (G : Group) (H : BG G .carrier → Group)
  : Product (Id (GroupHom (semidirect_product G H) G) (blind_semidirect_proj G H) (semidirect_projection G H))
      (Product (Id (GroupHom G (semidirect_product G H)) (blind_semidirect_section G H) (semidirect_section G H))
        (Id (GroupHom (H (shape G)) (semidirect_product G H)) (blind_semidirect_incl G H) (semidirect_inclusion G H)))
  ≔ (refl (semidirect_projection G H), (refl (semidirect_section G H), refl (semidirect_inclusion G H)))

def bridge_def_path_section_action (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : Id (Id (Y x') (f x') (f x') → Id (Y x) (f x) (f x))
      (blind_path_section_action X Y f x x' p) (q' ↦ section_loop_action X Y f x x' p q')
  ≔ refl (blind_path_section_action X Y f x x' p)

def bridge_def_wreath (G H : Group) (X : GSet G)
  : Id Group (blind_wreath G H X) (wreath_product H G X)
  ≔ refl (wreath_product H G X)

{` lem:pathpairsection. `}
def bridge_lem_pathpairsection : blind_lem_pathpairsection
  ≔ X Y f x x' ↦ path_pair_section_book_equiv X Y f x x'

{` Φ ∘ Ψ = id, by induction on p. `}
def bridge_pathpair_section_base (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x : X)
  (q : Id (Y x) (f x) (f x))
  : Id (Product (Id X x x) (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x (blind_pathpair X Y f x x (refl x, q))) (refl x, q)
  ≔ let e ≔ map_path (Y x) (Σ X Y) (y ↦ (x, y)) (f x) (f x) q in
    concat (Product (Id X x x) (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x (blind_pathpair X Y f x x (refl x, q)))
      (path_pair_section_map X Y f x x e) (refl x, q)
      (refl (path_pair_section_map X Y f x x) (concat_p1 (Σ X Y) (x, f x) (x, f x) e))
      (refl (refl x), section_pathover_loop_refl X Y f x q)

def bridge_pathpair_section (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X) (p : Id X x x')
  : (q : Id (Y x) (f x) (f x))
    → Id (Product (Id X x x') (Id (Y x) (f x) (f x)))
        (path_pair_section_map X Y f x x' (blind_pathpair X Y f x x' (p, q))) (p, q)
  ≔ J X x (x' p ↦ (q : Id (Y x) (f x) (f x))
        → Id (Product (Id X x x') (Id (Y x) (f x) (f x)))
            (path_pair_section_map X Y f x x' (blind_pathpair X Y f x x' (p, q))) (p, q))
      (q ↦ bridge_pathpair_section_base X Y f x q) x' p

def bridge_pathpair_eta (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (pq : Product (Id X x x') (Id (Y x) (f x) (f x)))
  : Id (Product (Id X x x') (Id (Y x) (f x) (f x)))
      (path_pair_section_map X Y f x x' (blind_pathpair X Y f x x' pq)) pq
  ≔ bridge_pathpair_section X Y f x x' (pq .fst) (pq .snd)

{` Φ is injective: Ψ Φ e = e. `}
def bridge_pathpair_injective (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (e e' : Id (Σ X Y) (x, f x) (x', f x'))
  (h : Id (Product (Id X x x') (Id (Y x) (f x) (f x))) (path_pair_section_map X Y f x x' e)
         (path_pair_section_map X Y f x x' e'))
  : Id (Id (Σ X Y) (x, f x) (x', f x')) e e'
  ≔ let P ≔ Id (Σ X Y) (x, f x) (x', f x') in
    let Q ≔ Product (Id X x x') (Id (Y x) (f x) (f x)) in
    let E ≔ path_pair_section_equiv X Y f x x' in
    concat P e (equiv_inverse_map P Q E (E .map e)) e'
      (inverse P (equiv_inverse_map P Q E (E .map e)) e (equiv_retraction P Q E e))
      (concat P (equiv_inverse_map P Q E (E .map e)) (equiv_inverse_map P Q E (E .map e')) e'
        (refl (equiv_inverse_map P Q E) h) (equiv_retraction P Q E e'))

def bridge_pathpair_epsilon (X : Type) (Y : X → Type) (f : (x : X) → Y x) (x x' : X)
  (e : Id (Σ X Y) (x, f x) (x', f x'))
  : Id (Id (Σ X Y) (x, f x) (x', f x')) (blind_pathpair X Y f x x' (path_pair_section_map X Y f x x' e)) e
  ≔ bridge_pathpair_injective X Y f x x' (blind_pathpair X Y f x x' (path_pair_section_map X Y f x x' e)) e
      (bridge_pathpair_eta X Y f x x' (path_pair_section_map X Y f x x' e))

def bridge_lem_pathpairsection_map : blind_lem_pathpairsection_map
  ≔ X Y f x x' ↦
      book_equivalence (Product (Id X x x') (Id (Y x) (f x) (f x))) (Id (Σ X Y) (x, f x) (x', f x'))
        (quasi_inverse_equiv (Product (Id X x x') (Id (Y x) (f x) (f x))) (Id (Σ X Y) (x, f x) (x', f x'))
          (blind_pathpair X Y f x x') (path_pair_section_map X Y f x x')
          (bridge_pathpair_eta X Y f x x') (bridge_pathpair_epsilon X Y f x x')) .equiv

{` def:pathsectionactionassoc. `}
def bridge_lem_pathsectionactionassoc : blind_lem_pathsectionactionassoc
  ≔ X Y f x x' x'' p p' q ↦ section_loop_action_assoc X Y f x x' p x'' p' q

{` lem:pathpairsectionmult (Ψ form), from path_pair_section_mult (Φ form). `}
def bridge_lem_pathpairsectionmult : blind_lem_pathpairsectionmult
  ≔ X Y f x x' x'' p q p' q' ↦
      let Psi ≔ blind_pathpair X Y f in
      let r : Product (Id X x x'') (Id (Y x) (f x) (f x))
        ≔ (concat X x x' x'' p p', concat (Y x) (f x) (f x) (f x) q (blind_path_section_action X Y f x x' p q')) in
      bridge_pathpair_injective X Y f x x''
        (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') (Psi x x' (p, q)) (Psi x' x'' (p', q')))
        (Psi x x'' r)
        (concat (Product (Id X x x'') (Id (Y x) (f x) (f x)))
          (path_pair_section_map X Y f x x''
            (concat (Σ X Y) (x, f x) (x', f x') (x'', f x'') (Psi x x' (p, q)) (Psi x' x'' (p', q'))))
          r (path_pair_section_map X Y f x x'' (Psi x x'' r))
          (path_pair_section_mult X Y f x x' x'' (Psi x x' (p, q)) (Psi x' x'' (p', q')) p q p' q'
            (bridge_pathpair_eta X Y f x x' (p, q)) (bridge_pathpair_eta X Y f x' x'' (p', q')))
          (inverse (Product (Id X x x'') (Id (Y x) (f x) (f x)))
            (path_pair_section_map X Y f x x'' (Psi x x'' r)) r (bridge_pathpair_eta X Y f x x'' r)))

{` congp.tex:291. `}
def bridge_lem_semidirect_kernel : blind_lem_semidirect_kernel
  ≔ G H ↦ (semidirect_inclusion_mono G H, (semidirect_kernel_iso G H, semidirect_kernel_iso_inclusion G H))

{` Converse (bonus): our formulation from the blind one. `}
def bridge_lem_semidirect_kernel_converse (k : blind_lem_semidirect_kernel) (G : Group) (H : BG G .carrier → Group)
  : Id (GroupMonos (semidirect_product G H))
      (H (shape G), (semidirect_inclusion G H, k G H .fst))
      (fiber_kernel (semidirect_product G H) G (semidirect_projection G H))
  ≔ sdp_group_monos_path_from_iso (semidirect_product G H) (H (shape G))
      (fiber_kernel_group (semidirect_product G H) G (semidirect_projection G H))
      (k G H .snd .fst) (semidirect_inclusion G H) (k G H .fst)
      (fiber_kernel_inclusion (semidirect_product G H) G (semidirect_projection G H))
      (fiber_kernel_inclusion_mono (semidirect_product G H) G (semidirect_projection G H))
      (k G H .snd .snd)
