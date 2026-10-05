export "723-abstract-conjugation"
export "437-conjugation-inner-automorphisms"

{` Chapter 7 (absgroup.tex), ex:conjhom, last paragraph: the connection
   of conj^g with inner automorphisms (exa:conj-concrete, def:inner-autos;
   module 437). For g : USym G:

   - Ω(id_BG, g⁻¹) is conj^g: the abstract homomorphism abstr of the
     pointed map (id_BG, g⁻¹) (conj_hom of module 437) is
     abstract_conj_hom (abstr G) g, i.e. s ↦ g·s·g⁻¹ with the usym_mul
     convention g·h = concat h g;
   - abstr(Binn)(g): USym(inn)(g) is an identification r : G = G of groups
     (inn_usym_fst, module 437); applying abstr to it gives an
     identification abstr G = abstr G of abstract groups, and this is the
     identification conj^g of xca:conj / ex:conjhom
     (inn_abstr_conj_path). Transport along r in the family USym is
     conj^g (inn_usym_acts_by_conjugation, module 437). `}

def abstr_conj_hom_is_abstract_conj (G : Group) (g : USym G)
  : Id (AbstractHom (abstr G) (abstr G)) (abstr_hom G G (conj_hom G (shape G) g)) (abstract_conj_hom (abstr G) g)
  ≔ abstract_hom_ext (abstr G) (abstr G) (abstr_hom G G (conj_hom G (shape G) g)) (abstract_conj_hom (abstr G) g)
      (s ↦ conj_at_shape_usym G g s)

def inn_identification (G : Group) (g : USym G) : Id Group G G ≔ usym_hom G (group_aut G) (inn G) g .fst

{` The isomorphism underlying abstr applied to USym(inn)(g) is conj^g. `}
def inn_abstr_iso (G : Group) (g : USym G)
  : Id (AbstractIso (abstr G) (abstr G))
      (abstract_group_path_to_iso (abstr G) (abstr G) (refl abstr (inn_identification G g)))
      (abstract_conj_iso (abstr G) g)
  ≔ abstract_iso_path (abstr G) (abstr G)
      (abstract_group_path_to_iso (abstr G) (abstr G) (refl abstr (inn_identification G g)))
      (abstract_conj_iso (abstr G) g)
      (funext (USym G) (_ ↦ USym G) (h ↦ transport Group USym G G (inn_identification G g) h)
        (abstract_conj (abstr G) g) (h ↦ inn_usym_acts_by_conjugation G g h))

{` abstr(Binn)(g) = conj^g as identifications abstr G = abstr G. `}
def inn_abstr_conj_path (G : Group) (g : USym G)
  : Id (Id AbstractGroup (abstr G) (abstr G)) (refl abstr (inn_identification G g)) (abstract_conj_path (abstr G) g)
  ≔ let A ≔ abstr G in
    equivalence_injective (Id AbstractGroup A A) (AbstractIso A A) (abstract_group_path_iso_equiv A A)
      (refl abstr (inn_identification G g)) (abstract_conj_path A g)
      (concat (AbstractIso A A)
        (abstract_group_path_to_iso A A (refl abstr (inn_identification G g)))
        (abstract_conj_iso A g)
        (abstract_group_path_to_iso A A (abstract_conj_path A g))
        (inn_abstr_iso G g)
        (inverse (AbstractIso A A) (abstract_group_path_to_iso A A (abstract_conj_path A g)) (abstract_conj_iso A g)
          (abstract_group_iso_path_section A A (abstract_conj_iso A g))))

{` Generic helpers (kept abstract so that no transport along a
   reflexivity path of a concrete identity type has to be evaluated, which
   triggers bug[E0500] here). `}
def transport_path_congr (X : Type) (B : X → Type) (x y : X) (q q' : Id X x y) (e : Id (Id X x y) q q') (b : B x)
  : Id (B y) (transport X B x y q b) (transport X B x y q' b)
  ≔ refl ((r ↦ transport X B x y r b) : Id X x y → B y) e

def path_transport_nontrivial (X : Type) (B : X → Type) (x : X) (q : Id X x x) (b : B x)
  (ne : Id (B x) (transport X B x x q b) b → Empty) (p : Id (Id X x x) q (refl x)) : Empty
  ≔ ne (concat (B x) (transport X B x x q b) (transport X B x x (refl x) b) b
      (transport_path_congr X B x x q (refl x) p b) (transport_refl X B x b))

{` Litmus: for Σ_3 and τ = (0 1) the identification abstr(Binn)(τ) is not
   refl (it moves σ = (1 2)). `}
def inn_abstr_sigma3_nontrivial
  (p : Id (Id AbstractGroup (abstr (symmetric_group three)) (abstr (symmetric_group three)))
    (refl abstr (inn_identification (symmetric_group three) sigma3_tau)) (refl (abstr (symmetric_group three))))
  : Empty
  ≔ let S ≔ symmetric_group three in let A ≔ abstr S in
    let B : AbstractGroup → Type ≔ X ↦ X .carrier in
    let q ≔ refl abstr (inn_identification S sigma3_tau) in
    path_transport_nontrivial AbstractGroup B A q sigma3_sigma
      (r ↦ abstract_conj_sigma3_moves
        (concat (USym S) (abstract_conj A sigma3_tau sigma3_sigma) (transport AbstractGroup B A A q sigma3_sigma) sigma3_sigma
          (transport_path_congr AbstractGroup B A A (abstract_conj_path A sigma3_tau) q
            (inverse (Id AbstractGroup A A) q (abstract_conj_path A sigma3_tau) (inn_abstr_conj_path S sigma3_tau)) sigma3_sigma)
          r))
      p

{` Litmus for xca:typemonoidisgroupoid (abstract-group half): the type of
   abstract groups is a groupoid (abstract_group_groupoid) but not a set. `}
def abstract_group_not_set (h : isSet AbstractGroup) : Empty
  ≔ inn_abstr_sigma3_nontrivial
      (h (abstr (symmetric_group three)) (abstr (symmetric_group three))
        (refl abstr (inn_identification (symmetric_group three) sigma3_tau)) (refl (abstr (symmetric_group three))))
