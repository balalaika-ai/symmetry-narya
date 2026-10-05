export "711-abstract-concrete-litmus"

{` Chapter 7 (absgroup.tex), sec:cat-equiv (marked wip in the book):
   xca:SG2=SG2-contractible, Iso(Σ_2, C_2) is contractible. Iso is the type
   GroupIso of group isomorphisms (module 401), Σ_2 = symmetric_group 2 and
   C_2 = cyclic_group 2. Proof through the equivalence of
   thm:Groupsareidentitytypes: GroupIso G H ≃ (G = H) ≃ (abstr G = abstr H)
   ≃ AbstractIso (abstr G) (abstr H), and both abstr Σ_2 and abstr C_2 are
   isomorphic to {±1} (sign_abstract_group, module 452), whose only
   automorphism is the identity. `}

{` GroupIso G H ≃ AbstractIso (abstr G) (abstr H). `}
def group_iso_abstract_iso_equiv (G H : Group) : Equiv (GroupIso G H) (AbstractIso (abstr G) (abstr H))
  ≔ compose_equiv (GroupIso G H) (Id Group G H) (AbstractIso (abstr G) (abstr H))
      (canonical_inverse_equiv (Id Group G H) (GroupIso G H) (group_path_iso_equiv G H))
      (compose_equiv (Id Group G H) (Id AbstractGroup (abstr G) (abstr H)) (AbstractIso (abstr G) (abstr H))
        (equivalence_on_paths Group AbstractGroup group_abstract_group_equiv G H)
        (abstract_group_path_iso_equiv (abstr G) (abstr H)))

def cyclic_two_abstr_sign_path : Id AbstractGroup (abstr (cyclic_group two)) sign_abstract_group
  ≔ concat AbstractGroup (abstr (cyclic_group two)) (abstr (concr sign_abstract_group)) sign_abstract_group
      (refl abstr (inverse Group (concr sign_abstract_group) (cyclic_group two) concr_sign_cyclic_two_path))
      (abstr_concr_path sign_abstract_group)

def cyclic_two_sign_abstract_iso : AbstractIso (abstr (cyclic_group two)) sign_abstract_group
  ≔ abstract_group_path_to_iso (abstr (cyclic_group two)) sign_abstract_group cyclic_two_abstr_sign_path

def sign_minus_ne_plus (p : Id Sign minus. plus.) : Empty ≔ plus_ne_minus (inverse Sign minus. plus. p)

{` Every automorphism of {±1} is the identity. `}
def sign_iso_unit (k : AbstractIso sign_abstract_group sign_abstract_group) : Id Sign (k .fst .map plus.) plus.
  ≔ abstract_hom_preserves_unit sign_abstract_group sign_abstract_group (k .fst .map) (k .snd)

def sign_iso_minus_not_plus (k : AbstractIso sign_abstract_group sign_abstract_group)
  (p : Id Sign (k .fst .map minus.) plus.) : Empty
  ≔ sign_minus_ne_plus
      (equivalence_injective Sign Sign (k .fst) minus. plus.
        (concat Sign (k .fst .map minus.) plus. (k .fst .map plus.) p
          (inverse Sign (k .fst .map plus.) plus. (sign_iso_unit k))))

def sign_iso_minus_value (k : AbstractIso sign_abstract_group sign_abstract_group)
  : (u : Sign) → Id Sign (k .fst .map minus.) u → Id Sign (k .fst .map minus.) minus.
  ≔ [ plus. ↦ p ↦ match sign_iso_minus_not_plus k p [] | minus. ↦ p ↦ p ]

def sign_iso_fixed (k : AbstractIso sign_abstract_group sign_abstract_group) (s : Sign) : Id Sign (k .fst .map s) s
  ≔ match s [
    | plus. ↦ sign_iso_unit k
    | minus. ↦ sign_iso_minus_value k (k .fst .map minus.) (refl (k .fst .map minus.)) ]

{` If A ≅ {±1} ≅ B, any isomorphism f : A ≅ B satisfies β(f(x)) = α(x). `}
def sign_like_iso_value (A B : AbstractGroup) (α : AbstractIso A sign_abstract_group)
  (β : AbstractIso B sign_abstract_group) (f : AbstractIso A B) (x : A .carrier)
  : Id Sign (β .fst .map (f .fst .map x)) (α .fst .map x)
  ≔ let S ≔ sign_abstract_group in
    let k : AbstractIso sign_abstract_group sign_abstract_group ≔ abstract_iso_compose S A S (abstract_iso_inverse A S α) (abstract_iso_compose A B S f β) in
    concat Sign (β .fst .map (f .fst .map x))
      (β .fst .map (f .fst .map (equiv_inverse_map (A .carrier) Sign (α .fst) (α .fst .map x)))) (α .fst .map x)
      (refl ((y ↦ β .fst .map (f .fst .map y)) : A .carrier → Sign) (equiv_unit (A .carrier) Sign (α .fst) x))
      (sign_iso_fixed k (α .fst .map x))

def sign_like_iso_prop (A B : AbstractGroup) (α : AbstractIso A sign_abstract_group)
  (β : AbstractIso B sign_abstract_group) : isProp (AbstractIso A B)
  ≔ f g ↦ abstract_iso_path A B f g
      (funext (A .carrier) (_ ↦ B .carrier) (f .fst .map) (g .fst .map)
        (x ↦ equivalence_injective (B .carrier) Sign (β .fst) (f .fst .map x) (g .fst .map x)
          (concat Sign (β .fst .map (f .fst .map x)) (α .fst .map x) (β .fst .map (g .fst .map x))
            (sign_like_iso_value A B α β f x)
            (inverse Sign (β .fst .map (g .fst .map x)) (α .fst .map x) (sign_like_iso_value A B α β g x)))))

def sigma_two_cyclic_two_iso : GroupIso (symmetric_group two) (cyclic_group two)
  ≔ group_path_iso_equiv (symmetric_group two) (cyclic_group two) .map
      (concat Group (symmetric_group two) (cyclic_group_fin (suc. zero.)) (cyclic_group two)
        (inverse Group (cyclic_group_fin (suc. zero.)) (symmetric_group two) cyclic_two_symmetric_two_path)
        (cyclic_group_fin_path (suc. zero.)))

def sigma_two_cyclic_two_isos_prop : isProp (GroupIso (symmetric_group two) (cyclic_group two))
  ≔ let G ≔ symmetric_group two in let H ≔ cyclic_group two in
    let E : Equiv (GroupIso G H) (AbstractIso (abstr G) (abstr H)) ≔ group_iso_abstract_iso_equiv G H in
    u v ↦ equivalence_injective (GroupIso G H) (AbstractIso (abstr G) (abstr H)) E u v
      (sign_like_iso_prop (abstr G) (abstr H) sigma_two_sign_abstract_iso cyclic_two_sign_abstract_iso (E .map u) (E .map v))

{` xca:SG2=SG2-contractible. `}
def sigma_two_cyclic_two_isos_contractible : BookIsContr (GroupIso (symmetric_group two) (cyclic_group two))
  ≔ (sigma_two_cyclic_two_iso, u ↦ sigma_two_cyclic_two_isos_prop sigma_two_cyclic_two_iso u)

{` Litmus: {±1} has exactly one automorphism, while Σ_3 (non-abelian)
   has a non-trivial one (inn_abstr_sigma3_nontrivial, module 730). `}
def sign_automorphisms_contractible : BookIsContr (AbstractIso sign_abstract_group sign_abstract_group)
  ≔ (abstract_iso_id sign_abstract_group,
     k ↦ abstract_iso_path sign_abstract_group sign_abstract_group (abstract_iso_id sign_abstract_group) k
       (funext Sign (_ ↦ Sign) (s ↦ s) (k .fst .map) (s ↦ inverse Sign (k .fst .map s) s (sign_iso_fixed k s))))
