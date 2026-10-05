export "709-groups-are-abstract-groups"
export "710-hom-delooping"
export "721-mere-inverses"
export "452-sign-two-loops"
export "419-cyclic-two-and-generated"
export "406-symmetric-group-three"

{` Litmus checks running through the equivalence Group ≃ AbstractGroup of
   thm:Groupsareidentitytypes and the Hom equivalence of
   lem:homomabstrconcr (built-in cross-check of chapters 4 and 7). `}

{` 1. Integers under addition (int_add_abstract_group, module 721). In
   abstr(concr ℤ) the symmetries T(u) attached to integers multiply like
   the integers: T(2) · T(3) = T(5), and T(u) acts on the principal torsor
   by x ↦ x - u (5 ↦ 3 for u = 2, by computation). `}
def litmus_int_two : Int ≔ pos. (suc. (suc. zero.))
def litmus_int_three : Int ≔ pos. (suc. (suc. (suc. zero.)))
def litmus_int_five : Int ≔ pos. (suc. (suc. (suc. (suc. (suc. zero.)))))

def concr_int_sum_litmus
  : Id (USym (concr int_add_abstract_group))
      (usym_mul (concr int_add_abstract_group) (concr_usym_of int_add_abstract_group litmus_int_two)
        (concr_usym_of int_add_abstract_group litmus_int_three))
      (concr_usym_of int_add_abstract_group litmus_int_five)
  ≔ inverse (USym (concr int_add_abstract_group))
      (concr_usym_of int_add_abstract_group litmus_int_five)
      (usym_mul (concr int_add_abstract_group) (concr_usym_of int_add_abstract_group litmus_int_two)
        (concr_usym_of int_add_abstract_group litmus_int_three))
      (concr_abstr_hom int_add_abstract_group litmus_int_two litmus_int_three)

{` Numerals written with literal suc. (a refl lemma on numerals through
   def aliases triggers the Narya anomaly Meta.Map.find_opt on import). `}
def concr_int_action_litmus
  : Id Int (abstract_r_map int_add_abstract_group (pos. (suc. (suc. zero.))) .fst .map (pos. (suc. (suc. (suc. (suc. (suc. zero.)))))))
      (pos. (suc. (suc. (suc. zero.))))
  ≔ refl (pos. (suc. (suc. (suc. zero.))))

{` 2. Σ₃: abstr(Σ₃) is not abelian, and neither is concr(abstr(Σ₃)). `}
def abstr_sigma_three_not_abelian (h : IsAbstractAbelian (abstr (symmetric_group three))) : Empty
  ≔ symmetric_group_three_not_abelian h

def concr_abstr_sigma_three_not_abelian (h : IsAbelian (concr (abstr (symmetric_group three)))) : Empty
  ≔ symmetric_group_three_not_abelian
      (transport Group IsAbelian (concr (abstr (symmetric_group three))) (symmetric_group three)
        (concr_abstr_path (symmetric_group three)) h)

{` 3. The abstract cyclic group of order 2, {±1} under multiplication
   (sign_abstract_group, module 452): concr of it is identified with
   cyclic_group 2, through abstr(Σ₂) ≅ {±1} and C₂ = Σ₂ (module 419). `}
def sigma_two_sign_abstract_iso : AbstractIso (abstr sign_sigma_two) sign_abstract_group
  ≔ (sigma_two_sign_equiv, sigma_two_sign_abstract_hom .snd)

def concr_sign_sigma_two_path : Id Group (concr sign_abstract_group) sign_sigma_two
  ≔ concat Group (concr sign_abstract_group) (concr (abstr sign_sigma_two)) sign_sigma_two
      (refl concr (inverse AbstractGroup (abstr sign_sigma_two) sign_abstract_group
        (abstract_group_path_from_iso (abstr sign_sigma_two) sign_abstract_group sigma_two_sign_abstract_iso)))
      (concr_abstr_path sign_sigma_two)

def concr_sign_cyclic_two_path : Id Group (concr sign_abstract_group) (cyclic_group two)
  ≔ concat Group (concr sign_abstract_group) (cyclic_group_fin (suc. zero.)) (cyclic_group two)
      (concat Group (concr sign_abstract_group) sign_sigma_two (cyclic_group_fin (suc. zero.))
        concr_sign_sigma_two_path
        (inverse Group (cyclic_group_fin (suc. zero.)) (symmetric_group two) cyclic_two_symmetric_two_path))
      (cyclic_group_fin_path (suc. zero.))

{` 4. lem:homomabstrconcr on the identity: deloop(abstr(id)) = id and
   abstr(deloop(id)) = id. `}
def deloop_identity_litmus (G : Group)
  : Id (GroupHom G G) (deloop_hom G G (abstr_hom G G (group_hom_id G))) (group_hom_id G)
  ≔ deloop_hom_retraction G G (group_hom_id G)

def deloop_abstr_identity_litmus (G : Group)
  : Id (AbstractHom (abstr G) (abstr G)) (abstr_hom G G (deloop_hom G G (abstract_hom_id (abstr G)))) (abstract_hom_id (abstr G))
  ≔ deloop_hom_section G G (abstract_hom_id (abstr G))
