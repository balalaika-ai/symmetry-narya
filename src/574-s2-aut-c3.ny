import "568-s2-acts-on-c3"
import "572-s2-c3-identification"
import "573-aut-c3-bound"
import "873-s-action-paths"
import "419-cyclic-two-and-generated"
import "280-book-equivalence-maps"

{` Chapter 5 (actions.tex), xca:AutC3: the action S ↦ G(S) of Σ_2 on C_3
   (ex:S2-acts-on-C3, modules 568/572) gives an identification Σ_2 = Aut(C_3).

   The action, as a pointed map into the component of C_3 in Group, is
   b : BΣ_2 → BAut(C_3) ≡ Group_(C_3), S ↦ (G(S), ‖C_3 = G(S)‖), pointed by
   the identification G(Fin 2) = C_3 of ex:S2-acts-on-C3 (s2c3_group_c3_path).
   We show that b is an equivalence (connected_map_equiv_from_loops), so b is
   (the classifying map of) a group isomorphism Σ_2 ≅ Aut(C_3), hence a path
   Σ_2 = Aut(C_3) in Group. On loops, b is ap_G : (sh = sh) → (G(sh) = G(sh)).

   (B) ap_G is injective. The Σ_2-set S ↦ USym G(S) is the pullback along G of
   H ↦ USym H (transport_ap), and e_S(u) ≔ transport along the carrier path
   of u of inl 0 is a map of Σ_2-sets USym G(S) → 1 ⊔ S (naturality by
   path induction). The symmetry u₀ of (1 ⊔ Fin 2, f) given by f_yes has
   e(u₀) = inr yes; so e(p · u₀) = inr (p · yes) for p : USym Σ_2, and
   ap_G p = ap_G q forces p · yes = q · yes, hence p = q (evaluation at
   yes = 0 is an equivalence USym Σ_2 ≃ Fin 2, sigma2_usym_equiv, module 412).
   (C) ap_G is surjective: G(sh) = G(sh) injects into Fin 2 (module 573,
   transported along G(sh) = C_3), and refl, ap_G(swap) have different images. `}

def S2C3Plus (S : TwoElementSets) : Type ≔ Sum (Fin (suc. zero.)) (two_set_carrier S)

{` e_S : USym G(S) → 1 ⊔ S, evaluation at inl 0 of the carrier permutation. `}
def s2c3_eval_zero (S : TwoElementSets) (u : USym (s2c3_group S)) : S2C3Plus S
  ≔ transport SetTypes (X ↦ X .fst) (s2c3_one_plus S) (s2c3_one_plus S) (u .fst .fst) (inl. (inr. star.))

def s2c3_eval_natural_base (S : TwoElementSets) (u : USym (s2c3_group S))
  : Id (S2C3Plus S) (s2c3_eval_zero S (transport TwoElementSets (R ↦ USym (s2c3_group R)) S S (refl S) u))
      (transport TwoElementSets S2C3Plus S S (refl S) (s2c3_eval_zero S u))
  ≔ concat (S2C3Plus S) (s2c3_eval_zero S (transport TwoElementSets (R ↦ USym (s2c3_group R)) S S (refl S) u))
      (s2c3_eval_zero S u) (transport TwoElementSets S2C3Plus S S (refl S) (s2c3_eval_zero S u))
      (refl (s2c3_eval_zero S) (transport_refl TwoElementSets (R ↦ USym (s2c3_group R)) S u))
      (inverse (S2C3Plus S) (transport TwoElementSets S2C3Plus S S (refl S) (s2c3_eval_zero S u)) (s2c3_eval_zero S u)
        (transport_refl TwoElementSets S2C3Plus S (s2c3_eval_zero S u)))

{` e is a map of Σ_2-sets: e(p · u) = p · e(u). `}
def s2c3_eval_natural (S S' : TwoElementSets) (p : Id TwoElementSets S S') (u : USym (s2c3_group S))
  : Id (S2C3Plus S') (s2c3_eval_zero S' (transport TwoElementSets (R ↦ USym (s2c3_group R)) S S' p u))
      (transport TwoElementSets S2C3Plus S S' p (s2c3_eval_zero S u))
  ≔ J TwoElementSets S
      (S'' q ↦ Id (S2C3Plus S'') (s2c3_eval_zero S'' (transport TwoElementSets (R ↦ USym (s2c3_group R)) S S'' q u))
        (transport TwoElementSets S2C3Plus S S'' q (s2c3_eval_zero S u)))
      (s2c3_eval_natural_base S u) S' p

def s2c3_transport_inr_base (S : TwoElementSets) (y : two_set_carrier S)
  : Id (S2C3Plus S) (transport TwoElementSets S2C3Plus S S (refl S) (inr. y))
      (inr. (transport TwoElementSets two_set_carrier S S (refl S) y))
  ≔ concat (S2C3Plus S) (transport TwoElementSets S2C3Plus S S (refl S) (inr. y)) (inr. y)
      (inr. (transport TwoElementSets two_set_carrier S S (refl S) y))
      (transport_refl TwoElementSets S2C3Plus S (inr. y))
      (refl ((z ↦ inr. z) : two_set_carrier S → S2C3Plus S)
        (inverse (two_set_carrier S) (transport TwoElementSets two_set_carrier S S (refl S) y) y
          (transport_refl TwoElementSets two_set_carrier S y)))

def s2c3_transport_inr (S S' : TwoElementSets) (p : Id TwoElementSets S S') (y : two_set_carrier S)
  : Id (S2C3Plus S') (transport TwoElementSets S2C3Plus S S' p (inr. y))
      (inr. (transport TwoElementSets two_set_carrier S S' p y))
  ≔ J TwoElementSets S
      (S'' q ↦ Id (S2C3Plus S'') (transport TwoElementSets S2C3Plus S S'' q (inr. y))
        (inr. (transport TwoElementSets two_set_carrier S S'' q y)))
      (s2c3_transport_inr_base S y) S' p

{` The symmetry u₀ of (1 ⊔ Fin 2, f) given by f_yes: f_yes commutes with
   f_yes and with f_no = f_yes⁻¹. `}
def s2c3_fy_commutes
  : SActionCommutes (Fin two) S2C3Carrier S2C3Carrier (s2c3_move s2c3_std) (s2c3_move s2c3_std) s2c3_fy
  ≔ a ↦ match a [
  | inr. star. ↦ x ↦ refl (s2c3_fy (s2c3_fy x))
  | inl. (inr. star.) ↦ x ↦ concat S2C3Carrier (s2c3_fy (s2c3_fn x)) x (s2c3_fn (s2c3_fy x)) (s2c3_fy_fn x)
      (inverse S2C3Carrier (s2c3_fn (s2c3_fy x)) x (s2c3_fn_fy x))
  | inl. (inl. e) ↦ match e [] ]

def s2c3_fy_path : Id Type S2C3Carrier S2C3Carrier ≔ ua S2C3Carrier S2C3Carrier s2c3_fy_equiv

def s2c3_loop_snd : Id (s_action_family (Fin two)) s2c3_fy_path (s2c3_move s2c3_std) (s2c3_move s2c3_std)
  ≔ equiv_inverse_map (Id (s_action_family (Fin two)) s2c3_fy_path (s2c3_move s2c3_std) (s2c3_move s2c3_std))
      (SActionCommutes (Fin two) S2C3Carrier S2C3Carrier (s2c3_move s2c3_std) (s2c3_move s2c3_std) (s2c3_fy_path .trr))
      (s_action_pathover_equiv (Fin two) S2C3Carrier S2C3Carrier s2c3_fy_path (s2c3_move s2c3_std) (s2c3_move s2c3_std))
      s2c3_fy_commutes

def s2c3_loop : Id (S2C3Type s2c3_std) (s2c3_point s2c3_std) (s2c3_point s2c3_std)
  ≔ (set_types_path (s2c3_one_plus s2c3_std) (s2c3_one_plus s2c3_std) s2c3_fy_equiv, s2c3_loop_snd)

def s2c3_fy_symmetry : USym (s2c3_group s2c3_std)
  ≔ component_path (S2C3Type s2c3_std) (s2c3_point s2c3_std)
      (component_point (S2C3Type s2c3_std) (s2c3_point s2c3_std))
      (component_point (S2C3Type s2c3_std) (s2c3_point s2c3_std)) s2c3_loop

{` Litmus: e(u₀) = f_yes(inl 0) = inr yes. `}
def s2c3_eval_fy_symmetry : Id S2C3Carrier (s2c3_eval_zero s2c3_std s2c3_fy_symmetry) s2c3_yes
  ≔ refl s2c3_yes

{` e(p · u₀) = inr (p · yes). `}
def s2c3_eval_transport (p : USym (symmetric_group two))
  : Id S2C3Carrier
      (s2c3_eval_zero s2c3_std (transport TwoElementSets (R ↦ USym (s2c3_group R)) s2c3_std s2c3_std p s2c3_fy_symmetry))
      (inr. (permutation_action (standard_set two) p s2c3_fin2_yes))
  ≔ concat S2C3Carrier
      (s2c3_eval_zero s2c3_std (transport TwoElementSets (R ↦ USym (s2c3_group R)) s2c3_std s2c3_std p s2c3_fy_symmetry))
      (transport TwoElementSets S2C3Plus s2c3_std s2c3_std p s2c3_yes)
      (inr. (permutation_action (standard_set two) p s2c3_fin2_yes))
      (s2c3_eval_natural s2c3_std s2c3_std p s2c3_fy_symmetry)
      (s2c3_transport_inr s2c3_std s2c3_std p s2c3_fin2_yes)

{` Litmus: e(swap · u₀) = inr no, so swap · u₀ ≠ u₀. `}
def s2c3_eval_swap_transport
  : Id S2C3Carrier
      (s2c3_eval_zero s2c3_std
        (transport TwoElementSets (R ↦ USym (s2c3_group R)) s2c3_std s2c3_std sigma2_swap s2c3_fy_symmetry))
      s2c3_no
  ≔ s2c3_eval_transport sigma2_swap

def s2c3_inr_proj (x : S2C3Carrier) : Fin two ≔ match x [ inl. _ ↦ s2c3_fin2_yes | inr. y ↦ y ]

{` In Fin 2: a ≠ b and c ≠ b imply a = c. `}
def s2c3_fin2_third (a b c : Fin two) (hab : Not (Id (Fin two) a b)) (hcb : Not (Id (Fin two) c b))
  : Id (Fin two) a c
  ≔ concat (Fin two) a (fin2_swap b) c
      (fin2_distinct_other b a (r ↦ hab (inverse (Fin two) b a r)))
      (inverse (Fin two) c (fin2_swap b) (fin2_distinct_other b c (r ↦ hcb (inverse (Fin two) b c r))))

{` (B) ap_G is injective on loops of BΣ_2. `}
def s2c3_group_ap_injective
  : PathReflecting (USym (symmetric_group two)) (Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std))
      (map_path TwoElementSets Group s2c3_group s2c3_std s2c3_std)
  ≔ p q h ↦
    let act ≔ permutation_action (standard_set two) in
    let Gs ≔ s2c3_group s2c3_std in
    let tr : Id Group Gs Gs → USym Gs ≔ r ↦ transport Group USym Gs Gs r s2c3_fy_symmetry in
    let ev ≔ s2c3_eval_zero s2c3_std in
    let yes_inr : Id S2C3Carrier (inr. (act p s2c3_fin2_yes)) (inr. (act q s2c3_fin2_yes))
      ≔ concat S2C3Carrier (inr. (act p s2c3_fin2_yes)) (ev (tr (refl s2c3_group p))) (inr. (act q s2c3_fin2_yes))
          (inverse S2C3Carrier (ev (tr (refl s2c3_group p))) (inr. (act p s2c3_fin2_yes)) (s2c3_eval_transport p))
          (concat S2C3Carrier (ev (tr (refl s2c3_group p))) (ev (tr (refl s2c3_group q))) (inr. (act q s2c3_fin2_yes))
            (refl ev (refl tr h)) (s2c3_eval_transport q)) in
    let yes_eq : Id (Fin two) (act p s2c3_fin2_yes) (act q s2c3_fin2_yes) ≔ refl s2c3_inr_proj yes_inr in
    equivalence_injective (USym (symmetric_group two)) (Fin two) sigma2_usym_equiv p q yes_eq

{` The swap acts nontrivially on C_3 (litmus). `}
def s2c3_swap_acts_nontrivially
  (p : Id (Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std))
    (map_path TwoElementSets Group s2c3_group s2c3_std s2c3_std sigma2_swap) (refl (s2c3_group s2c3_std)))
  : Empty
  ≔ sigma2_swap_nontrivial (s2c3_group_ap_injective sigma2_swap (usym_unit (symmetric_group two)) p)

{` (C) ap_G is surjective. `}
def s2c3_group_aut_at_most_two : GroupAutAtMostTwo (s2c3_group s2c3_std)
  ≔ group_aut_at_most_two_transfer (s2c3_group s2c3_std) (cyclic_group_fin two) s2c3_group_c3_path
      cyclic_fin_three_aut_at_most_two

def s2c3_group_ap_surjective (l : Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std))
  : BookFiber (USym (symmetric_group two)) (Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std))
      (map_path TwoElementSets Group s2c3_group s2c3_std s2c3_std) l
  ≔ let Gs ≔ s2c3_group s2c3_std in
    let ι ≔ s2c3_group_aut_at_most_two .fst in
    let inj ≔ s2c3_group_aut_at_most_two .snd in
    let r : Id Group Gs Gs ≔ refl Gs in
    let w : Id Group Gs Gs ≔ map_path TwoElementSets Group s2c3_group s2c3_std s2c3_std sigma2_swap in
    let differ : Not (Id (Fin two) (ι w) (ι r))
      ≔ k ↦ s2c3_swap_acts_nontrivially (inj w r k) in
    match fin_decidable_equality two (ι l) (ι r) [
    | inl. e ↦ (usym_unit (symmetric_group two), inj l r e)
    | inr. ne ↦ (sigma2_swap, inj l w (s2c3_fin2_third (ι l) (ι r) (ι w) ne differ)) ]

{` The action as a map into the component of C_3: S ↦ (G(S), ‖C_3 = G(S)‖). `}
def s2_aut_c3_map (S : TwoElementSets) : NativeComponent Group (cyclic_group_fin two)
  ≔ (s2c3_group S,
     mere_rec (Id TwoElementSets s2c3_std S) (Mere (Id Group (cyclic_group_fin two) (s2c3_group S)))
       (mere_isprop (Id Group (cyclic_group_fin two) (s2c3_group S)))
       (q ↦ mere (Id Group (cyclic_group_fin two) (s2c3_group S))
         (concat Group (cyclic_group_fin two) (s2c3_group s2c3_std) (s2c3_group S)
           (inverse Group (s2c3_group s2c3_std) (cyclic_group_fin two) s2c3_group_c3_path)
           (refl s2c3_group q)))
       (bg_connected (symmetric_group two) .snd s2c3_std S))

def s2_aut_c3_ap_injective
  : PathReflecting (USym (symmetric_group two))
      (Id (NativeComponent Group (cyclic_group_fin two)) (s2_aut_c3_map s2c3_std) (s2_aut_c3_map s2c3_std))
      (map_path TwoElementSets (NativeComponent Group (cyclic_group_fin two)) s2_aut_c3_map s2c3_std s2c3_std)
  ≔ p q h ↦
    s2c3_group_ap_injective p q
      (refl ((m ↦ m .fst)
        : Id (NativeComponent Group (cyclic_group_fin two)) (s2_aut_c3_map s2c3_std) (s2_aut_c3_map s2c3_std)
          → Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std)) h)

{` On loops, the action map is an equivalence. `}
def s2_aut_c3_ap_equiv
  : BookIsEquiv (USym (symmetric_group two))
      (Id (NativeComponent Group (cyclic_group_fin two)) (s2_aut_c3_map s2c3_std) (s2_aut_c3_map s2c3_std))
      (map_path TwoElementSets (NativeComponent Group (cyclic_group_fin two)) s2_aut_c3_map s2c3_std s2c3_std)
  ≔ let NC ≔ NativeComponent Group (cyclic_group_fin two) in
    let b0 ≔ s2_aut_c3_map s2c3_std in
    let F ≔ map_path TwoElementSets NC s2_aut_c3_map s2c3_std s2c3_std in
    l ↦
    let fib ≔ s2c3_group_ap_surjective (l .fst) in
    let center : BookFiber (USym (symmetric_group two)) (Id NC b0 b0) F l
      ≔ (fib .fst,
         equivalence_injective (Id NC b0 b0) (Id Group (s2c3_group s2c3_std) (s2c3_group s2c3_std))
           (component_path_equiv Group (cyclic_group_fin two) b0 b0) l (F (fib .fst)) (fib .snd)) in
    (center, v ↦ book_fiber_prop_of_injective (USym (symmetric_group two)) (Id NC b0 b0)
       (component_groupoid Group group_groupoid (cyclic_group_fin two) b0 b0) F s2_aut_c3_ap_injective l center v)

{` xca:AutC3. The action map BΣ_2 → BAut(C_3) is an equivalence. `}
def s2_aut_c3_map_equiv
  : BookIsEquiv TwoElementSets (NativeComponent Group (cyclic_group_fin two)) s2_aut_c3_map
  ≔ native_connected_map_equiv_from_loops_book_map TwoElementSets (NativeComponent Group (cyclic_group_fin two))
      s2_aut_c3_map (bg_connected (symmetric_group two)) (bg_connected (group_aut (cyclic_group_fin two))) s2c3_std
      s2_aut_c3_ap_equiv

def s2_aut_c3_pointed_map : BookPointedMap (BG (symmetric_group two)) (BG (group_aut (cyclic_group_fin two)))
  ≔ (s2_aut_c3_map,
     component_path Group (cyclic_group_fin two) (component_point Group (cyclic_group_fin two)) (s2_aut_c3_map s2c3_std)
       (inverse Group (s2c3_group s2c3_std) (cyclic_group_fin two) s2c3_group_c3_path))

def s2_aut_c3_pointed_equiv : BookPointedEquiv (BG (symmetric_group two)) (BG (group_aut (cyclic_group_fin two)))
  ≔ (s2_aut_c3_pointed_map, s2_aut_c3_map_equiv)

def s2_aut_c3_iso : GroupIso (symmetric_group two) (group_aut (cyclic_group_fin two))
  ≔ (mkhom (symmetric_group two) (group_aut (cyclic_group_fin two)) s2_aut_c3_pointed_map, s2_aut_c3_map_equiv)

{` xca:AutC3: Σ_2 = Aut(C_3). `}
def s2_aut_c3_path : Id Group (symmetric_group two) (group_aut (cyclic_group_fin two))
  ≔ group_path_from_iso (symmetric_group two) (group_aut (cyclic_group_fin two)) s2_aut_c3_iso

{` Litmus: the classifying map of the isomorphism is the action S ↦ G(S). `}
def s2_aut_c3_classifying (S : TwoElementSets)
  : Id Group (hom_function (symmetric_group two) (group_aut (cyclic_group_fin two)) (s2_aut_c3_iso .fst) S .fst)
      (s2_acts_on_c3 S)
  ≔ refl (s2c3_group S)

{` Litmus: Aut(C_3) has exactly two symmetries. `}
def aut_c3_usym_fin_two : Equiv (USym (group_aut (cyclic_group_fin two))) (Fin two)
  ≔ compose_equiv (USym (group_aut (cyclic_group_fin two))) (USym (symmetric_group two)) (Fin two)
      (transport_equiv (USym (group_aut (cyclic_group_fin two))) (USym (symmetric_group two))
        (refl USym (inverse Group (symmetric_group two) (group_aut (cyclic_group_fin two)) s2_aut_c3_path)))
      sigma2_usym_equiv
