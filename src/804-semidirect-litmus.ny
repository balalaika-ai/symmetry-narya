export "803-semidirect-kernel"
export "810-wreath-products"
export "505-gset-core-litmus"
export "412-symmetric-group-two"

{` Litmus checks for the semidirect product (congp.tex sec:Semidirect-products).

   (1) An action given by the trivial homomorphism G → Aut(H) yields the
       product G × H (the trivial action itself is checked in 800 and 802).
   (2) A non-abelian semidirect product with abelian G: Σ_2 acting on
       Aut_{S → BΣ_2}(const) for S : BΣ_2 (S ↦ the 2-element set S itself),
       i.e. G ⋉ H^X = wreath_product Σ_2 Σ_2 X of module 810 with the
       standard Σ_2-set X (module 505). The symmetries s(σ) and j(q') do not
       commute, where σ is the swap of Fin 2 and q' : USym H(sh) is the loop
       of the constant function given by (σ, refl) on (0, 1).
   (3) The multiplication formula evaluated on this pair:
       j(q') · s(σ) ↦ (σ, q'^σ) with q'^σ = (refl, σ) pointwise, and
       s(σ) · j(q') ↦ (σ, q') with q' = (σ, refl). `}

{` (1) The trivial homomorphism G → Aut(H) (constant at the shape of
   Aut(H)) gives the trivial action t ↦ H judgmentally. `}
def sdp_trivial_aut_hom (G H : Group) : GroupHom G (group_aut H)
  ≔ mkhom G (group_aut H) (_ ↦ shape (group_aut H), refl (shape (group_aut H)))

def sdp_trivial_aut_hom_action (G H : Group)
  : Id (BG G .carrier → Group) (hom_aut_action G H (sdp_trivial_aut_hom G H)) (_ ↦ H)
  ≔ refl ((_ ↦ H) : BG G .carrier → Group)

def sdp_trivial_aut_hom_product (G H : Group)
  : Id Group (semidirect_product_hom G H (sdp_trivial_aut_hom G H)) (product_group G H)
  ≔ semidirect_trivial_product_path G H

{` Evaluation of the action q'^p for actions of the form
   t ↦ Aut_{A(t) → B}(const_b): the value of q'^p at a : A(t) is the value of
   q' at the transport of a along p. By induction on p. `}
def sdp_component_loop_refl_value (X : Type) (A : X → Type) (B : Type) (b : B) (t : X)
  (q' : Id (NativeComponent (A t → B) (_ ↦ b)) (component_point (A t → B) (_ ↦ b)) (component_point (A t → B) (_ ↦ b)))
  (a : A t)
  : Id (Id B b b)
      (section_loop_action X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b)) t t
        (refl t) q' .fst (refl a))
      (q' .fst (refl a))
  ≔ refl ((w ↦ w .fst (refl a))
          : Id (NativeComponent (A t → B) (_ ↦ b)) (component_point (A t → B) (_ ↦ b))
              (component_point (A t → B) (_ ↦ b)) → Id B b b)
        (section_loop_action_refl X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b))
          t q')

{` Values of a path of constant functions along a path of arguments. `}
def sdp_const_fun_path_ap (A B : Type) (b : B) (F : Id (A → B) (_ ↦ b) (_ ↦ b)) (a a' : A) (e : Id A a a')
  : Id (Id B b b) (F (refl a)) (F (refl a'))
  ≔ refl ((y ↦ F (refl y)) : A → Id B b b) e

{` Values of loops of a constant function in a component, along a path of loops. `}
def sdp_component_loop_eval_path (A B : Type) (b : B)
  (w w' : Id (NativeComponent (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b)))
  (s : Id (Id (NativeComponent (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b))) w w')
  (a : A)
  : Id (Id B b b) (w .fst (refl a)) (w' .fst (refl a))
  ≔ refl ((v ↦ v .fst (refl a))
          : Id (NativeComponent (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b)) (component_point (A → B) (_ ↦ b))
            → Id B b b) s

def sdp_function_loop_action_eval_base (X : Type) (A : X → Type) (B : Type) (b : B) (t : X)
  (q' : Id (NativeComponent (A t → B) (_ ↦ b)) (component_point (A t → B) (_ ↦ b)) (component_point (A t → B) (_ ↦ b)))
  (a : A t)
  : Id (Id B b b)
      (section_loop_action X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b)) t t
        (refl t) q' .fst (refl a))
      (q' .fst (refl (transport X A t t (refl t) a)))
  ≔ concat (Id B b b)
      (section_loop_action X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b)) t t
        (refl t) q' .fst (refl a))
      (q' .fst (refl a))
      (q' .fst (refl (transport X A t t (refl t) a)))
      (sdp_component_loop_refl_value X A B b t q' a)
      (sdp_const_fun_path_ap (A t) B b (q' .fst) a (transport X A t t (refl t) a)
        (inverse (A t) (transport X A t t (refl t) a) a (transport_refl X A t a)))

def sdp_function_loop_action_eval (X : Type) (A : X → Type) (B : Type) (b : B) (t t' : X) (p : Id X t t')
  (q' : Id (NativeComponent (A t' → B) (_ ↦ b)) (component_point (A t' → B) (_ ↦ b)) (component_point (A t' → B) (_ ↦ b)))
  (a : A t)
  : Id (Id B b b)
      (section_loop_action X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b)) t t'
        p q' .fst (refl a))
      (q' .fst (refl (transport X A t t' p a)))
  ≔ J X t (t' p ↦ (q' : Id (NativeComponent (A t' → B) (_ ↦ b)) (component_point (A t' → B) (_ ↦ b))
          (component_point (A t' → B) (_ ↦ b))) (a : A t)
        → Id (Id B b b)
            (section_loop_action X (z ↦ NativeComponent (A z → B) (_ ↦ b)) (z ↦ component_point (A z → B) (_ ↦ b))
              t t' p q' .fst (refl a))
            (q' .fst (refl (transport X A t t' p a))))
      (q' a ↦ sdp_function_loop_action_eval_base X A B b t q' a) t' p q' a

{` (2) The example: G ≔ Σ_2, X ≔ the standard Σ_2-set, H ≔ Σ_2^X. `}
def sdp_litmus_action : BG (symmetric_group two) .carrier → Group
  ≔ wreath_power_action (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two)

def sdp_litmus_group : Group ≔ semidirect_product (symmetric_group two) sdp_litmus_action

def sdp_litmus_group_wreath
  : Id Group sdp_litmus_group
      (wreath_product (symmetric_group two) (symmetric_group two) (standard_symmetric_gset two))
  ≔ refl sdp_litmus_group

def sdp_litmus_loops : Fin two → USym (symmetric_group two)
  ≔ [ inr. _ ↦ sigma2_swap | inl. _ ↦ usym_unit (symmetric_group two) ]

{` q' : the symmetry of the constant function Fin 2 → BΣ_2 given by
   σ at 0 and refl at 1. `}
def sdp_litmus_loop : USym (sdp_litmus_action (shape (symmetric_group two)))
  ≔ component_path (Fin two → BG (symmetric_group two) .carrier) (wreath_constant_shape (symmetric_group two) (Fin two))
      (component_point (Fin two → BG (symmetric_group two) .carrier) (wreath_constant_shape (symmetric_group two) (Fin two)))
      (component_point (Fin two → BG (symmetric_group two) .carrier) (wreath_constant_shape (symmetric_group two) (Fin two)))
      (funext (Fin two) (_ ↦ BG (symmetric_group two) .carrier) (wreath_constant_shape (symmetric_group two) (Fin two))
        (wreath_constant_shape (symmetric_group two) (Fin two)) sdp_litmus_loops)

def sdp_litmus_loop_value (x : Fin two)
  : Id (USym (symmetric_group two)) (sdp_litmus_loop .fst (refl x)) (sdp_litmus_loops x)
  ≔ inverse (USym (symmetric_group two)) (sdp_litmus_loops x) (sdp_litmus_loop .fst (refl x))
      (funext_beta (Fin two) (_ ↦ BG (symmetric_group two) .carrier) (wreath_constant_shape (symmetric_group two) (Fin two))
        (wreath_constant_shape (symmetric_group two) (Fin two)) sdp_litmus_loops x)

{` q'^σ evaluated at x is q'(σ(x)). `}
def sdp_litmus_action_value (x : Fin two)
  : Id (USym (symmetric_group two))
      (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop .fst (refl x))
      (sdp_litmus_loops (fin2_swap x))
  ≔ concat (USym (symmetric_group two))
      (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop .fst (refl x))
      (sdp_litmus_loop .fst (refl (fin2_swap x)))
      (sdp_litmus_loops (fin2_swap x))
      (sdp_function_loop_action_eval (BG (symmetric_group two) .carrier) (z ↦ z .fst .fst)
        (BG (symmetric_group two) .carrier) (shape (symmetric_group two)) (shape (symmetric_group two))
        (shape (symmetric_group two)) sigma2_swap sdp_litmus_loop x)
      (sdp_litmus_loop_value (fin2_swap x))

{` s(σ) and j(q') in G ⋉ H. `}
def sdp_litmus_s : USym sdp_litmus_group
  ≔ usym_hom (symmetric_group two) sdp_litmus_group (semidirect_section (symmetric_group two) sdp_litmus_action)
      sigma2_swap

def sdp_litmus_j : USym sdp_litmus_group
  ≔ usym_hom (sdp_litmus_action (shape (symmetric_group two))) sdp_litmus_group
      (semidirect_inclusion (symmetric_group two) sdp_litmus_action) sdp_litmus_loop

{` (3) j(q') · s(σ) corresponds to (1 · σ, (q'^σ) · 1) and s(σ) · j(q') to
   (σ · 1, (1^1) · q'). `}
def sdp_litmus_pair_js
  : Id (Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (usym_unit (symmetric_group two), sdp_litmus_loop)
        (sigma2_swap, usym_unit (sdp_litmus_action (shape (symmetric_group two)))))
  ≔ concat (Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action sdp_litmus_j)
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action sdp_litmus_s))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (usym_unit (symmetric_group two), sdp_litmus_loop)
        (sigma2_swap, usym_unit (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_usym_mul (symmetric_group two) sdp_litmus_action sdp_litmus_j sdp_litmus_s)
      (refl (semidirect_pair_mul (symmetric_group two) sdp_litmus_action)
        (semidirect_usym_pair_inclusion (symmetric_group two) sdp_litmus_action sdp_litmus_loop)
        (semidirect_usym_pair_section (symmetric_group two) sdp_litmus_action sigma2_swap))

def sdp_litmus_pair_sj
  : Id (Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (sigma2_swap, usym_unit (sdp_litmus_action (shape (symmetric_group two))))
        (usym_unit (symmetric_group two), sdp_litmus_loop))
  ≔ concat (Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action sdp_litmus_s)
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action sdp_litmus_j))
      (semidirect_pair_mul (symmetric_group two) sdp_litmus_action
        (sigma2_swap, usym_unit (sdp_litmus_action (shape (symmetric_group two))))
        (usym_unit (symmetric_group two), sdp_litmus_loop))
      (semidirect_usym_mul (symmetric_group two) sdp_litmus_action sdp_litmus_s sdp_litmus_j)
      (refl (semidirect_pair_mul (symmetric_group two) sdp_litmus_action)
        (semidirect_usym_pair_section (symmetric_group two) sdp_litmus_action sigma2_swap)
        (semidirect_usym_pair_inclusion (symmetric_group two) sdp_litmus_action sdp_litmus_loop))

def sdp_litmus_js_fst
  : Id (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s) .fst)
      sigma2_swap
  ≔ concat (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s) .fst)
      (usym_mul (symmetric_group two) (usym_unit (symmetric_group two)) sigma2_swap)
      sigma2_swap
      (refl ((a ↦ a .fst)
          : Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two))))
            → USym (symmetric_group two))
        sdp_litmus_pair_js)
      (concat_p1 (BG (symmetric_group two) .carrier) (shape (symmetric_group two)) (shape (symmetric_group two)) sigma2_swap)

def sdp_litmus_js_snd
  : Id (USym (sdp_litmus_action (shape (symmetric_group two))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s) .snd)
      (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop)
  ≔ concat (USym (sdp_litmus_action (shape (symmetric_group two))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s) .snd)
      (usym_mul (sdp_litmus_action (shape (symmetric_group two)))
        (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop)
        (usym_unit (sdp_litmus_action (shape (symmetric_group two)))))
      (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop)
      (refl ((a ↦ a .snd)
          : Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two))))
            → USym (sdp_litmus_action (shape (symmetric_group two))))
        sdp_litmus_pair_js)
      (concat_1p (BG (sdp_litmus_action (shape (symmetric_group two))) .carrier)
        (shape (sdp_litmus_action (shape (symmetric_group two))))
        (shape (sdp_litmus_action (shape (symmetric_group two))))
        (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop))

def sdp_litmus_sj_snd
  : Id (USym (sdp_litmus_action (shape (symmetric_group two))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j) .snd)
      sdp_litmus_loop
  ≔ concat (USym (sdp_litmus_action (shape (symmetric_group two))))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j) .snd)
      (usym_mul (sdp_litmus_action (shape (symmetric_group two)))
        (semidirect_loop_action (symmetric_group two) sdp_litmus_action (usym_unit (symmetric_group two))
          (usym_unit (sdp_litmus_action (shape (symmetric_group two)))))
        sdp_litmus_loop)
      sdp_litmus_loop
      (refl ((a ↦ a .snd)
          : Product (USym (symmetric_group two)) (USym (sdp_litmus_action (shape (symmetric_group two))))
            → USym (sdp_litmus_action (shape (symmetric_group two))))
        sdp_litmus_pair_sj)
      (concat (USym (sdp_litmus_action (shape (symmetric_group two))))
        (usym_mul (sdp_litmus_action (shape (symmetric_group two)))
          (semidirect_loop_action (symmetric_group two) sdp_litmus_action (usym_unit (symmetric_group two))
            (usym_unit (sdp_litmus_action (shape (symmetric_group two)))))
          sdp_litmus_loop)
        (usym_mul (sdp_litmus_action (shape (symmetric_group two)))
          (usym_unit (sdp_litmus_action (shape (symmetric_group two)))) sdp_litmus_loop)
        sdp_litmus_loop
        (refl ((w ↦ usym_mul (sdp_litmus_action (shape (symmetric_group two))) w sdp_litmus_loop)
            : USym (sdp_litmus_action (shape (symmetric_group two))) → USym (sdp_litmus_action (shape (symmetric_group two))))
          (semidirect_loop_action_unit (symmetric_group two) sdp_litmus_action
            (usym_unit (sdp_litmus_action (shape (symmetric_group two))))))
        (concat_p1 (BG (sdp_litmus_action (shape (symmetric_group two))) .carrier)
          (shape (sdp_litmus_action (shape (symmetric_group two))))
          (shape (sdp_litmus_action (shape (symmetric_group two)))) sdp_litmus_loop))

{` The second components evaluated pointwise: j(q') · s(σ) has (refl, σ),
   s(σ) · j(q') has (σ, refl). `}
def sdp_litmus_js_value (x : Fin two)
  : Id (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s)
        .snd .fst (refl x))
      (sdp_litmus_loops (fin2_swap x))
  ≔ concat (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s)
        .snd .fst (refl x))
      (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop .fst (refl x))
      (sdp_litmus_loops (fin2_swap x))
      (sdp_component_loop_eval_path (Fin two) (BG (symmetric_group two) .carrier) (shape (symmetric_group two))
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s) .snd)
        (semidirect_loop_action (symmetric_group two) sdp_litmus_action sigma2_swap sdp_litmus_loop)
        sdp_litmus_js_snd x)
      (sdp_litmus_action_value x)

def sdp_litmus_js_value_zero
  : Id (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s)
        .snd .fst (refl fin2_zero))
      (usym_unit (symmetric_group two))
  ≔ sdp_litmus_js_value fin2_zero

def sdp_litmus_js_value_one
  : Id (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s)
        .snd .fst (refl fin2_one))
      sigma2_swap
  ≔ sdp_litmus_js_value fin2_one

def sdp_litmus_sj_value (x : Fin two)
  : Id (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j)
        .snd .fst (refl x))
      (sdp_litmus_loops x)
  ≔ concat (USym (symmetric_group two))
      (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j)
        .snd .fst (refl x))
      (sdp_litmus_loop .fst (refl x))
      (sdp_litmus_loops x)
      (sdp_component_loop_eval_path (Fin two) (BG (symmetric_group two) .carrier) (shape (symmetric_group two))
        (semidirect_usym_pair (symmetric_group two) sdp_litmus_action (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j) .snd)
        sdp_litmus_loop sdp_litmus_sj_snd x)
      (sdp_litmus_loop_value x)

{` (2) s(σ) and j(q') do not commute, although G = Σ_2 is abelian
   (sigma2_abelian); hence Σ_2 ⋉ H is not abelian. `}
def sdp_litmus_noncommuting
  (h : Id (USym sdp_litmus_group) (usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s)
    (usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j)) : Empty
  ≔ let js ≔ usym_mul sdp_litmus_group sdp_litmus_j sdp_litmus_s in
    let sj ≔ usym_mul sdp_litmus_group sdp_litmus_s sdp_litmus_j in
    let snd : USym sdp_litmus_group → USym (sdp_litmus_action (shape (symmetric_group two)))
      ≔ d ↦ semidirect_usym_pair (symmetric_group two) sdp_litmus_action d .snd in
    sigma2_swap_nontrivial
      (calc
        sigma2_swap = snd sj .fst (refl fin2_zero)
          by inverse (USym (symmetric_group two)) (snd sj .fst (refl fin2_zero)) sigma2_swap
               (sdp_litmus_sj_value fin2_zero)
        = snd js .fst (refl fin2_zero)
          by sdp_component_loop_eval_path (Fin two) (BG (symmetric_group two) .carrier) (shape (symmetric_group two))
               (snd sj) (snd js) (refl snd (inverse (USym sdp_litmus_group) js sj h)) fin2_zero
        = usym_unit (symmetric_group two) by sdp_litmus_js_value_zero ∎)

def sdp_litmus_not_abelian (h : IsAbelian sdp_litmus_group) : Empty
  ≔ sdp_litmus_noncommuting (h sdp_litmus_j sdp_litmus_s)
