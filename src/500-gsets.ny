export "404-group-examples"

{` Chapter 5 (actions.tex), section "Group actions (G-sets)".

   Conventions of this chapter.
   - A G-set is a family X : BG÷ → Set, with Set = SetTypes = Σ Type isSet;
     X z .fst is the set X(z) and X (shape G) .fst the underlying set.
   - The action of a path p : z = w in BG is transport in the family
     u ↦ X u .fst (the book's X(p) = trp^X(p) and p ·_X a = X(p)(a)).
   - For g : USym G this is a LEFT action for the book's multiplication
     g · h = usym_mul G g h = concat h g (h first, then g):
     (g · h) ·_X a = g ·_X (h ·_X a)  (gset_act_mul), e ·_X a = a (gset_act_unit).
   - The unit law and composition law are typal (J has only a typal β-rule). `}

{` def:Gset. The type of G-sets, GSet ≔ (BG → Set). `}
def GSet (G : Group) : Type ≔ BG G .carrier → SetTypes

{` The underlying type family z ↦ X(z) of a G-set. `}
def gset_family (G : Group) (X : GSet G) : BG G .carrier → Type ≔ z ↦ X z .fst

def gset_family_set (G : Group) (X : GSet G) (z : BG G .carrier) : isSet (X z .fst) ≔ X z .snd

{` The underlying set X(sh_G). `}
def gset_underlying (G : Group) (X : GSet G) : Type ≔ X (shape G) .fst

def gset_underlying_set (G : Group) (X : GSet G) : isSet (gset_underlying G X) ≔ X (shape G) .snd

{` def:Gset. For p : z = w, X(p) : X(z) → X(w) is transport and
   p ·_X a ≔ X(p)(a). `}
def gset_act (G : Group) (X : GSet G) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (a : X z .fst) : X w .fst
  ≔ transport (BG G .carrier) (u ↦ X u .fst) z w p a

{` The action of a symmetry g : USym G on the underlying set. `}
def gset_usym_act (G : Group) (X : GSet G) (g : USym G) (a : gset_underlying G X) : gset_underlying G X
  ≔ gset_act G X (shape G) (shape G) g a

{` X(p) is an equivalence X(z) ≃ X(w) (transport along the path of types
   X(p) = ap_X(p)); its map is literally gset_act. `}
def gset_act_equiv (G : Group) (X : GSet G) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  : Equiv (X z .fst) (X w .fst)
  ≔ transport_equiv (X z .fst) (X w .fst) (refl ((u ↦ X u .fst) : BG G .carrier → Type) p)

def gset_act_equiv_map (G : Group) (X : GSet G) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (a : X z .fst) : Id (X w .fst) (gset_act_equiv G X z w p .map a) (gset_act G X z w p a)
  ≔ refl (gset_act G X z w p a)

{` Functoriality of the action along paths: refl acts trivially and a
   composite path acts as the composite of the actions. `}
def gset_act_refl (G : Group) (X : GSet G) (z : BG G .carrier) (a : X z .fst)
  : Id (X z .fst) (gset_act G X z z (refl z) a) a
  ≔ transport_refl (BG G .carrier) (u ↦ X u .fst) z a

def gset_act_concat (G : Group) (X : GSet G) (z w v : BG G .carrier)
  (p : Id (BG G .carrier) z w) (q : Id (BG G .carrier) w v) (a : X z .fst)
  : Id (X v .fst) (gset_act G X z v (concat (BG G .carrier) z w v p q) a)
      (gset_act G X w v q (gset_act G X z w p a))
  ≔ transport_concat (BG G .carrier) (u ↦ X u .fst) z w v p q a

{` p⁻¹ · (p · a) = a and p · (p⁻¹ · b) = b. `}
def gset_act_inverse_left (G : Group) (X : GSet G) (z w : BG G .carrier)
  (p : Id (BG G .carrier) z w) (a : X z .fst)
  : Id (X z .fst) (gset_act G X w z (inverse (BG G .carrier) z w p) (gset_act G X z w p a)) a
  ≔ J (BG G .carrier) z
      (w p ↦ Id (X z .fst) (gset_act G X w z (inverse (BG G .carrier) z w p) (gset_act G X z w p a)) a)
      (concat (X z .fst)
        (gset_act G X z z (inverse (BG G .carrier) z z (refl z)) (gset_act G X z z (refl z) a))
        (gset_act G X z z (refl z) (gset_act G X z z (refl z) a)) a
        (refl ((r ↦ gset_act G X z z r (gset_act G X z z (refl z) a))
            : Id (BG G .carrier) z z → X z .fst)
          (inverse_refl (BG G .carrier) z))
        (concat (X z .fst) (gset_act G X z z (refl z) (gset_act G X z z (refl z) a))
          (gset_act G X z z (refl z) a) a
          (gset_act_refl G X z (gset_act G X z z (refl z) a)) (gset_act_refl G X z a)))
      w p

def gset_act_inverse_right (G : Group) (X : GSet G) (z w : BG G .carrier)
  (p : Id (BG G .carrier) z w) (b : X w .fst)
  : Id (X w .fst) (gset_act G X z w p (gset_act G X w z (inverse (BG G .carrier) z w p) b)) b
  ≔ J (BG G .carrier) z
      (w p ↦ (b : X w .fst) →
        Id (X w .fst) (gset_act G X z w p (gset_act G X w z (inverse (BG G .carrier) z w p) b)) b)
      (b ↦ concat (X z .fst)
        (gset_act G X z z (refl z) (gset_act G X z z (inverse (BG G .carrier) z z (refl z)) b))
        (gset_act G X z z (refl z) (gset_act G X z z (refl z) b)) b
        (refl ((r ↦ gset_act G X z z (refl z) (gset_act G X z z r b))
            : Id (BG G .carrier) z z → X z .fst)
          (inverse_refl (BG G .carrier) z))
        (concat (X z .fst) (gset_act G X z z (refl z) (gset_act G X z z (refl z) b))
          (gset_act G X z z (refl z) b) b
          (gset_act_refl G X z (gset_act G X z z (refl z) b)) (gset_act_refl G X z b)))
      w p b

{` The group action laws on the underlying set, in the book's orientation:
   e · a = a and (g · h) · a = g · (h · a), with g · h = usym_mul G g h. `}
def gset_act_unit (G : Group) (X : GSet G) (a : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X (usym_unit G) a) a
  ≔ gset_act_refl G X (shape G) a

def gset_act_mul (G : Group) (X : GSet G) (g h : USym G) (a : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X (usym_mul G g h) a)
      (gset_usym_act G X g (gset_usym_act G X h a))
  ≔ gset_act_concat G X (shape G) (shape G) (shape G) h g a

def gset_act_inv_left (G : Group) (X : GSet G) (g : USym G) (a : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X (usym_inv G g) (gset_usym_act G X g a)) a
  ≔ gset_act_inverse_left G X (shape G) (shape G) g a

def gset_act_inv_right (G : Group) (X : GSet G) (g : USym G) (a : gset_underlying G X)
  : Id (gset_underlying G X) (gset_usym_act G X g (gset_usym_act G X (usym_inv G g) a)) a
  ≔ gset_act_inverse_right G X (shape G) (shape G) g a

{` def:trivGset. triv_G S (z) ≔ S for all z : BG. Its action is the
   identity (transport in a constant family, a typal law). `}
def gset_trivial (G : Group) (S : SetTypes) : GSet G ≔ _ ↦ S

def gset_trivial_act (G : Group) (S : SetTypes) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (a : S .fst) : Id (S .fst) (gset_act G (gset_trivial G S) z w p a) a
  ≔ transport_constant (BG G .carrier) (S .fst) z w p a

{` def:principaltorsor and eq:pathsp. P_y(z) ≔ (y = z) and the principal
   G-torsor P_G ≔ P_{sh_G}, so P_G(z) ≡ (sh_G = z). `}
def gset_paths (G : Group) (y : BG G .carrier) : GSet G
  ≔ z ↦ (Id (BG G .carrier) y z, bg_groupoid G y z)

def principal_gset (G : Group) : GSet G ≔ gset_paths G (shape G)

{` P_G(sh_G) ≡ USym G (by definition). `}
def principal_gset_underlying (G : Group) : Id Type (gset_underlying G (principal_gset G)) (USym G)
  ≔ refl (USym G)

{` Footnote to def:Gset: on P_y the action is path composition,
   p ·_{P_y} q = concat q p (the book's p q), definitionally. `}
def gset_paths_act (G : Group) (y z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (q : Id (BG G .carrier) y z)
  : Id (Id (BG G .carrier) y w) (gset_act G (gset_paths G y) z w p q) (concat (BG G .carrier) y z w q p)
  ≔ refl (concat (BG G .carrier) y z w q p)

{` On the underlying set USym G of P_G the action is left multiplication:
   g ·_{P_G} h = g · h (usym_mul), definitionally. `}
def principal_gset_act (G : Group) (g h : USym G)
  : Id (USym G) (gset_usym_act G (principal_gset G) g h) (usym_mul G g h)
  ≔ refl (usym_mul G g h)

{` def:adjointrep. Ad_G(z) ≔ (z = z). `}
def adjoint_gset (G : Group) : GSet G ≔ z ↦ (Id (BG G .carrier) z z, bg_groupoid G z z)

{` ft:adjoint-transport. Ad_G(p)(q) = p q p⁻¹ in the book's notation,
   i.e. concat p⁻¹ (concat q p) (first p⁻¹, then q, then p). `}
def adjoint_gset_act (G : Group) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (q : Id (BG G .carrier) z z)
  : Id (Id (BG G .carrier) w w) (gset_act G (adjoint_gset G) z w p q)
      (concat (BG G .carrier) w z w (inverse (BG G .carrier) z w p) (concat (BG G .carrier) z z w q p))
  ≔ let B ≔ BG G .carrier in
    concat (Id B w w) (gset_act G (adjoint_gset G) z w p q)
      (concat B w z w (concat B w z z (inverse B z w p) q) p)
      (concat B w z w (inverse B z w p) (concat B z z w q p))
      (transport_loop_family B z w p q)
      (concat_assoc B w z z w (inverse B z w p) q p)

{` On the underlying set USym G: g ·_{Ad} h = g h g⁻¹ = usym_mul g (usym_mul h g⁻¹). `}
def adjoint_gset_usym_act (G : Group) (g h : USym G)
  : Id (USym G) (gset_usym_act G (adjoint_gset G) g h)
      (usym_mul G g (usym_mul G h (usym_inv G g)))
  ≔ transport_loop_family (BG G .carrier) (shape G) (shape G) g h

{` def:map-of-Gsets. Hom_G(X, Y) ≔ Π_{z:BG} (X(z) → Y(z)). `}
def GSetHom (G : Group) (X Y : GSet G) : Type ≔ (z : BG G .carrier) → X z .fst → Y z .fst

def gset_hom_set (G : Group) (X Y : GSet G) : isSet (GSetHom G X Y)
  ≔ pi_set (BG G .carrier) (z ↦ X z .fst → Y z .fst)
      (z ↦ pi_set (X z .fst) (_ ↦ Y z .fst) (_ ↦ Y z .snd))

def gset_hom_id (G : Group) (X : GSet G) : GSetHom G X X ≔ z x ↦ x

{` Composition g ∘ f (f first). `}
def gset_hom_compose (G : Group) (X Y Z : GSet G) (f : GSetHom G X Y) (g : GSetHom G Y Z)
  : GSetHom G X Z
  ≔ z x ↦ g z (f z x)

{` rem:map-of-Gsets. f_w(g ·_X x) = g ·_Y f_z(x) for g : z = w. `}
def gset_hom_natural (G : Group) (X Y : GSet G) (f : GSetHom G X Y) (z w : BG G .carrier)
  (g : Id (BG G .carrier) z w) (x : X z .fst)
  : Id (Y w .fst) (f w (gset_act G X z w g x)) (gset_act G Y z w g (f z x))
  ≔ J (BG G .carrier) z
      (w g ↦ Id (Y w .fst) (f w (gset_act G X z w g x)) (gset_act G Y z w g (f z x)))
      (concat (Y z .fst) (f z (gset_act G X z z (refl z) x)) (f z x) (gset_act G Y z z (refl z) (f z x))
        (refl (f z) (gset_act_refl G X z x))
        (inverse (Y z .fst) (gset_act G Y z z (refl z) (f z x)) (f z x) (gset_act_refl G Y z (f z x))))
      w g

{` The equivariance on the underlying sets: f(g · x) = g · f(x). `}
def gset_hom_equivariant (G : Group) (X Y : GSet G) (f : GSetHom G X Y) (g : USym G)
  (x : gset_underlying G X)
  : Id (gset_underlying G Y) (f (shape G) (gset_usym_act G X g x)) (gset_usym_act G Y g (f (shape G) x))
  ≔ gset_hom_natural G X Y f (shape G) (shape G) g x

{` def:Gsubset. The set Prop (as an element of Set), the trivial G-set
   triv_G Prop, and Sub_G(X) ≔ Hom_G(X, triv_G Prop), which is by definition
   Π_{z:BG} Sub(X(z)). `}
def gsubset_prop_set : SetTypes ≔ (PropTypes, propositions_set)

def GSubsets (G : Group) (X : GSet G) : Type ≔ GSetHom G X (gset_trivial G gsubset_prop_set)

def gsubsets_unfold (G : Group) (X : GSet G)
  : Id Type (GSubsets G X) ((z : BG G .carrier) → Subtypes (X z .fst))
  ≔ refl (GSubsets G X)

def gsubsets_set (G : Group) (X : GSet G) : isSet (GSubsets G X)
  ≔ gset_hom_set G X (gset_trivial G gsubset_prop_set)

{` The underlying G-set X_P(z) ≔ Σ_{x:X(z)} P(z)(x) of a G-subset P. `}
def gsubset_gset (G : Group) (X : GSet G) (P : GSubsets G X) : GSet G
  ≔ z ↦ (Σ (X z .fst) (x ↦ P z x .fst),
      sigma_set (X z .fst) (x ↦ P z x .fst) (X z .snd) (x ↦ prop_is_set (P z x .fst) (P z x .snd)))

{` rem:map-of-Gsets, special case Y = triv_G Prop: P_w(g · x) holds iff P_z(x). `}
def gsubset_invariant (G : Group) (X : GSet G) (P : GSubsets G X) (z w : BG G .carrier)
  (g : Id (BG G .carrier) z w) (x : X z .fst)
  : Id PropTypes (P w (gset_act G X z w g x)) (P z x)
  ≔ concat PropTypes (P w (gset_act G X z w g x))
      (gset_act G (gset_trivial G gsubset_prop_set) z w g (P z x)) (P z x)
      (gset_hom_natural G X (gset_trivial G gsubset_prop_set) P z w g x)
      (gset_trivial_act G gsubset_prop_set z w g (P z x))

def gsubset_invariant_iff (G : Group) (X : GSet G) (P : GSubsets G X) (z w : BG G .carrier)
  (g : Id (BG G .carrier) z w) (x : X z .fst)
  : Product (P w (gset_act G X z w g x) .fst → P z x .fst) (P z x .fst → P w (gset_act G X z w g x) .fst)
  ≔ (u ↦ transport PropTypes (Q ↦ Q .fst) (P w (gset_act G X z w g x)) (P z x)
        (gsubset_invariant G X P z w g x) u,
     u ↦ transport PropTypes (Q ↦ Q .fst) (P z x) (P w (gset_act G X z w g x))
        (inverse PropTypes (P w (gset_act G X z w g x)) (P z x) (gsubset_invariant G X P z w g x)) u)

{` def:finite-G-set. X is finite if X(sh_G) is; Card(X) ≔ Card(X(sh_G)). `}
def IsFiniteGSet (G : Group) (X : GSet G) : Type ≔ IsFinite (gset_underlying G X)

def is_finite_gset_prop (G : Group) (X : GSet G) : isProp (IsFiniteGSet G X)
  ≔ isfinite_prop (gset_underlying G X)

def gset_card (G : Group) (X : GSet G) (h : IsFiniteGSet G X) : Nat ≔ Card (X (shape G), h)

{` def:Gaction. An action of G on a set S is a homomorphism G → Σ_S. `}
def GroupActionOnSet (G : Group) (S : SetTypes) : Type ≔ GroupHom G (permutation_group S)

{` def:action. An action of G in a type A is a function BG → A, acting on
   the object X(sh_G). An action of G on a : A is a homomorphism from G to
   Aut_A(a); since Aut_A(a) is a group only for groupoids A, it is stated
   for an arbitrary type A as a pointed map BG →* (A_(a), (a, !)) (the
   ∞-group homomorphism), which for a groupoid A is literally a
   homomorphism G → Aut_A(a) (action_on_element_group_hom_equiv). `}
def ActionInType (G : Group) (A : Type) : Type ≔ BG G .carrier → A

def action_object (G : Group) (A : Type) (X : ActionInType G A) : A ≔ X (shape G)

def ActionOnElement (G : Group) (A : Type) (a : A) : Type
  ≔ BookPointedMap (BG G) (NativeComponent A a, component_point A a)

def action_on_element_group_hom_equiv (G : Group) (A : Type) (hA : isGroupoid A) (a : A)
  : Equiv (ActionOnElement G A a) (GroupHom G (automorphism_group A hA a))
  ≔ quasi_inverse_equiv (ActionOnElement G A a) (GroupHom G (automorphism_group A hA a))
      (k ↦ mkhom G (automorphism_group A hA a) k) (f ↦ hom_B G (automorphism_group A hA a) f)
      (k ↦ refl k) (f ↦ refl f)

{` A G-set is an action of G in Set (definitionally). `}
def gset_action_in_set (G : Group) : Id Type (GSet G) (ActionInType G SetTypes) ≔ refl (GSet G)

{` std-action. The standard action of G on sh_G: A ≔ BG and X ≔ id. `}
def standard_action (G : Group) : ActionInType G (BG G .carrier) ≔ z ↦ z

def standard_action_object (G : Group)
  : Id (BG G .carrier) (action_object G (BG G .carrier) (standard_action G)) (shape G)
  ≔ refl (shape G)

{` def:restrictandinduce. For f : Hom(G, H): the restriction f^*Y ≔ Y ∘ Bf
   of an H-set Y, and the induced H-set
   f_!X(w) ≔ ‖Σ_{z:BG} (Bf(z) = w) × X(z)‖₀ of a G-set X. `}
def gset_restrict (G H : Group) (f : GroupHom G H) (Y : GSet H) : GSet G
  ≔ z ↦ Y (hom_function G H f z)

def GSetInducedSum (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier) : Type
  ≔ Σ (BG G .carrier) (z ↦ Product (Id (BG H .carrier) (hom_function G H f z) w) (X z .fst))

def gset_induce (G H : Group) (f : GroupHom G H) (X : GSet G) : GSet H
  ≔ w ↦ (SetTrunc (GSetInducedSum G H f X w), set_trunc_set (GSetInducedSum G H f X w))

{` rem:coinduced-Hset. f_*X(w) ≔ Π_{z:BG} ((Bf(z) = w) → X(z)), a set
   since X lands in sets. `}
def gset_coinduce (G H : Group) (f : GroupHom G H) (X : GSet G) : GSet H
  ≔ w ↦ ((z : BG G .carrier) → Id (BG H .carrier) (hom_function G H f z) w → X z .fst,
      pi_set (BG G .carrier) (z ↦ Id (BG H .carrier) (hom_function G H f z) w → X z .fst)
        (z ↦ pi_set (Id (BG H .carrier) (hom_function G H f z) w) (_ ↦ X z .fst) (_ ↦ X z .snd)))

{` Extensionality for maps of G-sets. `}
def gset_hom_ext (G : Group) (X Y : GSet G) (f f' : GSetHom G X Y)
  (h : (z : BG G .carrier) (x : X z .fst) → Id (Y z .fst) (f z x) (f' z x))
  : Id (GSetHom G X Y) f f'
  ≔ funext (BG G .carrier) (z ↦ X z .fst → Y z .fst) f f'
      (z ↦ funext (X z .fst) (_ ↦ Y z .fst) (f z) (f' z) (h z))

{` rem:GSet=SetHomG, the two directions as maps (their equivalence is in a
   later module). A G-set X gives the homomorphism G → Σ_{X(sh_G)} classified
   by z ↦ (X(z), !), pointed by reflexivity; a homomorphism f : G → Σ_S
   gives the G-set z ↦ Bf(z) (the "delooping" of f). `}
def gset_to_action (G : Group) (X : GSet G) : GroupActionOnSet G (X (shape G))
  ≔ let S ≔ X (shape G) in
    mkhom G (permutation_group S)
      (z ↦ (X z, mere_rec (Id (BG G .carrier) (shape G) z) (Mere (Id SetTypes S (X z)))
              (mere_isprop (Id SetTypes S (X z)))
              (p ↦ mere (Id SetTypes S (X z)) (map_path (BG G .carrier) SetTypes X (shape G) z p))
              (bg_connected G .snd (shape G) z)),
       component_path SetTypes S (component_point SetTypes S)
         (X (shape G), mere_rec (Id (BG G .carrier) (shape G) (shape G)) (Mere (Id SetTypes S S))
              (mere_isprop (Id SetTypes S S))
              (p ↦ mere (Id SetTypes S S) (map_path (BG G .carrier) SetTypes X (shape G) (shape G) p))
              (bg_connected G .snd (shape G) (shape G)))
         (refl S))

def action_to_gset (G : Group) (S : SetTypes) (f : GroupActionOnSet G S) : GSet G
  ≔ z ↦ hom_function G (permutation_group S) f z .fst

{` The underlying set of the delooped G-set is identified with S by the
   pointing path of f. `}
def action_to_gset_underlying (G : Group) (S : SetTypes) (f : GroupActionOnSet G S)
  : Id SetTypes S (action_to_gset G S f (shape G))
  ≔ hom_point G (permutation_group S) f .fst

def gset_to_action_to_gset (G : Group) (X : GSet G)
  : Id (GSet G) (action_to_gset G (X (shape G)) (gset_to_action G X)) X
  ≔ refl X
