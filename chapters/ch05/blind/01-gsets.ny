{` Blind statements for chapter 5 (actions.tex), section "Group actions (G-sets)".
   Written without looking at the project's chapter-5 modules. `}
export "../../../src/437-conjugation-inner-automorphisms"
export "../../../src/485-infinity-groups"
export "../../../src/410-pointed-connected-groupoids"
export "../../../src/406-symmetric-group-three"
export "../../../src/483-figure-eight-coverings"

{` Helpers. `}
def BlindIff (P Q : Type) : Type ≔ Product (P → Q) (Q → P)
def BlindBG (G : Group) : Type ≔ BG G .carrier

{` def:Gset. A G-set is a function BG → Set. `}
def BlindGSet (G : Group) : Type ≔ BlindBG G → SetTypes

{` def:Gset. The underlying set X(sh_G). `}
def blind_underlying_set (G : Group) (X : BlindGSet G) : Type ≔ X (shape G) .fst

{` def:Gset. p ·_X a ≔ X(p)(a) = transport of a along p : z = w in the family X. `}
def blind_act (G : Group) (X : BlindGSet G) (z w : BlindBG G) (p : Id (BlindBG G) z w) (a : X z .fst) : X w .fst
  ≔ transport (BlindBG G) (u ↦ X u .fst) z w p a

{` The action of g : USym G on the underlying set. `}
def blind_usym_act (G : Group) (X : BlindGSet G) (g : USym G) (a : X (shape G) .fst) : X (shape G) .fst
  ≔ blind_act G X (shape G) (shape G) g a

{` def:Gset: X(p) is an equivalence X(z) ≃ X(w). `}
def blind_act_is_equiv : Type
  ≔ (G : Group) (X : BlindGSet G) (z w : BlindBG G) (p : Id (BlindBG G) z w)
    → BookIsEquiv (X z .fst) (X w .fst) (blind_act G X z w p)

{` def:trivGset. `}
def blind_triv (G : Group) (S : SetTypes) : BlindGSet G ≔ _ ↦ S

{` rem:G-set-vs-set-bundle: G-sets are equivalent to coverings over BG. `}
def blind_gset_vs_coverings : Type ≔ (G : Group) → Equiv (BlindGSet G) (Coverings (BlindBG G))

{` def:principaltorsor. `}
def blind_princ (G : Group) : BlindGSet G
  ≔ z ↦ (Id (BlindBG G) (shape G) z, bg_groupoid G (shape G) z)

{` eq:pathsp. P_y(z) ≔ (y = z). `}
def blind_pathsp (G : Group) (y : BlindBG G) : BlindGSet G
  ≔ z ↦ (Id (BlindBG G) y z, bg_groupoid G y z)

{` def:principaltorsor: transport along q : y = y' sends p : y = z to p q⁻¹ (book order), i.e. q⁻¹ then p. `}
def blind_pathsp_transport : Type
  ≔ (G : Group) (y y' : BlindBG G) (q : Id (BlindBG G) y y') (z : BlindBG G) (p : Id (BlindBG G) y z)
    → Id (Id (BlindBG G) y' z)
        (transport (BlindBG G) (u ↦ blind_pathsp G u z .fst) y y' q p)
        (concat (BlindBG G) y' y z (inverse (BlindBG G) y y' q) p)

{` def:principaltorsor: princ G (sh_G) ≡ USym G. `}
def blind_princ_underlying : Type ≔ (G : Group) → Id Type (blind_underlying_set G (blind_princ G)) (USym G)

{` def:adjointrep. `}
def blind_Ad (G : Group) : BlindGSet G ≔ z ↦ (Id (BlindBG G) z z, bg_groupoid G z z)

{` ft:adjoint-transport: Ad_G(p)(q) = p q p⁻¹ (book order), i.e. p⁻¹, then q, then p. `}
def blind_Ad_transport : Type
  ≔ (G : Group) (y z : BlindBG G) (p : Id (BlindBG G) y z) (q : Id (BlindBG G) y y)
    → Id (Id (BlindBG G) z z) (blind_act G (blind_Ad G) y z p q)
        (concat (BlindBG G) z y z (inverse (BlindBG G) y z p) (concat (BlindBG G) y y z q p))

{` ft:adjoint-transport: princ G(p)(q) is q followed by p (book: p q). `}
def blind_princ_transport : Type
  ≔ (G : Group) (y z : BlindBG G) (p : Id (BlindBG G) y z) (q : Id (BlindBG G) (shape G) y)
    → Id (Id (BlindBG G) (shape G) z) (blind_act G (blind_princ G) y z p q) (concat (BlindBG G) (shape G) y z q p)

{` def:adjointrep: Σ_{z:BG} Ad_G(z) ≃ (S¹ → BG), with the first projection corresponding to evaluation at base. `}
def blind_Ad_free_loops : Type
  ≔ (G : Group) (C : CircleSignature)
    → Σ (BookEquiv (Σ (BlindBG G) (z ↦ blind_Ad G z .fst)) (C .carrier → BlindBG G))
        (e ↦ (u : Σ (BlindBG G) (z ↦ blind_Ad G z .fst)) → Id (BlindBG G) (e .map u (C .base)) (u .fst))

{` ex:HomHGasGset. Hom(H,G)(x,y) ≔ Hom(mkgroup(BH÷,x), mkgroup(BG÷,y)), an (H×G)-set. `}
def blind_hom_hg (H G : Group) : BlindGSet (product_group H G)
  ≔ u ↦ (GroupHom (group_at H (u .fst)) (group_at G (u .snd)), group_hom_set (group_at H (u .fst)) (group_at G (u .snd)))

{` ex:HomHGasGset. The restriction to G: Hom(H,G)(y) ≔ Hom(H,G)(sh_H, y). `}
def blind_hom_g (H G : Group) : BlindGSet G ≔ y ↦ blind_hom_hg H G (shape H, y)

{` ex:HomHGasGset: Hom(H,G)(x,y) ≃ Σ_{f : BH÷ → BG÷} (y = f(x)). `}
def blind_hom_hg_unfold : Type
  ≔ (H G : Group) (x : BlindBG H) (y : BlindBG G)
    → Equiv (blind_hom_hg H G (x, y) .fst) (Σ (BlindBG H → BlindBG G) (f ↦ Id (BlindBG G) y (f x)))

{` xca:HomZGvsAdG, with Z = mkgroup(S¹, base) for any circle. `}
def blind_HomZGvsAdG : Type
  ≔ (C : CircleSignature) (G : Group) → Id (BlindGSet G) (blind_Ad G) (blind_hom_g (circle_group C) G)

{` def:map-of-Gsets. `}
def BlindHomG (G : Group) (X Y : BlindGSet G) : Type ≔ (z : BlindBG G) → X z .fst → Y z .fst

{` def:map-of-Gsets: Hom_G(X,Y) is a set. `}
def blind_hom_g_set : Type ≔ (G : Group) (X Y : BlindGSet G) → isSet (BlindHomG G X Y)

{` Tot(X) = Σ_{z:BG} X(z). `}
def BlindTot (G : Group) (X : BlindGSet G) : Type ≔ Σ (BlindBG G) (z ↦ X z .fst)

{` xca:equivariant-map-totalization. `}
def blind_equivariant_map_totalization : Type
  ≔ (G : Group) (X Y : BlindGSet G)
    → Equiv (BlindHomG G X Y)
        (Σ (BlindTot G X → BlindTot G Y)
           (f ↦ Id (BlindTot G X → BlindBG G) (u ↦ u .fst) (u ↦ f u .fst)))

{` rem:map-of-Gsets: f_w(g ·_X x) = g ·_Y f_z(x). `}
def blind_map_of_gsets_equivariant : Type
  ≔ (G : Group) (X Y : BlindGSet G) (f : BlindHomG G X Y) (z w : BlindBG G) (x : X z .fst) (g : Id (BlindBG G) z w)
    → Id (Y w .fst) (f w (blind_act G X z w g x)) (blind_act G Y z w g (f z x))

{` The set Prop. `}
def blind_prop_set : SetTypes ≔ (PropTypes, propositions_set)

{` rem:map-of-Gsets: for P : Hom_G(X, triv Prop), P_w(g·x) iff P_z(x). `}
def blind_map_to_prop_invariant : Type
  ≔ (G : Group) (X : BlindGSet G) (P : BlindHomG G X (blind_triv G blind_prop_set)) (z w : BlindBG G) (x : X z .fst)
    (g : Id (BlindBG G) z w)
    → BlindIff (P w (blind_act G X z w g x) .fst) (P z x .fst)

{` def:Gsubset. Sub_G(X) ≔ Hom_G(X, triv_G Prop). `}
def BlindSubG (G : Group) (X : BlindGSet G) : Type ≔ BlindHomG G X (blind_triv G blind_prop_set)

{` def:Gsubset: Sub_G(X) ≡ Π_z Sub(X(z)). `}
def blind_subg_unfold : Type
  ≔ (G : Group) (X : BlindGSet G) → Id Type (BlindSubG G X) ((z : BlindBG G) → Subtypes (X z .fst))

{` def:Gsubset: Sub_G(X) is a set. `}
def blind_subg_set : Type ≔ (G : Group) (X : BlindGSet G) → isSet (BlindSubG G X)

{` ft:SubTotX: Sub_G(X) ≃ (Tot(X) → Prop). `}
def blind_subg_tot : Type ≔ (G : Group) (X : BlindGSet G) → Equiv (BlindSubG G X) (Subtypes (BlindTot G X))

{` def:Gsubset. The underlying G-set X_P(z) ≔ Σ_{x:X(z)} P(z)(x). `}
def blind_gsubset_underlying (G : Group) (X : BlindGSet G) (P : BlindSubG G X) : BlindGSet G
  ≔ z ↦ (Σ (X z .fst) (x ↦ P z x .fst),
         sigma_set (X z .fst) (x ↦ P z x .fst) (X z .snd) (x ↦ prop_is_set (P z x .fst) (P z x .snd)))

{` The proof that P(sh_G) is closed under the action (needed to define the evaluation map of xca:SubGX-closedSubXshG). `}
def blind_subset_closed (G : Group) (X : BlindGSet G) (P : BlindSubG G X) (x : X (shape G) .fst) (px : P (shape G) x .fst)
  (g : USym G) : P (shape G) (blind_usym_act G X g x) .fst
  ≔ refl P g (pathover_of_eq (BlindBG G) (u ↦ X u .fst) (shape G) (shape G) g x (blind_usym_act G X g x)
       (refl (blind_usym_act G X g x))) .fst .trr px

{` xca:SubGX-closedSubXshG: subsets of X(sh_G) closed under the action. `}
def BlindClosedSubsets (G : Group) (X : BlindGSet G) : Type
  ≔ Σ (Subtypes (X (shape G) .fst))
      (Q ↦ (x : X (shape G) .fst) → Q x .fst → (g : USym G) → Q (blind_usym_act G X g x) .fst)

def blind_subset_eval (G : Group) (X : BlindGSet G) (P : BlindSubG G X) : BlindClosedSubsets G X
  ≔ (P (shape G), x px g ↦ blind_subset_closed G X P x px g)

{` xca:SubGX-closedSubXshG: evaluation at sh_G is an equivalence. `}
def blind_SubGX_closedSubXshG : Type
  ≔ (G : Group) (X : BlindGSet G) → BookIsEquiv (BlindSubG G X) (BlindClosedSubsets G X) (blind_subset_eval G X)

{` xca:ptd-conn-to-comp. `}
def blind_ptd_conn_to_comp : Type
  ≔ (A B : Pointed) (hA : Connected (A .carrier))
    → Equiv (BookPointedMap A B)
        (BookPointedMap A (NativeComponent (B .carrier) (B .point), component_point (B .carrier) (B .point)))

{` rem:GSet=SetHomG: pairs of a set and a homomorphism into its permutation group. `}
def BlindSetHom (G : Group) : Type ≔ Σ SetTypes (S ↦ GroupHom G (permutation_group S))

{` rem:GSet=SetHomG: the pair u corresponds to X: X(sh_G) = S and g · x corresponds to f(g)(x). `}
def BlindActionCompatible (G : Group) (X : BlindGSet G) (u : BlindSetHom G) : Type
  ≔ Σ (Id SetTypes (X (shape G)) (u .fst))
      (p ↦ (g : USym G) (x : X (shape G) .fst)
        → Id (u .fst .fst)
            (transport SetTypes (S ↦ S .fst) (X (shape G)) (u .fst) p (blind_usym_act G X g x))
            (permutation_action (u .fst) (usym_hom G (permutation_group (u .fst)) (u .snd) g)
               (transport SetTypes (S ↦ S .fst) (X (shape G)) (u .fst) p x)))

{` rem:GSet=SetHomG: GSet ≃ Σ_{S:Set} Hom(G, Σ_S), compatibly with underlying sets and actions. `}
def blind_GSet_SetHomG : Type
  ≔ (G : Group)
    → Σ (Equiv (BlindGSet G) (BlindSetHom G)) (e ↦ (X : BlindGSet G) → BlindActionCompatible G X (e .map X))

{` def:Gaction. An action of G on a set S. `}
def BlindAction (G : Group) (S : SetTypes) : Type ≔ GroupHom G (permutation_group S)

{` xca:Ad-triv-abelian. `}
def blind_Ad_triv_abelian : Type
  ≔ (G : Group) → BlindIff (IsAbelian G) (Id (BlindGSet G) (blind_Ad G) (blind_triv G (USym G, usym_set G)))

{` xca:Ad-princ-trivial. `}
def blind_Ad_princ_trivial : Type
  ≔ (G : Group) → BlindIff (Id Group G trivial_group) (Id (BlindGSet G) (blind_Ad G) (blind_princ G))

{` def:finite-G-set. `}
def BlindIsFiniteGSet (G : Group) (X : BlindGSet G) : Type ≔ IsFinite (X (shape G) .fst)

def blind_gset_card (G : Group) (X : BlindGSet G) (h : BlindIsFiniteGSet G X) : Nat ≔ cardinality (X (shape G) .fst) h

{` def:finite-G-set, footnote: finiteness / n-element-ness at sh_G iff at every z. `}
def blind_finite_gset_everywhere : Type
  ≔ (G : Group) (X : BlindGSet G) → BlindIff (IsFinite (X (shape G) .fst)) ((z : BlindBG G) → IsFinite (X z .fst))

def blind_n_element_gset_everywhere : Type
  ≔ (G : Group) (X : BlindGSet G) (n : Nat)
    → BlindIff (Mere (Id Type (Fin n) (X (shape G) .fst))) ((z : BlindBG G) → Mere (Id Type (Fin n) (X z .fst)))

{` def:transitiveGset. istrans(X) ≔ ∃_{x:X(sh)} Π_{y:X(sh)} ∃_{g:USym G} (x = g·y). `}
def BlindIsTrans (G : Group) (X : BlindGSet G) : Type
  ≔ Mere (Σ (X (shape G) .fst)
      (x ↦ (y : X (shape G) .fst) → Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) x (blind_usym_act G X g y)))))

{` eq:Gset-trans-gen (remark): transitive iff ∃x with (- · x) surjective. `}
def blind_trans_iff_surjective : Type
  ≔ (G : Group) (X : BlindGSet G)
    → BlindIff (BlindIsTrans G X)
        (Mere (Σ (X (shape G) .fst) (x ↦ Surjective (USym G) (X (shape G) .fst) (g ↦ blind_usym_act G X g x))))

{` eq:Gset-trans-gen: the version over all z : BG. `}
def blind_trans_iff_all_z : Type
  ≔ (G : Group) (X : BlindGSet G)
    → BlindIff (BlindIsTrans G X)
        ((z : BlindBG G) → Mere (Σ (X z .fst) (x ↦ (y : X z .fst)
           → Mere (Σ (Id (BlindBG G) z z) (g ↦ Id (X z .fst) x (blind_act G X z z g y))))))

{` eq:Gset-trans-gen: nonempty and any two elements related. `}
def blind_trans_iff_nonempty : Type
  ≔ (G : Group) (X : BlindGSet G)
    → BlindIff (BlindIsTrans G X)
        (Product (Mere (X (shape G) .fst))
           ((x y : X (shape G) .fst) → Mere (Σ (USym G) (g ↦ Id (X (shape G) .fst) x (blind_usym_act G X g y)))))

{` eq:Gset-trans-gen: the empty G-set is not transitive. `}
def blind_empty_not_trans : Type ≔ (G : Group) → Not (BlindIsTrans G (blind_triv G (Empty, empty_set)))

{` lem:conistrans: transitive iff the associated covering (its total space) is connected. `}
def blind_conistrans : Type
  ≔ (G : Group) (X : BlindGSet G) → BlindIff (BlindIsTrans G X) (Connected (BlindTot G X))

{` lem:evisinjwhentransitive. `}
def blind_evisinjwhentransitive : Type
  ≔ (G : Group) (X Y : BlindGSet G) (z : BlindBG G) (x : X z .fst) (t : BlindIsTrans G X)
    → IsEmbedding (BlindHomG G X Y) (Y z .fst) (f ↦ f z x)

{` Evaluation (X = X) → X(z) at x : X(z) (def:normal-action). `}
def blind_gset_ev (G : Group) (X : BlindGSet G) (z : BlindBG G) (x : X z .fst) : Id (BlindGSet G) X X → X z .fst
  ≔ e ↦ transport (BlindGSet G) (Y ↦ Y z .fst) X X e x

{` xca:not-normal. The figure eight S¹∨S¹ is a signature (no HITs); that it is a groupoid is a hypothesis. `}
def blind_figure_eight_group (W : FigureEightSignature) (hW : isGroupoid (W .carrier)) : Group
  ≔ mkgroup (W .carrier, W .base,
      based_to_connected (W .carrier) (W .base)
        (x ↦ trunc_map native_truncation (Id (W .carrier) x (W .base)) (Id (W .carrier) (W .base) x)
               (inverse (W .carrier) x (W .base)) (figure_eight_connected_to_base W x)),
      hW)

{` The G-set of fig:not-normal: base ↦ 3 = {0,1,2}, loop₁ ↦ cyclic successor, loop₂ ↦ the transposition (0 1). `}
def blind_not_normal_gset (W : FigureEightSignature) (hW : isGroupoid (W .carrier))
  : BlindGSet (blind_figure_eight_group W hW)
  ≔ figure_eight_rec W SetTypes
      (standard_set three,
       (set_types_path (standard_set three) (standard_set three) (finite_fin_successor (suc. (suc. zero.))),
        set_types_path (standard_set three) (standard_set three) fin3_swap01_equiv))

{` xca:not-normal: X is transitive (implicit in the text). `}
def blind_not_normal_transitive : Type
  ≔ (W : FigureEightSignature) (hW : isGroupoid (W .carrier))
    → BlindIsTrans (blind_figure_eight_group W hW) (blind_not_normal_gset W hW)

{` xca:not-normal: X = X is contractible. `}
def blind_not_normal_aut_contractible : Type
  ≔ (W : FigureEightSignature) (hW : isGroupoid (W .carrier))
    → BookIsContr (Id (BlindGSet (blind_figure_eight_group W hW)) (blind_not_normal_gset W hW) (blind_not_normal_gset W hW))

{` xca:not-normal: ev_x is injective but not surjective. `}
def blind_not_normal_ev : Type
  ≔ (W : FigureEightSignature) (hW : isGroupoid (W .carrier)) (x : blind_not_normal_gset W hW (W .base) .fst)
    → Product
        (IsEmbedding (Id (BlindGSet (blind_figure_eight_group W hW)) (blind_not_normal_gset W hW) (blind_not_normal_gset W hW))
           (blind_not_normal_gset W hW (W .base) .fst)
           (blind_gset_ev (blind_figure_eight_group W hW) (blind_not_normal_gset W hW) (W .base) x))
        (Not (Surjective (Id (BlindGSet (blind_figure_eight_group W hW)) (blind_not_normal_gset W hW) (blind_not_normal_gset W hW))
           (blind_not_normal_gset W hW (W .base) .fst)
           (blind_gset_ev (blind_figure_eight_group W hW) (blind_not_normal_gset W hW) (W .base) x)))

{` def:normal-action. A transitive G-set is normal if every evaluation map is an equivalence. `}
def BlindIsNormal (G : Group) (X : BlindGSet G) : Type
  ≔ Product (BlindIsTrans G X)
      ((z : BlindBG G) (x : X z .fst) → BookIsEquiv (Id (BlindGSet G) X X) (X z .fst) (blind_gset_ev G X z x))

{` xca:normal-action-equiv (for transitive X, as in def:normal-action). `}
def blind_normal_action_equiv : Type
  ≔ (G : Group) (X : BlindGSet G) (t : BlindIsTrans G X) (z : BlindBG G) (x : X z .fst)
    (h : BookIsEquiv (Id (BlindGSet G) X X) (X z .fst) (blind_gset_ev G X z x))
    (z' : BlindBG G) (x' : X z' .fst)
    → BookIsEquiv (Id (BlindGSet G) X X) (X z' .fst) (blind_gset_ev G X z' x')

{` def:action. An action of G in a type A. `}
def BlindActionIn (G : Group) (A : Type) : Type ≔ BlindBG G → A

{` def:action. The object acted on. `}
def blind_action_object (G : Group) (A : Type) (X : BlindActionIn G A) : A ≔ X (shape G)

{` def:action. An action of G on a : A is a homomorphism G → Aut_A(a) (an ∞-group for general A). `}
def BlindActionOn (G : Group) (A : Type) (a : A) : Type
  ≔ InftyGroupHom (group_to_infty_group G) (infty_automorphism_group A a)

{` std-action. `}
def blind_standard_action (G : Group) : BlindActionIn G (BlindBG G) ≔ z ↦ z

{` ex:S2-acts-on-C3. A shape S : BΣ₂ is a 2-element set. `}
def blind_s2_two_element (S : BlindBG (symmetric_group two)) : TwoElement (S .fst .fst)
  ≔ mere_rec (Id SetTypes (standard_set two) (S .fst)) (TwoElement (S .fst .fst)) (two_element_prop (S .fst .fst))
      (p ↦ mere (Id Type (Fin two) (S .fst .fst)) (p .fst)) (S .snd)

{` swap(s): the other element of S. `}
def blind_s2_swap (S : BlindBG (symmetric_group two)) (s : S .fst .fst) : S .fst .fst
  ≔ two_pointed_enumeration (S .fst .fst) (blind_s2_two_element S) s .map true.

def blind_s2_dec (S : BlindBG (symmetric_group two)) : DecidableEquality (S .fst .fst)
  ≔ finite_decidable_equality (S .fst .fst) (two_element_finite (S .fst .fst) (blind_s2_two_element S))

def blind_s2c3_case (S : BlindBG (symmetric_group two)) (s t : S .fst .fst) (d : Decidable (Id (S .fst .fst) t s))
  : Sum (Fin (suc. zero.)) (S .fst .fst)
  ≔ match d [ inl. _ ↦ inr. (blind_s2_swap S s) | inr. _ ↦ inl. (inr. star.) ]

{` f_s(inl 0) ≔ inr s, f_s(inr s) ≔ inr swap(s), f_s(inr swap(s)) ≔ inl 0. `}
def blind_s2c3_fun (S : BlindBG (symmetric_group two)) (s : S .fst .fst) (x : Sum (Fin (suc. zero.)) (S .fst .fst))
  : Sum (Fin (suc. zero.)) (S .fst .fst)
  ≔ match x [
    | inl. _ ↦ inr. s
    | inr. t ↦ blind_s2c3_case S s t (blind_s2_dec S t s) ]

{` Σ_{X:Set} (S → (X → X)). `}
def BlindS2C3Type (S : BlindBG (symmetric_group two)) : Type ≔ Σ SetTypes (X ↦ S .fst .fst → X .fst → X .fst)

def blind_s2c3_type_groupoid (S : BlindBG (symmetric_group two)) : isGroupoid (BlindS2C3Type S)
  ≔ hlevel_to_groupoid (BlindS2C3Type S)
      (hlevel_sigma (suc. (suc. (suc. zero.)))  SetTypes (X ↦ S .fst .fst → X .fst → X .fst)
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (X ↦ hlevel_raise (suc. (suc. zero.)) (S .fst .fst → X .fst → X .fst)
           (set_to_hlevel_two (S .fst .fst → X .fst → X .fst)
              (pi_set (S .fst .fst) (_ ↦ X .fst → X .fst) (_ ↦ pi_set (X .fst) (_ ↦ X .fst) (_ ↦ X .snd))))))

def blind_s2c3_point (S : BlindBG (symmetric_group two)) : BlindS2C3Type S
  ≔ ((Sum (Fin (suc. zero.)) (S .fst .fst), sum_set (Fin (suc. zero.)) (S .fst .fst) (fin_set (suc. zero.)) (S .fst .snd)),
     blind_s2c3_fun S)

{` ex:S2-acts-on-C3. G(S) ≔ Aut(1 ⊔ S, f), an action BΣ₂ → Group. `}
def blind_s2_acts_on_c3 (S : BlindBG (symmetric_group two)) : Group
  ≔ automorphism_group (BlindS2C3Type S) (blind_s2c3_type_groupoid S) (blind_s2c3_point S)

def blind_bool_s2_shape : BlindBG (symmetric_group two)
  ≔ ((Bool, bool_set),
     mere (Id SetTypes (standard_set two) (Bool, bool_set)) (set_types_path (standard_set two) (Bool, bool_set) fin_two_equiv))

{` ex:S2-acts-on-C3: G(bool) is identified with C₃. `}
def blind_s2_acts_on_c3_bool : Type ≔ Id Group (blind_s2_acts_on_c3 blind_bool_s2_shape) (cyclic_group_fin (suc. (suc. zero.)))

{` xca:AutC3. Given an identification p : C₃ = G(sh), the action classifies a homomorphism Σ₂ → Aut(C₃). `}
def blind_autc3_witness (p : Id Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 (shape (symmetric_group two))))
  (z : BlindBG (symmetric_group two)) : Mere (Id Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 z))
  ≔ trunc_map native_truncation (Id (BlindBG (symmetric_group two)) (shape (symmetric_group two)) z)
      (Id Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 z))
      (q ↦ concat Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 (shape (symmetric_group two)))
             (blind_s2_acts_on_c3 z) p (refl blind_s2_acts_on_c3 q))
      (bg_connected (symmetric_group two) .snd (shape (symmetric_group two)) z)

def blind_autc3_classifying
  (p : Id Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 (shape (symmetric_group two))))
  : BookPointedMap (BG (symmetric_group two)) (BG (group_aut (cyclic_group_fin (suc. (suc. zero.)))))
  ≔ (z ↦ (blind_s2_acts_on_c3 z, blind_autc3_witness p z),
     component_path Group (cyclic_group_fin (suc. (suc. zero.)))
       (component_point Group (cyclic_group_fin (suc. (suc. zero.))))
       (blind_s2_acts_on_c3 (shape (symmetric_group two)), blind_autc3_witness p (shape (symmetric_group two))) p)

{` xca:AutC3: the action gives an identification Σ₂ = Aut(C₃) (the classified homomorphism is an isomorphism). `}
def blind_AutC3 : Type
  ≔ (p : Id Group (cyclic_group_fin (suc. (suc. zero.))) (blind_s2_acts_on_c3 (shape (symmetric_group two))))
    → IsGroupIso (symmetric_group two) (group_aut (cyclic_group_fin (suc. (suc. zero.))))
        (mkhom (symmetric_group two) (group_aut (cyclic_group_fin (suc. (suc. zero.)))) (blind_autc3_classifying p))

{` Example (actions.tex 669): the standard Σ_n-set (A, !) ↦ A. `}
def blind_standard_sn_set (n : Nat) : BlindGSet (symmetric_group n) ≔ A ↦ A .fst

{` Example (actions.tex 669), footnote: the standard Σ_n-set is transitive for n > 0. `}
def blind_standard_sn_set_transitive : Type
  ≔ (m : Nat) → BlindIsTrans (symmetric_group (suc. m)) (blind_standard_sn_set (suc. m))

{` Example (actions.tex 669): the Σ_n-set of decidable subsets A ↦ (A → 2), with underlying set n → 2. `}
def blind_sn_decidable_subsets (n : Nat) : BlindGSet (symmetric_group n)
  ≔ A ↦ (A .fst .fst → Bool, pi_set (A .fst .fst) (_ ↦ Bool) (_ ↦ bool_set))

def blind_sn_decidable_subsets_underlying : Type
  ≔ (n : Nat) → Id Type (blind_underlying_set (symmetric_group n) (blind_sn_decidable_subsets n)) (Fin n → Bool)
