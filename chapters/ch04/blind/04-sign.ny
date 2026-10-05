export "03-homs"
export "../../../src/176-transposition-generation"
export "../../../src/243-k-cycle-supports"
export "../../../src/36-cardinality-arithmetic"

{` Blind statements, chapter 4, section "The sign homomorphism".
   BS_2 is the classifying type of S_2 = Aut_Set(bn 2), i.e. the
   component of Set at bn 2. `}
def BlindBSG2 : Type ≔ NativeComponent SetTypes (blind_bn_set two)
def blind_bsg2_pt : BlindBSG2 ≔ blind_component_point SetTypes (blind_bn_set two)

def BlindLocalSections (E : Type) (P : E → BlindBSG2) : Type ≔ (e : E) → P e .fst .fst

{` "has an even number of elements": a cardinality witness k (S = Fin k)
   with k even. `}
def blind_nat_even (n : Nat) : Bool ≔ match n [ zero. ↦ true. | suc. k ↦ bool_not (blind_nat_even k) ]

def BlindEvenCard (S : Type) : Type
  ≔ Σ Nat (k ↦ Product (Mere (Id Type S (Fin k))) (Id Bool (blind_nat_even k) true.))

def blind_even_card_prop (S : Type) : isProp (BlindEvenCard S)
  ≔ u v ↦ subtype_equal Nat (k ↦ Product (Mere (Id Type S (Fin k))) (Id Bool (blind_nat_even k) true.))
      (k ↦ product_prop (Mere (Id Type S (Fin k))) (Id Bool (blind_nat_even k) true.)
        (mere_isprop (Id Type S (Fin k))) (bool_set (blind_nat_even k) true.))
      u v (cardinality_witness_unique S (u .fst, u .snd .fst) (v .fst, v .snd .fst))

{` Definition (line 1473): the parity relation. `}
def BlindParityRel (E : Type) (P : E → BlindBSG2) (f g : BlindLocalSections E P) : Type
  ≔ BlindEvenCard (Σ E (e ↦ Not (Id (P e .fst .fst) (f e) (g e))))

def blind_parity_predicate (E : Type) (P : E → BlindBSG2)
  : BlindLocalSections E P → BlindLocalSections E P → PropTypes
  ≔ f g ↦ (BlindParityRel E P f g, blind_even_card_prop (Σ E (e ↦ Not (Id (P e .fst .fst) (f e) (g e)))))

{` The quotient (set quotient as the image of the predicate map, the
   construction of def:quotient-set; it needs no proof that the relation
   is an equivalence relation). `}
def BlindParityQuotient (E : Type) (P : E → BlindBSG2) : Type
  ≔ Image (BlindLocalSections E P) (BlindLocalSections E P → PropTypes) (blind_parity_predicate E P)
def blind_parity_class (E : Type) (P : E → BlindBSG2) (f : BlindLocalSections E P) : BlindParityQuotient E P
  ≔ image_factor (BlindLocalSections E P) (BlindLocalSections E P → PropTypes) (blind_parity_predicate E P) f
def blind_parity_quotient_set (E : Type) (P : E → BlindBSG2) : isSet (BlindParityQuotient E P)
  ≔ image_set (BlindLocalSections E P) (BlindLocalSections E P → PropTypes) (blind_parity_predicate E P)
      (subtypes_set (BlindLocalSections E P))

{` lem:parityequiv. `}
def blind_lem_parityequiv : Type
  ≔ (E : FiniteSets) (P : E .fst .fst → BlindBSG2) →
    let X ≔ BlindLocalSections (E .fst .fst) P in
    let R ≔ BlindParityRel (E .fst .fst) P in
    let Q ≔ BlindParityQuotient (E .fst .fst) P in
    Product ((f : X) → R f f)
      (Product ((f g : X) → R f g → R g f)
        (Product ((f g h : X) → R f g → R g h → R f h)
          (Product (Mere (E .fst .fst) → Mere (Id Type (Fin two) Q))
            (Not (E .fst .fst) → Mere (Id Type (Fin (suc. zero.)) Q)))))

{` def:mu_E. The power S_2^E is the product of the constant family
   (ex:bigproductofgroups, parametrized by xca:bigproductfunext (i)).
   For nonempty E the classifying map is P ↦ (Π P)/~, made an element of
   BS_2 by lem:parityequiv; its pointing path is a parameter, specified
   to send the class of the constant function at 0 (the book's all +1
   function) to 0 (= +1). For empty E it is the constant map, pointed by
   refl. Emptiness is decided by finite_inhabited_decidable. `}
def blind_group_power (hp : blind_xca_bigproduct_connected) (E : FiniteSets) (G : BlindGroup) : BlindGroup
  ≔ blind_group_bigproduct hp E (_ ↦ G)

def blind_two_to_component (X : SetTypes) (t : Mere (Id Type (Fin two) (X .fst))) : Mere (Id SetTypes (blind_bn_set two) X)
  ≔ mere_rec (Id Type (Fin two) (X .fst)) (Mere (Id SetTypes (blind_bn_set two) X)) (mere_isprop (Id SetTypes (blind_bn_set two) X))
      (p ↦ mere (Id SetTypes (blind_bn_set two) X) (subtype_equal Type isSet isset_isprop (blind_bn_set two) X p)) t

def blind_Bmu_nonempty (lem : blind_lem_parityequiv) (E : FiniteSets) (ne : Mere (E .fst .fst))
  (P : E .fst .fst → BlindBSG2) : BlindBSG2
  ≔ let Q ≔ BlindParityQuotient (E .fst .fst) P in
    let S : SetTypes ≔ (Q, blind_parity_quotient_set (E .fst .fst) P) in
    (S, blind_two_to_component S (lem E P .snd .snd .snd .fst ne))

def BlindMuPointing (lem : blind_lem_parityequiv) (E : FiniteSets) (ne : Mere (E .fst .fst)) : Type
  ≔ let c : E .fst .fst → BlindBSG2 ≔ _ ↦ blind_bsg2_pt in
    let target ≔ blind_Bmu_nonempty lem E ne c in
    Σ (Id BlindBSG2 blind_bsg2_pt target) (p ↦
      Id (BlindParityQuotient (E .fst .fst) c)
        (transport BlindBSG2 (X ↦ X .fst .fst) blind_bsg2_pt target p blind_fin_two_zero)
        (blind_parity_class (E .fst .fst) c (_ ↦ blind_fin_two_zero)))

{` The decision is an argument of the helper (a variable, so the match
   reduces as soon as the decision is a constructor); blind_mu_E feeds it
   the decision of finite_inhabited_decidable. Since Decidable (Mere E)
   is a proposition, every decision gives the same homomorphism. `}
def blind_mu_E_dec (hp : blind_xca_bigproduct_connected) (lem : blind_lem_parityequiv)
  (ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne) (E : FiniteSets)
  (d : Decidable (Mere (E .fst .fst)))
  : BlindHom (blind_group_power hp E (blind_SG two)) (blind_SG two)
  ≔ match d [
  | inl. ne ↦ blind_mkhom (blind_group_power hp E (blind_SG two)) (blind_SG two) (blind_Bmu_nonempty lem E ne, ptg E ne .fst)
  | inr. _ ↦ blind_mkhom (blind_group_power hp E (blind_SG two)) (blind_SG two) (_ ↦ blind_bsg2_pt, refl blind_bsg2_pt) ]

def blind_mu_E (hp : blind_xca_bigproduct_connected) (lem : blind_lem_parityequiv)
  (ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne) (E : FiniteSets)
  : BlindHom (blind_group_power hp E (blind_SG two)) (blind_SG two)
  ≔ blind_mu_E_dec hp lem ptg E (finite_inhabited_decidable (E .fst .fst) (E .snd))

{` xca (line 1570): under funext, USym mu_E (s) is the product of the
   values of s : E → {±1}; with {±1} = loops at bn 2 in BS_2 this says
   USym mu_E (s) = refl iff s takes the value -1 (≠ refl) an even number
   of times. `}
def blind_xca_mu_product : Type
  ≔ (hp : blind_xca_bigproduct_connected) (lem : blind_lem_parityequiv)
    (ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne) (E : FiniteSets)
    (s : E .fst .fst → Id BlindBSG2 blind_bsg2_pt blind_bsg2_pt) →
    let c : E .fst .fst → BlindBSG2 ≔ _ ↦ blind_bsg2_pt in
    BlindIff
      (Id (Id BlindBSG2 blind_bsg2_pt blind_bsg2_pt)
        (blind_usym_hom (blind_group_power hp E (blind_SG two)) (blind_SG two) (blind_mu_E hp lem ptg E)
          (funext (E .fst .fst) (_ ↦ BlindBSG2) c c s))
        (refl blind_bsg2_pt))
      (BlindEvenCard (Σ (E .fst .fst) (e ↦ Not (Id (Id BlindBSG2 blind_bsg2_pt blind_bsg2_pt) (s e) (refl blind_bsg2_pt)))))

{` def:sign-ordering: E(A) the 2-element subsets of A, P(e) the
   underlying 2-element set. `}
def BlindTwoSubsets (A : SetTypes) : Type ≔ Σ (Subtypes (A .fst)) (S ↦ TwoElement (SubtypeCarrier (A .fst) S))

def blind_two_subsets_set (A : SetTypes) : SetTypes
  ≔ (BlindTwoSubsets A, sigma_set (Subtypes (A .fst)) (S ↦ TwoElement (SubtypeCarrier (A .fst) S))
      (subtypes_set (A .fst))
      (S ↦ prop_is_set (TwoElement (SubtypeCarrier (A .fst) S)) (two_element_prop (SubtypeCarrier (A .fst) S))))

def blind_two_subset_family (A : SetTypes) (e : BlindTwoSubsets A) : BlindBSG2
  ≔ let X : SetTypes ≔ (SubtypeCarrier (A .fst) (e .fst),
      sigma_set (A .fst) (x ↦ e .fst x .fst) (A .snd) (x ↦ prop_is_set (e .fst x .fst) (e .fst x .snd))) in
    (X, blind_two_to_component X (e .snd))

def BlindLocalOrderings (A : SetTypes) : Type ≔ BlindLocalSections (BlindTwoSubsets A) (blind_two_subset_family A)
def BlindSignOrderings (A : SetTypes) : Type ≔ BlindParityQuotient (BlindTwoSubsets A) (blind_two_subset_family A)

{` def:sgn. The data the book uses implicitly are collected as
   hypotheses: xca:bigproductfunext (i) (for S_2^E), lem:parityequiv,
   the pointing of mu_E, finiteness of E(A) for finite A, and for each n
   the identification of every 2-element subset {i, j} of bn n with bn 2
   given by the total order (0 ↦ the smaller element). `}
def blind_fin_val (n : Nat) (x : Fin n) : Nat
  ≔ match n [
  | zero. ↦ match x [ ]
  | suc. m ↦ match x [ inl. y ↦ blind_fin_val m y | inr. _ ↦ m ] ]

def blind_bsn_finite (n : Nat) (A : NativeComponent SetTypes (blind_bn_set n)) : IsFinite (A .fst .fst)
  ≔ mere_rec (Id SetTypes (blind_bn_set n) (A .fst)) (IsFinite (A .fst .fst)) (mere_isprop (Σ Nat (m ↦ Id Type (A .fst .fst) (Fin m))))
      (p ↦ mere (Σ Nat (m ↦ Id Type (A .fst .fst) (Fin m)))
        (n, inverse Type (Fin n) (A .fst .fst) (map_path SetTypes Type (X ↦ X .fst) (blind_bn_set n) (A .fst) p)))
      (A .snd)

def BlindSignHyps : Type ≔ sig (
  hp : blind_xca_bigproduct_connected,
  lem : blind_lem_parityequiv,
  ptg : (E : FiniteSets) (ne : Mere (E .fst .fst)) → BlindMuPointing lem E ne,
  fin : (A : SetTypes) → IsFinite (A .fst) → IsFinite (BlindTwoSubsets A),
  ord : (n : Nat) (e : BlindTwoSubsets (blind_bn_set n)) →
    Σ (Id BlindBSG2 blind_bsg2_pt (blind_two_subset_family (blind_bn_set n) e)) (q ↦
      let t ≔ transport BlindBSG2 (X ↦ X .fst .fst) blind_bsg2_pt (blind_two_subset_family (blind_bn_set n) e) q in
      BookLt (blind_fin_val n (t blind_fin_two_zero .fst)) (blind_fin_val n (t blind_fin_two_one .fst))))

def blind_two_subsets_finite (H : BlindSignHyps) (A : SetTypes) (hA : IsFinite (A .fst)) : FiniteSets
  ≔ (blind_two_subsets_set A, H .fin A hA)

def BlindBSGn (n : Nat) : Type ≔ NativeComponent SetTypes (blind_bn_set n)

{` Deciding whether E(A) is nonempty, uniformly in A : BS_n, by the
   cardinality n (a match on the variable n): for n ≥ 2 the subset
   {n-2, n-1} of bn n, transported to A along the mere identification;
   for n ≤ 1 a 2-element subset would make the 2-element carrier, a
   subtype of the proposition A, a proposition. `}
def blind_last_two_low (m : Nat) (x : Fin (suc. m)) : PropTypes
  ≔ match x [ inl. _ ↦ (Empty, empty_prop) | inr. _ ↦ (Unit, unit_prop) ]

def blind_last_two (m : Nat) : Subtypes (Fin (suc. (suc. m)))
  ≔ [ inl. x ↦ blind_last_two_low m x | inr. _ ↦ (Unit, unit_prop) ]

def BlindLastTwo (m : Nat) : Type ≔ SubtypeCarrier (Fin (suc. (suc. m))) (blind_last_two m)

def blind_last_two_in_low (m : Nat) (y : Fin (suc. zero.)) : BlindLastTwo m
  ≔ match y [ inl. e ↦ match e [] | inr. u ↦ (inl. (inr. u), u) ]

def blind_last_two_in (m : Nat) : Fin two → BlindLastTwo m
  ≔ [ inl. y ↦ blind_last_two_in_low m y | inr. u ↦ (inr. u, u) ]

def blind_last_two_out_low (m : Nat) (z : Fin (suc. m)) (s : blind_last_two_low m z .fst) : Fin two
  ≔ match z [ inl. _ ↦ match s [] | inr. u ↦ inl. (inr. u) ]

def blind_last_two_out (m : Nat) (x : Fin (suc. (suc. m))) (s : blind_last_two m x .fst) : Fin two
  ≔ match x [ inl. z ↦ blind_last_two_out_low m z s | inr. u ↦ inr. u ]

def blind_last_two_eta (m : Nat) (a : Fin two)
  : Id (Fin two) (blind_last_two_out m (blind_last_two_in m a .fst) (blind_last_two_in m a .snd)) a
  ≔ match a [
  | inl. y ↦ match y [ inl. e ↦ match e [] | inr. u ↦ refl (inl. (inr. u) : Fin two) ]
  | inr. u ↦ refl (inr. u : Fin two) ]

def blind_last_two_eps_low (m : Nat) (z : Fin (suc. m)) (s : blind_last_two_low m z .fst)
  : Id (BlindLastTwo m) (blind_last_two_in m (blind_last_two_out_low m z s)) (inl. z, s)
  ≔ match z [
  | inl. _ ↦ match s []
  | inr. u ↦ match u [ star. ↦ match s [ star. ↦ refl ((inl. (inr. star.), star.) : BlindLastTwo m) ] ] ]

def blind_last_two_eps (m : Nat) (x : Fin (suc. (suc. m))) (s : blind_last_two m x .fst)
  : Id (BlindLastTwo m) (blind_last_two_in m (blind_last_two_out m x s)) (x, s)
  ≔ match x [
  | inl. z ↦ blind_last_two_eps_low m z s
  | inr. u ↦ match u [ star. ↦ match s [ star. ↦ refl ((inr. star., star.) : BlindLastTwo m) ] ] ]

def blind_last_two_equiv (m : Nat) : Equiv (Fin two) (BlindLastTwo m)
  ≔ quasi_inverse_equiv (Fin two) (BlindLastTwo m) (blind_last_two_in m)
      (c ↦ blind_last_two_out m (c .fst) (c .snd)) (blind_last_two_eta m)
      (c ↦ blind_last_two_eps m (c .fst) (c .snd))

def blind_last_two_subset (m : Nat) : BlindTwoSubsets (blind_bn_set (suc. (suc. m)))
  ≔ (blind_last_two m, mere (Id Type (Fin two) (BlindLastTwo m)) (ua (Fin two) (BlindLastTwo m) (blind_last_two_equiv m)))

def blind_two_subsets_inhabited (m : Nat) (A : BlindBSGn (suc. (suc. m))) : Mere (BlindTwoSubsets (A .fst))
  ≔ mere_rec (Id SetTypes (blind_bn_set (suc. (suc. m))) (A .fst)) (Mere (BlindTwoSubsets (A .fst)))
      (mere_isprop (BlindTwoSubsets (A .fst)))
      (p ↦ mere (BlindTwoSubsets (A .fst))
        (transport SetTypes BlindTwoSubsets (blind_bn_set (suc. (suc. m))) (A .fst) p (blind_last_two_subset m)))
      (A .snd)

def blind_fin_two_not_prop (h : isProp (Fin two)) : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit blind_fin_two_zero blind_fin_two_one (h blind_fin_two_zero blind_fin_two_one)

def blind_two_subset_of_prop (X : SetTypes) (hX : isProp (X .fst)) (e : BlindTwoSubsets X) : Empty
  ≔ let C ≔ SubtypeCarrier (X .fst) (e .fst) in
    mere_rec (Id Type (Fin two) C) Empty empty_prop
      (q ↦ blind_fin_two_not_prop
        (transport Type isProp C (Fin two) (inverse Type (Fin two) C q)
          (sigma_prop (X .fst) (x ↦ e .fst x .fst) hX (x ↦ e .fst x .snd))))
      (e .snd)

def blind_two_subsets_small (n : Nat) (hn : isProp (Fin n)) (A : BlindBSGn n) : Not (Mere (BlindTwoSubsets (A .fst)))
  ≔ t ↦
    let hA : isProp (A .fst .fst)
      ≔ mere_rec (Id SetTypes (blind_bn_set n) (A .fst)) (isProp (A .fst .fst)) (isprop_isprop (A .fst .fst))
          (p ↦ transport SetTypes (X ↦ isProp (X .fst)) (blind_bn_set n) (A .fst) p hn) (A .snd) in
    mere_rec (BlindTwoSubsets (A .fst)) Empty empty_prop (blind_two_subset_of_prop (A .fst) hA) t

def blind_fin_one_prop : isProp (Fin (suc. zero.))
  ≔ x y ↦ match x, y [
  | inl. e, _ ↦ match e []
  | inr. _, inl. e ↦ match e []
  | inr. u, inr. v ↦ inr. (unit_prop u v) ]

def blind_two_subsets_dec (n : Nat) (A : BlindBSGn n) : Decidable (Mere (BlindTwoSubsets (A .fst)))
  ≔ match n [
  | zero. ↦ inr. (blind_two_subsets_small zero. empty_prop A)
  | suc. k ↦ match k [
    | zero. ↦ inr. (blind_two_subsets_small (suc. zero.) blind_fin_one_prop A)
    | suc. m ↦ inl. (blind_two_subsets_inhabited m A) ] ]

{` Bμ_{E(A)} as a pointed map, with the decision above. `}
def blind_Bmu_sgn (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n)
  : BookPointedMap (blind_BG (blind_group_power (H .hp) (blind_two_subsets_finite H (A .fst) (blind_bsn_finite n A)) (blind_SG two)))
      (blind_BG (blind_SG two))
  ≔ let E ≔ blind_two_subsets_finite H (A .fst) (blind_bsn_finite n A) in
    blind_Bhom (blind_group_power (H .hp) E (blind_SG two)) (blind_SG two)
      (blind_mu_E_dec (H .hp) (H .lem) (H .ptg) E (blind_two_subsets_dec n A))

def blind_Bsgn_map (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) : BlindBSG2
  ≔ blind_Bmu_sgn H n A .fst (blind_two_subset_family (A .fst))

def blind_Bsgn_pt (H : BlindSignHyps) (n : Nat)
  : Id BlindBSG2 blind_bsg2_pt (blind_Bsgn_map H n (blind_component_point SetTypes (blind_bn_set n)))
  ≔ let A ≔ blind_component_point SetTypes (blind_bn_set n) in
    let E ≔ blind_two_subsets_finite H (A .fst) (blind_bsn_finite n A) in
    let Bmu ≔ blind_Bmu_sgn H n A in
    let c : E .fst .fst → BlindBSG2 ≔ _ ↦ blind_bsg2_pt in
    let P ≔ blind_two_subset_family (A .fst) in
    concat BlindBSG2 blind_bsg2_pt (Bmu .fst c) (Bmu .fst P) (Bmu .snd)
      (map_path (E .fst .fst → BlindBSG2) BlindBSG2 (Bmu .fst) c P
        (funext (E .fst .fst) (_ ↦ BlindBSG2) c P (e ↦ H .ord n e .fst)))

def blind_sgn (H : BlindSignHyps) (n : Nat) : BlindHom (blind_SG n) (blind_SG two)
  ≔ blind_mkhom (blind_SG n) (blind_SG two) (blind_Bsgn_map H n, blind_Bsgn_pt H n)

{` def:alternating-groups. The total type is connected only for n ≥ 2
   (for n ≤ 1 E(A) is empty and Bsgn is constant at bn 2, so the total
   type is FinSet_n × bn 2, which has two components); the group is
   parametrized by the pointed-connected-groupoid property. `}
def BlindAltCarrier (H : BlindSignHyps) (n : Nat) : Type ≔ Σ (BlindBSGn n) (A ↦ blind_Bsgn_map H n A .fst .fst)

def blind_alt_shape (H : BlindSignHyps) (n : Nat) : BlindAltCarrier H n
  ≔ (blind_component_point SetTypes (blind_bn_set n),
      transport BlindBSG2 (X ↦ X .fst .fst) blind_bsg2_pt (blind_Bsgn_map H n (blind_component_point SetTypes (blind_bn_set n)))
        (blind_Bsgn_pt H n) blind_fin_two_zero)

def BlindAltPtConn (H : BlindSignHyps) (n : Nat) : Type
  ≔ Product (Connected (BlindAltCarrier H n)) (isGroupoid (BlindAltCarrier H n))

def blind_AG (H : BlindSignHyps) (n : Nat) (h : BlindAltPtConn H n) : BlindGroup
  ≔ blind_mkgroup (BlindAltCarrier H n, (blind_alt_shape H n, (h .fst, h .snd)))

def blind_alt_ptconn : Type ≔ (H : BlindSignHyps) (n : Nat) → BlindAltPtConn H (suc. (suc. n))
def blind_alt_small_disconnected : Type
  ≔ (H : BlindSignHyps) → Product (Not (Connected (BlindAltCarrier H zero.))) (Not (Connected (BlindAltCarrier H (suc. zero.))))

{` xca:isos_A3_C3: two (distinct) isomorphisms A_3 → C_3. `}
def blind_xca_isos_A3_C3 : Type
  ≔ (H : BlindSignHyps) (h : BlindAltPtConn H blind_three) →
    let A ≔ blind_AG H blind_three h in
    let C ≔ blind_CG (suc. (suc. zero.)) in
    Σ (BlindIso A C) (f ↦ Σ (BlindIso A C) (g ↦ Not (Id (BlindIso A C) f g)))

{` def:sgn-permutation. A permutation σ of A : BS_n acts on Bsgn(A) by
   transport along ap Bsgn (ua σ); σ is odd (sign -1) if this swaps the
   two elements (has no fixed point), even (sign +1) if it is the
   identity. For n ≤ 1 Bsgn is constant, so every σ is even, as the
   book's clause for cardinality 0 or 1 requires. `}
{` The loop ua σ in BS_n, built as a pair (path of carriers, path over
   in the proposition parts) so that its carrier component is ua σ
   definitionally. `}
def blind_set_ua_loop (S : SetTypes) (σ : Equiv (S .fst) (S .fst)) : Id SetTypes S S
  ≔ let p ≔ ua (S .fst) (S .fst) σ in
    (p, pathover_of_eq Type isSet (S .fst) (S .fst) p (S .snd) (S .snd)
      (isset_isprop (S .fst) (transport Type isSet (S .fst) (S .fst) p (S .snd)) (S .snd)))

def blind_bsgn_loop (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst)) : Id (BlindBSGn n) A A
  ≔ let p ≔ blind_set_ua_loop (A .fst) σ in
    let M : SetTypes → Type ≔ X ↦ Mere (Id SetTypes (blind_bn_set n) X) in
    (p, pathover_of_eq SetTypes M (A .fst) (A .fst) p (A .snd) (A .snd)
      (mere_isprop (Id SetTypes (blind_bn_set n) (A .fst)) (transport SetTypes M (A .fst) (A .fst) p (A .snd)) (A .snd)))

def blind_sgn_action (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst))
  : blind_Bsgn_map H n A .fst .fst → blind_Bsgn_map H n A .fst .fst
  ≔ transport BlindBSG2 (X ↦ X .fst .fst) (blind_Bsgn_map H n A) (blind_Bsgn_map H n A)
      (map_path (BlindBSGn n) BlindBSG2 (blind_Bsgn_map H n) A A (blind_bsgn_loop n A σ))

def BlindPermEven (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst)) : Type
  ≔ (x : blind_Bsgn_map H n A .fst .fst) → Id (blind_Bsgn_map H n A .fst .fst) (blind_sgn_action H n A σ x) x
def BlindPermOdd (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (σ : Equiv (A .fst .fst) (A .fst .fst)) : Type
  ≔ (x : blind_Bsgn_map H n A .fst .fst) → Not (Id (blind_Bsgn_map H n A .fst .fst) (blind_sgn_action H n A σ x) x)

{` lem:sign-properties. (1) transpositions are odd; (2) a k-cycle
   (k = j+2, IsKCycle of chapter 3) is even iff k is odd; (3) a word of
   transpositions composing to the identity has even length. Decidable
   equality of A is quantified (it is a proposition for finite sets). `}
def blind_lem_sign_transposition : Type
  ≔ (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (d : DecidableEquality (A .fst .fst))
    (a b : A .fst .fst) → Not (Id (A .fst .fst) a b) →
    BlindPermOdd H n A (transposition_equiv (A .fst .fst) d a b)

def blind_lem_sign_cycle : Type
  ≔ (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (j : Nat) (σ : Equiv (A .fst .fst) (A .fst .fst)) →
    IsKCycle (A .fst .fst) j σ →
    Product (Id Bool (blind_nat_even (suc. (suc. j))) false. → BlindPermEven H n A σ)
      (Id Bool (blind_nat_even (suc. (suc. j))) true. → BlindPermOdd H n A σ)

def blind_lem_sign_identity_even : Type
  ≔ (A : Type) (hA : IsFinite A) (d : DecidableEquality A) (w : List (Transpositions A)) →
    Id (A → A) (transposition_word_map A d w) (identity A) →
    Id Bool (blind_nat_even (length (Transpositions A) w)) true.

{` cor:sign-defined. `}
def blind_cor_sign_defined : Type
  ≔ (H : BlindSignHyps) (n : Nat) (A : BlindBSGn n) (d : DecidableEquality (A .fst .fst))
    (σ : Equiv (A .fst .fst) (A .fst .fst)) (w v : List (Transpositions (A .fst .fst))) →
    Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d w) (σ .map) →
    Id (A .fst .fst → A .fst .fst) (transposition_word_map (A .fst .fst) d v) (σ .map) →
    Product (Id Bool (blind_nat_even (length (Transpositions (A .fst .fst)) w)) (blind_nat_even (length (Transpositions (A .fst .fst)) v)))
      (Product (Id Bool (blind_nat_even (length (Transpositions (A .fst .fst)) w)) true. → BlindPermEven H n A σ)
        (Id Bool (blind_nat_even (length (Transpositions (A .fst .fst)) w)) false. → BlindPermOdd H n A σ))

{` xca:sign-by-crossings: σ of bn n is even iff its number of inversions
   (pairs i < j with σ(i) > σ(j)) is even. `}
def BlindInversions (n : Nat) (σ : Equiv (Fin n) (Fin n)) : Type
  ≔ Σ (Fin n) (i ↦ Σ (Fin n) (j ↦ Product (BookLt (blind_fin_val n i) (blind_fin_val n j))
      (BookLt (blind_fin_val n (σ .map j)) (blind_fin_val n (σ .map i)))))

def blind_xca_sign_by_crossings : Type
  ≔ (H : BlindSignHyps) (n : Nat) (σ : Equiv (Fin n) (Fin n)) (k : Nat) →
    Mere (Id Type (BlindInversions n σ) (Fin k)) →
    BlindIff (BlindPermEven H n (blind_component_point SetTypes (blind_bn_set n)) σ) (Id Bool (blind_nat_even k) true.)

{` xca (line 1779): for n ≥ 2 there are n!/2 even permutations of bn n,
   stated as 2 × #even = n!. `}
def blind_xca_even_count : Type
  ≔ (H : BlindSignHyps) (n : Nat) →
    let m : Nat ≔ suc. (suc. n) in
    Mere (Id Type (Product (Fin two) (Σ (Equiv (Fin m) (Fin m)) (BlindPermEven H m (blind_component_point SetTypes (blind_bn_set m)))))
      (Fin (factorial m)))

{` ---- Litmus checks (by refl): the sign definitions compute. ---- `}
def blind_fin3_0 : Fin blind_three ≔ inl. (inl. (inr. star.))
def blind_fin3_1 : Fin blind_three ≔ inl. (inr. star.)
def blind_fin3_2 : Fin blind_three ≔ inr. star.
def blind_bsgn_pt (n : Nat) : BlindBSGn n ≔ blind_component_point SetTypes (blind_bn_set n)
def blind_tau01 : Equiv (Fin blind_three) (Fin blind_three)
  ≔ transposition_equiv (Fin blind_three) (fin_decidable_equality blind_three) blind_fin3_0 blind_fin3_1

{` For n = 2, 3 and every A : BS_n, Bsgn(A) is the set of sign orderings of A
   (μ_{E(A)} takes its nonempty branch). `}
def blind_litmus_bsgn_two (H : BlindSignHyps) (A : BlindBSGn two)
  : Id Type (blind_Bsgn_map H two A .fst .fst) (BlindSignOrderings (A .fst))
  ≔ refl (BlindSignOrderings (A .fst))
def blind_litmus_bsgn_three (H : BlindSignHyps) (A : BlindBSGn blind_three)
  : Id Type (blind_Bsgn_map H blind_three A .fst .fst) (BlindSignOrderings (A .fst))
  ≔ refl (BlindSignOrderings (A .fst))

{` For n = 0, 1, Bsgn is constant at bn 2, and the sign action is transport along
   refl (definitionally), hence the identity. `}
def blind_litmus_bsgn_zero (H : BlindSignHyps) (A : BlindBSGn zero.) : Id BlindBSG2 (blind_Bsgn_map H zero. A) blind_bsg2_pt
  ≔ refl blind_bsg2_pt
def blind_litmus_bsgn_one (H : BlindSignHyps) (A : BlindBSGn (suc. zero.)) : Id BlindBSG2 (blind_Bsgn_map H (suc. zero.) A) blind_bsg2_pt
  ≔ refl blind_bsg2_pt
def blind_litmus_sgn_action_one (H : BlindSignHyps) (A : BlindBSGn (suc. zero.)) (σ : Equiv (A .fst .fst) (A .fst .fst))
  (x : Fin two) : Id (Fin two) (blind_sgn_action H (suc. zero.) A σ x) x
  ≔ transport_refl BlindBSG2 (X ↦ X .fst .fst) blind_bsg2_pt x

{` The loop of a transposition moves points as the transposition does. `}
def blind_litmus_loop_tau
  : Id (Fin blind_three)
      (transport (BlindBSGn blind_three) (A ↦ A .fst .fst) (blind_bsgn_pt blind_three) (blind_bsgn_pt blind_three)
        (blind_bsgn_loop blind_three (blind_bsgn_pt blind_three) blind_tau01) blind_fin3_0)
      blind_fin3_1
  ≔ refl blind_fin3_1

{` The sign action of σ is transport of sign orderings along ua σ (def:sgn-permutation),
   on bn 2 for the swap (blind_swap2 of 01-groups) and on bn 3 for the transposition (0 1). `}
def blind_litmus_sgn_action_swap2 (H : BlindSignHyps)
  : Id (BlindSignOrderings (blind_bn_set two) → BlindSignOrderings (blind_bn_set two))
      (blind_sgn_action H two (blind_bsgn_pt two) blind_swap2)
      (transport (BlindBSGn two) (A ↦ BlindSignOrderings (A .fst)) (blind_bsgn_pt two) (blind_bsgn_pt two)
        (blind_bsgn_loop two (blind_bsgn_pt two) blind_swap2))
  ≔ refl (transport (BlindBSGn two) (A ↦ BlindSignOrderings (A .fst)) (blind_bsgn_pt two) (blind_bsgn_pt two)
        (blind_bsgn_loop two (blind_bsgn_pt two) blind_swap2))
def blind_litmus_sgn_action_tau01 (H : BlindSignHyps)
  : Id (BlindSignOrderings (blind_bn_set blind_three) → BlindSignOrderings (blind_bn_set blind_three))
      (blind_sgn_action H blind_three (blind_bsgn_pt blind_three) blind_tau01)
      (transport (BlindBSGn blind_three) (A ↦ BlindSignOrderings (A .fst)) (blind_bsgn_pt blind_three) (blind_bsgn_pt blind_three)
        (blind_bsgn_loop blind_three (blind_bsgn_pt blind_three) blind_tau01))
  ≔ refl (transport (BlindBSGn blind_three) (A ↦ BlindSignOrderings (A .fst)) (blind_bsgn_pt blind_three) (blind_bsgn_pt blind_three)
        (blind_bsgn_loop blind_three (blind_bsgn_pt blind_three) blind_tau01))

{` The transposition (0 1) moves the 2-element subset S = {1, 2} of bn 3 to
   {0, 2}: the transported predicate at x computes to S(τ(x)) (up to transport
   along refl in the constant family PropTypes, which Narya does not reduce on
   Σ-types); so at 0 it is S(1) = Unit, at 1 it is S(0) = Empty. `}
def blind_litmus_subset_tau01_at0
  : Id PropTypes
      (transport (BlindBSGn blind_three) (A ↦ BlindTwoSubsets (A .fst)) (blind_bsgn_pt blind_three) (blind_bsgn_pt blind_three)
        (blind_bsgn_loop blind_three (blind_bsgn_pt blind_three) blind_tau01) (blind_last_two_subset (suc. zero.)) .fst blind_fin3_0)
      (refl PropTypes .trr.1 (blind_last_two (suc. zero.) blind_fin3_1))
  ≔ refl (refl PropTypes .trr.1 (blind_last_two (suc. zero.) blind_fin3_1))
def blind_litmus_subset_tau01_at1
  : Id PropTypes
      (transport (BlindBSGn blind_three) (A ↦ BlindTwoSubsets (A .fst)) (blind_bsgn_pt blind_three) (blind_bsgn_pt blind_three)
        (blind_bsgn_loop blind_three (blind_bsgn_pt blind_three) blind_tau01) (blind_last_two_subset (suc. zero.)) .fst blind_fin3_1)
      (refl PropTypes .trr.1 (blind_last_two (suc. zero.) blind_fin3_0))
  ≔ refl (refl PropTypes .trr.1 (blind_last_two (suc. zero.) blind_fin3_0))
