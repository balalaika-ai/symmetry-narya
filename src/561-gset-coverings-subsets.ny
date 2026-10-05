export "501-transitive-gsets"

{` Chapter 5 (actions.tex), sec:gsets: G-sets as coverings
   (rem:G-set-vs-set-bundle), maps of G-sets as maps of total types over BG
   (xca:equivariant-map-totalization), G-subsets as subtypes of the total
   type (ft:SubTotX of def:Gsubset) and as subsets of the underlying set
   closed under the action (xca:SubGX-closedSubXshG). `}

{` rem:G-set-vs-set-bundle. The type of G-sets is equivalent to the type of
   coverings over BG (coverings_setfamilies_equiv, chapter 3). The map sends
   X to the covering fst : Σ_{z:BG} X(z) → BG (gset_coverings_equiv_total,
   gset_coverings_equiv_projection, both refl). `}
def gset_coverings_equiv (G : Group) : Equiv (GSet G) (Coverings (BG G .carrier))
  ≔ canonical_inverse_equiv (Coverings (BG G .carrier)) (GSet G) (coverings_setfamilies_equiv (BG G .carrier))

def gset_coverings_equiv_total (G : Group) (X : GSet G)
  : Id Type (gset_coverings_equiv G .map X .fst) (ActionType G X)
  ≔ refl (ActionType G X)

def gset_coverings_equiv_projection (G : Group) (X : GSet G)
  : Id (ActionType G X → BG G .carrier) (gset_coverings_equiv G .map X .snd .fst) (u ↦ u .fst)
  ≔ refl ((u ↦ u .fst) : ActionType G X → BG G .carrier)

{` The inverse sends a covering to its family of fibers. `}
def gset_coverings_equiv_inverse (G : Group) (c : Coverings (BG G .carrier)) (z : BG G .carrier)
  : Id Type
      (equiv_inverse_map (GSet G) (Coverings (BG G .carrier)) (gset_coverings_equiv G) c z .fst)
      (BookFiber (c .fst) (BG G .carrier) (c .snd .fst) z)
  ≔ refl (BookFiber (c .fst) (BG G .carrier) (c .snd .fst) z)

{` xca:equivariant-map-totalization, for any families X, Y over a type B:
   maps of families Π_b (X(b) → Y(b)) ≃ functions f : Tot(X) → Tot(Y)
   with fst = fst ∘ f. Chain: Σ-functions are pairs (choice), contract
   away (f₁, fst = f₁) (lem:contract-away), curry (xca:Sigma-curry). `}
def fiberwise_maps_over_equiv (B : Type) (X Y : B → Type)
  : Equiv (Σ (Σ B X → Σ B Y) (f ↦ Id (Σ B X → B) (t ↦ t .fst) (t ↦ f t .fst))) ((b : B) → X b → Y b)
  ≔ let TX ≔ Σ B X in
    let TY ≔ Σ B Y in
    let S0 ≔ Σ (TX → TY) (f ↦ Id (TX → B) (t ↦ t .fst) (t ↦ f t .fst)) in
    let S1 ≔ Σ (Σ (TX → B) (f1 ↦ (t : TX) → Y (f1 t))) (p ↦ Id (TX → B) (t ↦ t .fst) (p .fst)) in
    let S2 ≔ Σ (TX → B) (f1 ↦ Σ (Id (TX → B) (t ↦ t .fst) f1) (_ ↦ (t : TX) → Y (f1 t))) in
    let S3 ≔ (t : TX) → Y (t .fst) in
    let S4 ≔ (b : B) → X b → Y b in
    compose_equiv S0 S1 S4
      (quasi_inverse_equiv S0 S1
        (u ↦ ((t ↦ u .fst t .fst, t ↦ u .fst t .snd), u .snd))
        (v ↦ (t ↦ (v .fst .fst t, v .fst .snd t), v .snd))
        (u ↦ refl u) (v ↦ refl v))
      (compose_equiv S1 S2 S4
        (quasi_inverse_equiv S1 S2
          (v ↦ (v .fst .fst, (v .snd, v .fst .snd)))
          (w ↦ ((w .fst, w .snd .snd), w .snd .fst))
          (v ↦ refl v) (w ↦ refl w))
        (compose_equiv S2 S3 S4
          (contract_away_equiv (TX → B) (t ↦ t .fst) (f1 _ ↦ (t : TX) → Y (f1 t)))
          (curry_equiv B X (b _ ↦ Y b))))

{` xca:equivariant-map-totalization for G-sets:
   Hom_G(X, Y) ≃ Σ_{f : Tot(X) → Tot(Y)} (fst = fst ∘ f). The map sends h to
   its totalization (z, x) ↦ (z, h_z(x)) with reflexivity
   (gset_hom_totalization_map, refl). `}
def gset_hom_totalization_equiv (G : Group) (X Y : GSet G)
  : Equiv (GSetHom G X Y)
      (Σ (ActionType G X → ActionType G Y) (f ↦ Id (ActionType G X → BG G .carrier) (t ↦ t .fst) (t ↦ f t .fst)))
  ≔ canonical_inverse_equiv
      (Σ (ActionType G X → ActionType G Y) (f ↦ Id (ActionType G X → BG G .carrier) (t ↦ t .fst) (t ↦ f t .fst)))
      (GSetHom G X Y)
      (fiberwise_maps_over_equiv (BG G .carrier) (z ↦ X z .fst) (z ↦ Y z .fst))

def gset_hom_totalization_map (G : Group) (X Y : GSet G) (h : GSetHom G X Y)
  : Id (Σ (ActionType G X → ActionType G Y) (f ↦ Id (ActionType G X → BG G .carrier) (t ↦ t .fst) (t ↦ f t .fst)))
      (gset_hom_totalization_equiv G X Y .map h)
      (totalize (BG G .carrier) (z ↦ X z .fst) (z ↦ Y z .fst) h, refl ((t ↦ t .fst) : ActionType G X → BG G .carrier))
  ≔ refl (gset_hom_totalization_equiv G X Y .map h)

{` ft:SubTotX. Sub_G(X) is, by uncurrying (xca:Sigma-curry), the type
   Tot(X) → Prop of subtypes of Tot(X); the map is uncurrying
   (gsubsets_total_equiv_map, refl). `}
def gsubsets_total_equiv (G : Group) (X : GSet G) : Equiv (GSubsets G X) (Subtypes (ActionType G X))
  ≔ canonical_inverse_equiv (Subtypes (ActionType G X)) (GSubsets G X)
      (curry_equiv (BG G .carrier) (z ↦ X z .fst) (_ _ ↦ PropTypes))

def gsubsets_total_equiv_map (G : Group) (X : GSet G) (P : GSubsets G X) (z : BG G .carrier) (x : X z .fst)
  : Id PropTypes (gsubsets_total_equiv G X .map P (z, x)) (P z x)
  ≔ refl (P z x)

{` xca:SubGX-closedSubXshG. The subsets of X(sh_G) closed under the action:
   Σ_{Q : Sub(X(sh_G))} Π_{x} (Q(x) → Π_{g : USym G} Q(g · x)). `}
def GSetClosedSubsets (G : Group) (X : GSet G) : Type
  ≔ Σ (Subtypes (gset_underlying G X))
      (Q ↦ (x : gset_underlying G X) → Q x .fst → (g : USym G) → Q (gset_usym_act G X g x) .fst)

def gset_closed_condition_prop (G : Group) (X : GSet G) (Q : Subtypes (gset_underlying G X))
  : isProp ((x : gset_underlying G X) → Q x .fst → (g : USym G) → Q (gset_usym_act G X g x) .fst)
  ≔ pi_prop (gset_underlying G X) (x ↦ Q x .fst → (g : USym G) → Q (gset_usym_act G X g x) .fst)
      (x ↦ pi_prop (Q x .fst) (_ ↦ (g : USym G) → Q (gset_usym_act G X g x) .fst)
        (_ ↦ pi_prop (USym G) (g ↦ Q (gset_usym_act G X g x) .fst) (g ↦ Q (gset_usym_act G X g x) .snd)))

{` Evaluation at sh_G (with the closure property from rem:map-of-Gsets). `}
def gsubset_restrict_closed (G : Group) (X : GSet G) (P : GSubsets G X) : GSetClosedSubsets G X
  ≔ (P (shape G), x px g ↦ gsubset_invariant_iff G X P (shape G) (shape G) g x .snd px)

{` The inverse: Q ↦ (z, x) ↦ Π_{p : z = sh_G} Q(p · x). `}
def gsubset_extend (G : Group) (X : GSet G) (Q : GSetClosedSubsets G X) : GSubsets G X
  ≔ z x ↦ ((p : Id (BG G .carrier) z (shape G)) → Q .fst (gset_act G X z (shape G) p x) .fst,
      pi_prop (Id (BG G .carrier) z (shape G)) (p ↦ Q .fst (gset_act G X z (shape G) p x) .fst)
        (p ↦ Q .fst (gset_act G X z (shape G) p x) .snd))

def gsubset_extend_restrict (G : Group) (X : GSet G) (P : GSubsets G X)
  : Id (GSubsets G X) (gsubset_extend G X (gsubset_restrict_closed G X P)) P
  ≔ let B ≔ BG G .carrier in
    let E ≔ gsubset_extend G X (gsubset_restrict_closed G X P) in
    funext B (z ↦ X z .fst → PropTypes) E P
      (z ↦ funext (X z .fst) (_ ↦ PropTypes) (E z) (P z)
        (x ↦ proposition_extensionality (E z x) (P z x)
          (h ↦ mere_rec (Id B z (shape G)) (P z x .fst) (P z x .snd)
            (p ↦ gsubset_invariant_iff G X P z (shape G) p x .fst (h p))
            (bg_connected G .snd z (shape G)))
          (px p ↦ gsubset_invariant_iff G X P z (shape G) p x .snd px)))

def gsubset_restrict_extend (G : Group) (X : GSet G) (Q : GSetClosedSubsets G X)
  : Id (GSetClosedSubsets G X) (gsubset_restrict_closed G X (gsubset_extend G X Q)) Q
  ≔ let S ≔ gset_underlying G X in
    let R ≔ gsubset_restrict_closed G X (gsubset_extend G X Q) in
    subtype_equal (Subtypes S)
      (Q' ↦ (x : S) → Q' x .fst → (g : USym G) → Q' (gset_usym_act G X g x) .fst)
      (gset_closed_condition_prop G X) R Q
      (funext S (_ ↦ PropTypes) (R .fst) (Q .fst)
        (x ↦ proposition_extensionality (R .fst x) (Q .fst x)
          (h ↦ transport S (y ↦ Q .fst y .fst) (gset_act G X (shape G) (shape G) (refl (shape G)) x) x
            (gset_act_refl G X (shape G) x) (h (refl (shape G))))
          (qx p ↦ Q .snd x qx p)))

{` xca:SubGX-closedSubXshG: evaluation at sh_G is an equivalence from
   Sub_G(X) to the closed subsets of X(sh_G). `}
def gsubsets_closed_equiv (G : Group) (X : GSet G) : Equiv (GSubsets G X) (GSetClosedSubsets G X)
  ≔ quasi_inverse_equiv (GSubsets G X) (GSetClosedSubsets G X)
      (gsubset_restrict_closed G X) (gsubset_extend G X)
      (gsubset_extend_restrict G X) (gsubset_restrict_extend G X)

def gsubsets_closed_equiv_eval (G : Group) (X : GSet G) (P : GSubsets G X)
  : Id (Subtypes (gset_underlying G X)) (gsubsets_closed_equiv G X .map P .fst) (P (shape G))
  ≔ refl (P (shape G))

{` Litmus: the full subset of X(sh_G) is closed, and the G-subset it
   extends to holds everywhere. `}
def gsubset_full_closed (G : Group) (X : GSet G) : GSetClosedSubsets G X
  ≔ (_ ↦ (Unit, unit_prop), x _ g ↦ star.)

def gsubset_full_extend_true (G : Group) (X : GSet G) (z : BG G .carrier) (x : X z .fst)
  : gsubset_extend G X (gsubset_full_closed G X) z x .fst
  ≔ _ ↦ star.
