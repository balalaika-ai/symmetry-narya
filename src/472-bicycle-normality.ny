export "471-bicycle-paths"

{` lem:evisinj-bicycle, def:normal-bicycle, xca:normal-bicycle-equiv,
   def:cbid-bicycle and the claims after it (group.tex 2063–2133). `}

{` Two maps out of a bicycle structure that commute with a, b and agree at
   one point agree everywhere (the proof of lem:evisinj-bicycle: list
   induction gives h⟦ℓ⟧ = ⟦ℓ⟧'h, then connectivity). `}
def bicycle_commuting_maps_agree (X Y : Type) (hY : isSet Y) (a b : Equiv X X) (a' b' : Equiv Y Y)
  (c : BicycleConnected X a b) (h k : X → Y)
  (ha : Commutes X Y a a' h) (hb : Commutes X Y b b' h) (ka : Commutes X Y a a' k) (kb : Commutes X Y b b' k)
  (x0 : X) (p : Id Y (h x0) (k x0)) (y : X) : Id Y (h y) (k y)
  ≔ mere_rec (BicycleWordFrom X a b x0 y) (Id Y (h y) (k y)) (hY (h y) (k y))
      (w ↦ calc
        h y = h (bicycle_meaning_map X a b (w .fst) x0) by refl h (w .snd)
        = bicycle_meaning_map Y a' b' (w .fst) (h x0) by bicycle_meaning_intertwine X Y a b a' b' h ha hb (w .fst) x0
        = bicycle_meaning_map Y a' b' (w .fst) (k x0) by refl (bicycle_meaning_map Y a' b' (w .fst)) p
        = k (bicycle_meaning_map X a b (w .fst) x0)
          by inverse Y (k (bicycle_meaning_map X a b (w .fst) x0)) (bicycle_meaning_map Y a' b' (w .fst) (k x0))
            (bicycle_meaning_intertwine X Y a b a' b' k ka kb (w .fst) x0)
        = k y by inverse Y (k y) (k (bicycle_meaning_map X a b (w .fst) x0)) (refl k (w .snd)) ∎)
      (c .snd x0 y)

def bicycle_iso_ext (B B' : Bicycles) (e d : BicycleIsomorphisms B B') (x0 : bicycle_carrier B)
  (p : Id (bicycle_carrier B') (e .fst .map x0) (d .fst .map x0)) : Id (BicycleIsomorphisms B B') e d
  ≔ subtype_equal (Equiv (bicycle_carrier B) (bicycle_carrier B'))
      (f ↦ BicycleCommutations (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (f .map))
      (f ↦ bicycle_commutations_prop (bicycle_set B) (bicycle_set B') (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (f .map))
      e d
      (equiv_homotopy (bicycle_carrier B) (bicycle_carrier B') (e .fst) (d .fst)
        (bicycle_commuting_maps_agree (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier_set B')
          (bicycle_a B) (bicycle_b B) (bicycle_a B') (bicycle_b B') (bicycle_connectivity B)
          (e .fst .map) (d .fst .map) (e .snd .fst) (e .snd .snd) (d .snd .fst) (d .snd .snd) x0 p))

{` lem:evisinj-bicycle: ev_{x₀} : ((X,a,b) = (X',a',b')) → X', e ↦ e(x₀),
   reflects paths, hence is injective in the sense of def:injection
   (propositional book fibers), X' being a set. `}
def bicycle_evaluation_path_reflecting (B B' : Bicycles) (x0 : bicycle_carrier B)
  : PathReflecting (Id Bicycles B B') (bicycle_carrier B') (p ↦ bicycle_path_evaluate B B' p x0)
  ≔ p q h ↦
      let E ≔ bicycle_paths_equiv B B' in
      let Einv ≔ equiv_inverse_map (Id Bicycles B B') (BicycleIsomorphisms B B') E in
      calc
        p = Einv (E .map p)
          by inverse (Id Bicycles B B') (Einv (E .map p)) p (equiv_retraction (Id Bicycles B B') (BicycleIsomorphisms B B') E p)
        = Einv (E .map q) by refl Einv (bicycle_iso_ext B B' (E .map p) (E .map q) x0 h)
        = q by equiv_retraction (Id Bicycles B B') (BicycleIsomorphisms B B') E q ∎

def bicycle_evaluation_injective (B B' : Bicycles) (x0 : bicycle_carrier B)
  : IsEmbedding (Id Bicycles B B') (bicycle_carrier B') (p ↦ bicycle_path_evaluate B B' p x0)
  ≔ path_reflecting_set_embedding (Id Bicycles B B') (bicycle_carrier B') (bicycle_carrier_set B')
      (p ↦ bicycle_path_evaluate B B' p x0) (bicycle_evaluation_path_reflecting B B' x0)

{` Identity, inverse and composite of bicycle isomorphisms. `}
def bicycle_iso_id (B : Bicycles) : BicycleIsomorphisms B B
  ≔ (identity_equiv (bicycle_carrier B),
      (x ↦ refl (bicycle_a B .map x), x ↦ refl (bicycle_b B .map x)))

def bicycle_commutes_inverse (X Y : Type) (a : Equiv X X) (a' : Equiv Y Y) (e : Equiv X Y)
  (h : Commutes X Y a a' (e .map)) : Commutes Y X a' a (equiv_inverse_map X Y e)
  ≔ y ↦ let g ≔ equiv_inverse_map X Y e in calc
      g (a' .map y) = g (a' .map (e .map (g y)))
        by refl ((z ↦ g (a' .map z)) : Y → X) (inverse Y (e .map (g y)) y (equiv_counit X Y e y))
      = g (e .map (a .map (g y))) by refl g (inverse Y (e .map (a .map (g y))) (a' .map (e .map (g y))) (h (g y)))
      = a .map (g y) by equiv_retraction X Y e (a .map (g y)) ∎

def bicycle_iso_inverse (B B' : Bicycles) (e : BicycleIsomorphisms B B') : BicycleIsomorphisms B' B
  ≔ (canonical_inverse_equiv (bicycle_carrier B) (bicycle_carrier B') (e .fst),
      (bicycle_commutes_inverse (bicycle_carrier B) (bicycle_carrier B') (bicycle_a B) (bicycle_a B') (e .fst) (e .snd .fst),
       bicycle_commutes_inverse (bicycle_carrier B) (bicycle_carrier B') (bicycle_b B) (bicycle_b B') (e .fst) (e .snd .snd)))

def bicycle_iso_compose (B B' B'' : Bicycles) (e : BicycleIsomorphisms B B') (d : BicycleIsomorphisms B' B'')
  : BicycleIsomorphisms B B''
  ≔ (compose_equiv (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier B'') (e .fst) (d .fst),
      (x ↦ concat (bicycle_carrier B'')
          (d .fst .map (e .fst .map (bicycle_a B .map x)))
          (d .fst .map (bicycle_a B' .map (e .fst .map x)))
          (bicycle_a B'' .map (d .fst .map (e .fst .map x)))
          (refl (d .fst .map) (e .snd .fst x)) (d .snd .fst (e .fst .map x)),
       x ↦ concat (bicycle_carrier B'')
          (d .fst .map (e .fst .map (bicycle_b B .map x)))
          (d .fst .map (bicycle_b B' .map (e .fst .map x)))
          (bicycle_b B'' .map (d .fst .map (e .fst .map x)))
          (refl (d .fst .map) (e .snd .snd x)) (d .snd .snd (e .fst .map x))))

{` Evaluation of reflexivity and of composite paths. `}
def bicycle_path_evaluate_refl (B : Bicycles) (x : bicycle_carrier B)
  : Id (bicycle_carrier B) (bicycle_path_evaluate B B (refl B) x) x
  ≔ transport_refl Type (Y ↦ Y) (bicycle_carrier B) x

def bicycle_path_evaluate_concat (B B' B'' : Bicycles) (p : Id Bicycles B B') (q : Id Bicycles B' B'')
  (x : bicycle_carrier B)
  : Id (bicycle_carrier B'') (bicycle_path_evaluate B B'' (concat Bicycles B B' B'' p q) x)
      (bicycle_path_evaluate B' B'' q (bicycle_path_evaluate B B' p x))
  ≔ concat (bicycle_carrier B'')
      (bicycle_path_evaluate B B'' (concat Bicycles B B' B'' p q) x)
      (transport Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B'')
        (concat Type (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier B'') (p .fst .fst) (q .fst .fst)) x)
      (bicycle_path_evaluate B' B'' q (bicycle_path_evaluate B B' p x))
      (refl ((r ↦ transport Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B'') r x)
          : Id Type (bicycle_carrier B) (bicycle_carrier B'') → bicycle_carrier B'')
        (map_path_concat Bicycles Type (u ↦ u .fst .fst) B B' B'' p q))
      (transport_concat Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B') (bicycle_carrier B'')
        (p .fst .fst) (q .fst .fst) x)

def bicycle_path_evaluate_inverse (B B' : Bicycles) (p : Id Bicycles B B') (x : bicycle_carrier B)
  : Id (bicycle_carrier B) (bicycle_path_evaluate B' B (inverse Bicycles B B' p) (bicycle_path_evaluate B B' p x)) x
  ≔ concat (bicycle_carrier B)
      (bicycle_path_evaluate B' B (inverse Bicycles B B' p) (bicycle_path_evaluate B B' p x))
      (transport Type (Y ↦ Y) (bicycle_carrier B') (bicycle_carrier B)
        (inverse Type (bicycle_carrier B) (bicycle_carrier B') (p .fst .fst)) (bicycle_path_evaluate B B' p x))
      x
      (refl ((r ↦ transport Type (Y ↦ Y) (bicycle_carrier B') (bicycle_carrier B) r (bicycle_path_evaluate B B' p x))
          : Id Type (bicycle_carrier B') (bicycle_carrier B) → bicycle_carrier B)
        (map_path_inverse Bicycles Type (u ↦ u .fst .fst) B B' p))
      (transport_inverse_roundtrip Type (Y ↦ Y) (bicycle_carrier B) (bicycle_carrier B') (p .fst .fst) x)

{` def:normal-bicycle. ev_x : ((X,a,b) = (X,a,b)) → X, e ↦ e(x), and
   normality: ev_x is an equivalence (book orientation) for all x : X. `}
def bicycle_evaluation (B : Bicycles) (x : bicycle_carrier B) : Id Bicycles B B → bicycle_carrier B
  ≔ p ↦ bicycle_path_evaluate B B p x

def IsNormalBicycle (B : Bicycles) : Type
  ≔ (x : bicycle_carrier B) → BookIsEquiv (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x)

def is_normal_bicycle_prop (B : Bicycles) : isProp (IsNormalBicycle B)
  ≔ pi_prop (bicycle_carrier B) (x ↦ BookIsEquiv (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x))
      (x ↦ book_isequiv_isprop (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x))

def NormalBicycles : Type ≔ Σ Bicycles IsNormalBicycle

def bicycle_evaluation_equiv (B : Bicycles) (h : IsNormalBicycle B) (x : bicycle_carrier B)
  : BookEquiv (Id Bicycles B B) (bicycle_carrier B)
  ≔ (bicycle_evaluation B x, h x)

{` xca:normal-bicycle-equiv. If ev_x is an equivalence for some x, then
   for all y, z there is a symmetry sending y to z (namely e_z ∘ e_y⁻¹ with
   e_y = ev_x⁻¹(y)), so ev_y is injective and surjective, hence an
   equivalence (lem:inj+surj). `}
def bicycle_symmetry_between (B : Bicycles) (x : bicycle_carrier B)
  (h : BookIsEquiv (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x)) (y z : bicycle_carrier B)
  : BookFiber (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B y) z
  ≔ let X ≔ bicycle_carrier B in
    let E ≔ bicycle_paths_equiv B B in
    let ey ≔ E .map (h y .center .fst) in
    let ez ≔ E .map (h z .center .fst) in
    let iso ≔ bicycle_iso_compose B B B (bicycle_iso_inverse B B ey) ez in
    (bicycle_path_from_iso B B iso, calc
      z = ez .fst .map x by h z .center .snd
      = ez .fst .map (equiv_inverse_map X X (ey .fst) (ey .fst .map x))
        by refl (ez .fst .map) (equiv_unit X X (ey .fst) x)
      = ez .fst .map (equiv_inverse_map X X (ey .fst) y)
        by refl ((w ↦ ez .fst .map (equiv_inverse_map X X (ey .fst) w)) : X → X)
          (inverse X y (ey .fst .map x) (h y .center .snd)) ∎)

def normal_bicycle_from_point (B : Bicycles) (x : bicycle_carrier B)
  (h : BookIsEquiv (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x)) : IsNormalBicycle B
  ≔ y ↦ embedding_surjection_equiv native_truncation (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B y)
      (bicycle_evaluation_injective B B y)
      (z ↦ native_truncation .include (BookFiber (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B y) z)
        (bicycle_symmetry_between B x h y z)) .equiv

{` More generally: if every z is reached from x by a symmetry, B is normal. `}
def normal_bicycle_from_point_surjective (B : Bicycles) (x : bicycle_carrier B)
  (s : (z : bicycle_carrier B) → Mere (BookFiber (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x) z))
  : IsNormalBicycle B
  ≔ normal_bicycle_from_point B x
      (embedding_surjection_equiv native_truncation (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x)
        (bicycle_evaluation_injective B B x) s .equiv)

{` group.tex 2115–2117: for a normal bicycle there is a unique symmetry,
   i.e. permutation of X commuting with a and b, mapping x to x'. `}
def normal_bicycle_unique_symmetry (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B)
  : BookIsContr (Σ (BicycleIsomorphisms B B) (e ↦ Id (bicycle_carrier B) x' (e .fst .map x)))
  ≔ book_contractibility_equiv (BookFiber (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation B x) x')
      (Σ (BicycleIsomorphisms B B) (e ↦ Id (bicycle_carrier B) x' (e .fst .map x)))
      (bicycle_sigma_reindex_equiv (Id Bicycles B B) (BicycleIsomorphisms B B) (bicycle_paths_equiv B B)
        (e ↦ Id (bicycle_carrier B) x' (e .fst .map x)))
      .map (h x x')

{` def:cbid-bicycle: the symmetry sending x to x'. `}
def bicycle_cbid (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B) : Id Bicycles B B
  ≔ h x x' .center .fst

def bicycle_cbid_sends (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B)
  : Id (bicycle_carrier B) x' (bicycle_path_evaluate B B (bicycle_cbid B h x x') x)
  ≔ h x x' .center .snd

{` Uniqueness: any symmetry sending x to x' is cbid x x'. `}
def bicycle_cbid_unique (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B) (p : Id Bicycles B B)
  (q : Id (bicycle_carrier B) (bicycle_path_evaluate B B p x) x') : Id (Id Bicycles B B) p (bicycle_cbid B h x x')
  ≔ bicycle_evaluation_path_reflecting B B x p (bicycle_cbid B h x x')
      (concat (bicycle_carrier B) (bicycle_path_evaluate B B p x) x' (bicycle_path_evaluate B B (bicycle_cbid B h x x') x)
        q (bicycle_cbid_sends B h x x'))

{` Claims after def:cbid-bicycle: cbid x x = id, cbid x' x'' ∘ cbid x x' =
   cbid x x'' (the composite g ∘ f of symmetries is concat f g), and the
   inverse of ev_x maps x' to cbid x x'. `}
def bicycle_cbid_self (B : Bicycles) (h : IsNormalBicycle B) (x : bicycle_carrier B)
  : Id (Id Bicycles B B) (bicycle_cbid B h x x) (refl B)
  ≔ inverse (Id Bicycles B B) (refl B) (bicycle_cbid B h x x)
      (bicycle_cbid_unique B h x x (refl B) (bicycle_path_evaluate_refl B x))

def bicycle_cbid_compose (B : Bicycles) (h : IsNormalBicycle B) (x x' x'' : bicycle_carrier B)
  : Id (Id Bicycles B B) (concat Bicycles B B B (bicycle_cbid B h x x') (bicycle_cbid B h x' x''))
      (bicycle_cbid B h x x'')
  ≔ bicycle_cbid_unique B h x x'' (concat Bicycles B B B (bicycle_cbid B h x x') (bicycle_cbid B h x' x''))
      (calc
        bicycle_path_evaluate B B (concat Bicycles B B B (bicycle_cbid B h x x') (bicycle_cbid B h x' x'')) x
        = bicycle_path_evaluate B B (bicycle_cbid B h x' x'') (bicycle_path_evaluate B B (bicycle_cbid B h x x') x)
          by bicycle_path_evaluate_concat B B B (bicycle_cbid B h x x') (bicycle_cbid B h x' x'') x
        = bicycle_path_evaluate B B (bicycle_cbid B h x' x'') x'
          by refl (bicycle_path_evaluate B B (bicycle_cbid B h x' x''))
            (inverse (bicycle_carrier B) x' (bicycle_path_evaluate B B (bicycle_cbid B h x x') x) (bicycle_cbid_sends B h x x'))
        = x'' by inverse (bicycle_carrier B) x'' (bicycle_path_evaluate B B (bicycle_cbid B h x' x'') x')
            (bicycle_cbid_sends B h x' x'') ∎)

def bicycle_cbid_inverse_evaluation (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B)
  : Id (Id Bicycles B B)
      (equiv_inverse_map (Id Bicycles B B) (bicycle_carrier B)
        (native_equivalence (Id Bicycles B B) (bicycle_carrier B) (bicycle_evaluation_equiv B h x)) x')
      (bicycle_cbid B h x x')
  ≔ refl (bicycle_cbid B h x x')

{` The symmetry inverse to cbid x x' is cbid x' x. `}
def bicycle_cbid_inverse (B : Bicycles) (h : IsNormalBicycle B) (x x' : bicycle_carrier B)
  : Id (Id Bicycles B B) (inverse Bicycles B B (bicycle_cbid B h x x')) (bicycle_cbid B h x' x)
  ≔ bicycle_cbid_unique B h x' x (inverse Bicycles B B (bicycle_cbid B h x x'))
      (calc
        bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_cbid B h x x')) x'
        = bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_cbid B h x x'))
            (bicycle_path_evaluate B B (bicycle_cbid B h x x') x)
          by refl (bicycle_path_evaluate B B (inverse Bicycles B B (bicycle_cbid B h x x'))) (bicycle_cbid_sends B h x x')
        = x by bicycle_path_evaluate_inverse B B (bicycle_cbid B h x x') x ∎)
