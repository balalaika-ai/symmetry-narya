export "500-gsets"

{` Chapter 5, sec:gsets and sec:transitiveGsets: the action type (total
   type) of a G-set, identifications in it, transitivity (def:transitiveGset),
   lem:conistrans, identifications of G-sets and the evaluation maps of
   lem:evisinjwhentransitive and the remark after it. `}

{` def:actiontype (1). The action type X_hG ≔ Σ_{z:BG} X(z), the total type
   Tot(X) of the G-set (sec:sum-types). `}
def ActionType (G : Group) (X : GSet G) : Type ≔ Σ (BG G .carrier) (z ↦ X z .fst)

def action_type_groupoid (G : Group) (X : GSet G) : isGroupoid (ActionType G X)
  ≔ hlevel_to_groupoid (ActionType G X)
      (hlevel_sigma (suc. (suc. (suc. zero.)))
        (BG G .carrier) (z ↦ X z .fst) (groupoid_to_hlevel (BG G .carrier) (bg_groupoid G))
        (z ↦ hlevel_raise (suc. (suc. zero.)) (X z .fst) (set_to_hlevel_two (X z .fst) (X z .snd))))

{` rem:path-in-action-type. ((z, x) = (w, y)) ≃ Σ_{g : z = w} (g · x = y). `}
def ActionTypePath (G : Group) (X : GSet G) (u v : ActionType G X) : Type
  ≔ Σ (Id (BG G .carrier) (u .fst) (v .fst))
      (g ↦ Id (X (v .fst) .fst) (gset_act G X (u .fst) (v .fst) g (u .snd)) (v .snd))

def action_type_path_equiv (G : Group) (X : GSet G) (u v : ActionType G X)
  : Equiv (Id (ActionType G X) u v) (ActionTypePath G X u v)
  ≔ let B ≔ BG G .carrier in
    let F : B → Type ≔ z ↦ X z .fst in
    compose_equiv (Id (ActionType G X) u v) (SigmaPath B F u v) (ActionTypePath G X u v)
      (canonical_inverse_equiv (SigmaPath B F u v) (Id (ActionType G X) u v) (sigma_path_equiv B F u v))
      (family_equiv (Id B (u .fst) (v .fst)) (g ↦ Id F g (u .snd) (v .snd))
        (g ↦ Id (X (v .fst) .fst) (gset_act G X (u .fst) (v .fst) g (u .snd)) (v .snd))
        (g ↦ pathover_transport_equiv B F (u .fst) (v .fst) g (u .snd) (v .snd)))

{` The identification (z, x) = (w, y) given by g : z = w and g · x = y. `}
def action_type_path (G : Group) (X : GSet G) (z w : BG G .carrier) (x : X z .fst) (y : X w .fst)
  (g : Id (BG G .carrier) z w) (e : Id (X w .fst) (gset_act G X z w g x) y)
  : Id (ActionType G X) (z, x) (w, y)
  ≔ (g, pathover_of_eq (BG G .carrier) (u ↦ X u .fst) z w g x y e)

{` def:transitiveGset. istrans(X) ≔ ∃_{x:X(sh)} Π_{y:X(sh)} ∃_{g:USym G} (x = g · y). `}
def IsTransitive (G : Group) (X : GSet G) : Type
  ≔ Mere (Σ (gset_underlying G X)
      (x ↦ (y : gset_underlying G X) →
        Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) x (gset_usym_act G X g y)))))

def is_transitive_prop (G : Group) (X : GSet G) : isProp (IsTransitive G X)
  ≔ mere_isprop (Σ (gset_underlying G X)
      (x ↦ (y : gset_underlying G X) →
        Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) x (gset_usym_act G X g y)))))

{` lem:conistrans (⇒). A transitive G-set has a connected action type. `}
def transitive_point_reach (G : Group) (X : GSet G) (x0 : gset_underlying G X)
  (h : (y : gset_underlying G X) →
        Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) x0 (gset_usym_act G X g y))))
  : (z : BG G .carrier) (a : X z .fst) → Mere (Id (ActionType G X) (shape G, x0) (z, a))
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    connected_based_elim native_truncation B (bg_connected G) (shape G)
      (z ↦ (a : X z .fst) → Mere (Id T (shape G, x0) (z, a)))
      (z ↦ pi_prop (X z .fst) (a ↦ Mere (Id T (shape G, x0) (z, a))) (a ↦ mere_isprop (Id T (shape G, x0) (z, a))))
      (a ↦ mere_rec (Σ (USym G) (g ↦ Id (gset_underlying G X) x0 (gset_usym_act G X g a)))
        (Mere (Id T (shape G, x0) (shape G, a))) (mere_isprop (Id T (shape G, x0) (shape G, a)))
        (ge ↦ mere (Id T (shape G, x0) (shape G, a))
          (inverse T (shape G, a) (shape G, x0)
            (action_type_path G X (shape G) (shape G) a x0 (ge .fst)
              (inverse (gset_underlying G X) x0 (gset_usym_act G X (ge .fst) a) (ge .snd)))))
        (h a))

def transitive_action_type_connected (G : Group) (X : GSet G) (t : IsTransitive G X)
  : Connected (ActionType G X)
  ≔ let T ≔ ActionType G X in
    mere_rec (Σ (gset_underlying G X)
        (x ↦ (y : gset_underlying G X) →
          Mere (Σ (USym G) (g ↦ Id (gset_underlying G X) x (gset_usym_act G X g y)))))
      (Connected T) (connected_isprop T)
      (xh ↦
        (mere T (shape G, xh .fst),
         u v ↦ merely_paths_compose native_truncation T (shape G, xh .fst) u v
           (transitive_point_reach G X (xh .fst) (xh .snd) (u .fst) (u .snd))
           (transitive_point_reach G X (xh .fst) (xh .snd) (v .fst) (v .snd))))
      t

{` lem:conistrans (⇐). A connected action type gives transitivity. `}
def connected_action_type_transitive (G : Group) (X : GSet G) (c : Connected (ActionType G X))
  : IsTransitive G X
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    let S ≔ gset_underlying G X in
    let Goal ≔ IsTransitive G X in
    mere_rec T Goal (is_transitive_prop G X)
      (u ↦ mere_rec (Id B (u .fst) (shape G)) Goal (is_transitive_prop G X)
        (p ↦
          let x ≔ gset_act G X (u .fst) (shape G) p (u .snd) in
          mere (Σ S (x ↦ (y : S) → Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))))
            (x, y ↦ mere_rec (Id T (shape G, y) (shape G, x))
              (Mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))))
              (mere_isprop (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y))))
              (r ↦ let ge ≔ action_type_path_equiv G X (shape G, y) (shape G, x) .map r in
                mere (Σ (USym G) (g ↦ Id S x (gset_usym_act G X g y)))
                  (ge .fst, inverse S (gset_usym_act G X (ge .fst) y) x (ge .snd)))
              (c .snd (shape G, y) (shape G, x))))
        (bg_connected G .snd (u .fst) (shape G)))
      (c .fst)

def transitive_connected_equiv (G : Group) (X : GSet G)
  : Equiv (IsTransitive G X) (Connected (ActionType G X))
  ≔ iff_equiv (IsTransitive G X) (Connected (ActionType G X))
      (is_transitive_prop G X) (connected_isprop (ActionType G X))
      (transitive_action_type_connected G X) (connected_action_type_transitive G X)

{` lem:conistrans, in the book's terms: X is transitive iff the associated
   covering fst : Tot(X) → BG has a connected domain. `}
def transitive_iff_connected_covering (G : Group) (X : GSet G)
  : Product (IsTransitive G X → Connected (ActionType G X)) (Connected (ActionType G X) → IsTransitive G X)
  ≔ (transitive_action_type_connected G X, connected_action_type_transitive G X)

{` lem:evisinjwhentransitive. ev_x : Hom_G(X, Y) → Y(z), ev_x(f) ≔ f_z(x). `}
def gset_hom_eval (G : Group) (X Y : GSet G) (z : BG G .carrier) (x : X z .fst) (f : GSetHom G X Y)
  : Y z .fst ≔ f z x

{` Maps agreeing at one point of a transitive G-set agree everywhere. `}
def gset_hom_eval_reflects (G : Group) (X Y : GSet G) (z : BG G .carrier) (x : X z .fst)
  (hX : IsTransitive G X) (f f' : GSetHom G X Y) (e : Id (Y z .fst) (f z x) (f' z x))
  : Id (GSetHom G X Y) f f'
  ≔ let T ≔ ActionType G X in
    let C : T → Type ≔ v ↦ Id (Y (v .fst) .fst) (f (v .fst) (v .snd)) (f' (v .fst) (v .snd)) in
    let c ≔ transitive_action_type_connected G X hX in
    funext (BG G .carrier) (w ↦ X w .fst → Y w .fst) f f'
      (w ↦ funext (X w .fst) (_ ↦ Y w .fst) (f w) (f' w)
        (x' ↦ mere_rec (Id T (z, x) (w, x')) (C (w, x'))
          (Y w .snd (f w x') (f' w x'))
          (r ↦ transport T C (z, x) (w, x') r e)
          (c .snd (z, x) (w, x'))))

def gset_hom_eval_injective (G : Group) (X Y : GSet G) (z : BG G .carrier) (x : X z .fst)
  (hX : IsTransitive G X) : IsEmbedding (GSetHom G X Y) (Y z .fst) (gset_hom_eval G X Y z x)
  ≔ path_reflecting_set_embedding (GSetHom G X Y) (Y z .fst) (Y z .snd) (gset_hom_eval G X Y z x)
      (gset_hom_eval_reflects G X Y z x hX)

{` Identifications of G-sets. By function extensionality, the subtype
   property of Set and univalence, (X = Y) ≃ Π_{z:BG} (X(z) ≃ Y(z)); the
   map sends e to transport along e at each z. `}
def gset_path_transport (G : Group) (X Y : GSet G) (e : Id (GSet G) X Y) (z : BG G .carrier)
  : X z .fst → Y z .fst
  ≔ transport (GSet G) (W ↦ W z .fst) X Y e

def gset_path_equiv (G : Group) (X Y : GSet G)
  : Equiv (Id (GSet G) X Y) ((z : BG G .carrier) → Equiv (X z .fst) (Y z .fst))
  ≔ let B ≔ BG G .carrier in
    compose_equiv (Id (GSet G) X Y) ((z : B) → Id SetTypes (X z) (Y z))
      ((z : B) → Equiv (X z .fst) (Y z .fst))
      (function_extensionality B (_ ↦ SetTypes) X Y)
      (pi_equiv B (z ↦ Id SetTypes (X z) (Y z)) (z ↦ Equiv (X z .fst) (Y z .fst))
        (z ↦ compose_equiv (Id SetTypes (X z) (Y z)) (Id Type (X z .fst) (Y z .fst)) (Equiv (X z .fst) (Y z .fst))
          (subtype_path_equiv Type isSet isset_isprop (X z) (Y z))
          (transport_univalence_equiv (X z .fst) (Y z .fst))))

def gset_path_equiv_map (G : Group) (X Y : GSet G) (e : Id (GSet G) X Y) (z : BG G .carrier)
  (x : X z .fst)
  : Id (Y z .fst) (gset_path_equiv G X Y .map e z .map x) (gset_path_transport G X Y e z x)
  ≔ refl (gset_path_transport G X Y e z x)

{` The type of G-sets is a groupoid. `}
def gset_groupoid (G : Group) : isGroupoid (GSet G)
  ≔ X Y ↦ hlevel_two_to_set (Id (GSet G) X Y)
      (hlevel_equiv (suc. (suc. zero.)) ((z : BG G .carrier) → Equiv (X z .fst) (Y z .fst)) (Id (GSet G) X Y)
        (canonical_inverse_equiv (Id (GSet G) X Y) ((z : BG G .carrier) → Equiv (X z .fst) (Y z .fst))
          (gset_path_equiv G X Y))
        (set_to_hlevel_two ((z : BG G .carrier) → Equiv (X z .fst) (Y z .fst))
          (pi_set (BG G .carrier) (z ↦ Equiv (X z .fst) (Y z .fst))
            (z ↦ equivalences_set (X z .fst) (Y z .fst) (Y z .snd)))))

{` The identification of G-sets from a family of equivalences. `}
def gset_path_from_equivs (G : Group) (X Y : GSet G) (e : (z : BG G .carrier) → Equiv (X z .fst) (Y z .fst))
  : Id (GSet G) X Y
  ≔ equiv_inverse_map (Id (GSet G) X Y) ((z : BG G .carrier) → Equiv (X z .fst) (Y z .fst))
      (gset_path_equiv G X Y) e

{` The underlying map of G-sets of an identification X = Y. `}
def gset_path_to_hom (G : Group) (X Y : GSet G) (e : Id (GSet G) X Y) : GSetHom G X Y
  ≔ z ↦ gset_path_transport G X Y e z

{` "Via function extensionality, X = Y is a subtype of Hom_G(X, Y)":
   identifications with the same underlying map are equal. `}
def gset_path_to_hom_reflects (G : Group) (X Y : GSet G) (e e' : Id (GSet G) X Y)
  (h : Id (GSetHom G X Y) (gset_path_to_hom G X Y e) (gset_path_to_hom G X Y e'))
  : Id (Id (GSet G) X Y) e e'
  ≔ let B ≔ BG G .carrier in
    equivalence_injective (Id (GSet G) X Y) ((z : B) → Equiv (X z .fst) (Y z .fst))
      (gset_path_equiv G X Y) e e'
      (funext B (z ↦ Equiv (X z .fst) (Y z .fst)) (gset_path_equiv G X Y .map e) (gset_path_equiv G X Y .map e')
        (z ↦ equiv_path (X z .fst) (Y z .fst) (gset_path_equiv G X Y .map e z) (gset_path_equiv G X Y .map e' z)
          (refl ((k ↦ k z) : GSetHom G X Y → X z .fst → Y z .fst) h)))

def gset_path_to_hom_embedding (G : Group) (X Y : GSet G)
  : IsEmbedding (Id (GSet G) X Y) (GSetHom G X Y) (gset_path_to_hom G X Y)
  ≔ path_reflecting_set_embedding (Id (GSet G) X Y) (GSetHom G X Y) (gset_hom_set G X Y)
      (gset_path_to_hom G X Y) (gset_path_to_hom_reflects G X Y)

{` The remark after lem:evisinjwhentransitive: ev_x : (X = Y) → Y(z),
   ev_x(e) ≔ e_z(x) (transport along e at z), is an injection when X is
   transitive. `}
def gset_path_eval (G : Group) (X Y : GSet G) (z : BG G .carrier) (x : X z .fst) (e : Id (GSet G) X Y)
  : Y z .fst ≔ gset_path_transport G X Y e z x

def gset_path_eval_injective (G : Group) (X Y : GSet G) (z : BG G .carrier) (x : X z .fst)
  (hX : IsTransitive G X) : IsEmbedding (Id (GSet G) X Y) (Y z .fst) (gset_path_eval G X Y z x)
  ≔ path_reflecting_set_embedding (Id (GSet G) X Y) (Y z .fst) (Y z .snd) (gset_path_eval G X Y z x)
      (e e' h ↦ gset_path_to_hom_reflects G X Y e e'
        (gset_hom_eval_reflects G X Y z x hX (gset_path_to_hom G X Y e) (gset_path_to_hom G X Y e') h))

{` def:normal-action. A (transitive) G-set X is normal if every evaluation
   ev_x : (X = X) → X(z), ev_x(e) ≔ e_z(x), is an equivalence. Transitivity
   is a separate hypothesis wherever it is used. `}
def IsNormalGSet (G : Group) (X : GSet G) : Type
  ≔ (z : BG G .carrier) (x : X z .fst) → BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x)

def is_normal_gset_prop (G : Group) (X : GSet G) : isProp (IsNormalGSet G X)
  ≔ pi_prop (BG G .carrier) (z ↦ (x : X z .fst) → BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x))
      (z ↦ pi_prop (X z .fst) (x ↦ BookIsEquiv (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x))
        (x ↦ book_isequiv_isprop (Id (GSet G) X X) (X z .fst) (gset_path_eval G X X z x)))
