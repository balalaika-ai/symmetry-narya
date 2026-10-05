export "1702-diaconescu"

{` "‖X → BG‖₀ is contractible for any group G", with chapter 4's Group
   (module 400: a wrapped pointed connected groupoid BG). The ∞-group
   version quantifies over pointed connected types (BG, sh) (def:inftygps),
   unfolded here. `}
def GroupTorsorsTrivial (X : Type) : Type ≔ (G : Group) → BookIsContr (SetTrunc (X → BG G .carrier))

def InfinityGroupTorsorsTrivial (X : Type) : Type
  ≔ (BG : Type) (sh : BG) → Connected BG → BookIsContr (SetTrunc (X → BG))

def group_torsors_trivial_prop (X : Type) : isProp (GroupTorsorsTrivial X)
  ≔ pi_prop Group (G ↦ BookIsContr (SetTrunc (X → BG G .carrier)))
      (G ↦ book_iscontr_isprop (SetTrunc (X → BG G .carrier)))

def infinity_group_torsors_restrict (X : Type) (h : InfinityGroupTorsorsTrivial X) : GroupTorsorsTrivial X
  ≔ G ↦ h (BG G .carrier) (shape G) (bg_connected G)

{` A map f : X → BG that is merely pointwise identified with the constant
   map has the same class in ‖X → BG‖₀. `}
def set_trunc_constant_path (X BG : Type) (sh : BG) (f : X → BG)
  (h : Mere ((x : X) → Id BG sh (f x)))
  : Id (SetTrunc (X → BG)) (set_trunc (X → BG) (_ ↦ sh)) (set_trunc (X → BG) f)
  ≔ equiv_inverse_map (Id (SetTrunc (X → BG)) (set_trunc (X → BG) (_ ↦ sh)) (set_trunc (X → BG) f))
      (Mere (Id (X → BG) (_ ↦ sh) f))
      (set_trunc_paths (X → BG) (_ ↦ sh) f)
      (trunc_map native_truncation ((x : X) → Id BG sh (f x)) (Id (X → BG) (_ ↦ sh) f)
        (funext X (_ ↦ BG) (_ ↦ sh) f) h)

def set_trunc_constant_contractible (X BG : Type) (sh : BG)
  (h : (f : X → BG) → Mere ((x : X) → Id BG sh (f x))) : BookIsContr (SetTrunc (X → BG))
  ≔ (set_trunc (X → BG) (_ ↦ sh),
      set_trunc_induction (X → BG) (z ↦ Id (SetTrunc (X → BG)) (set_trunc (X → BG) (_ ↦ sh)) z)
        (z ↦ prop_is_set (Id (SetTrunc (X → BG)) (set_trunc (X → BG) (_ ↦ sh)) z)
          (set_trunc_set (X → BG) (set_trunc (X → BG) (_ ↦ sh)) z))
        (f ↦ set_trunc_constant_path X BG sh f (h f)))

{` lem:ac-impl-triv-coh-sets: X-AC for a set X makes ‖X → BG‖₀ contractible
   for every group G, using the family of sets P(x) = (sh = f(x)). `}
def local_choice_torsors_trivial (X : Type) (hX : isSet X) (ac : LocalChoice X) : GroupTorsorsTrivial X
  ≔ G ↦ set_trunc_constant_contractible X (BG G .carrier) (shape G)
      (f ↦ ac (x ↦ (Id (BG G .carrier) (shape G) (f x), bg_groupoid G (shape G) (f x)))
        (x ↦ bg_connected G .snd (shape G) (f x)))

{` xca after "We now come to the analogue": the untruncated X-AC_∞ for a set X
   makes ‖X → BG‖₀ contractible for every ∞-group G. `}
def untruncated_local_choice_torsors_trivial (X : Type) (hX : isSet X) (ac : UntruncatedLocalChoice X)
  : InfinityGroupTorsorsTrivial X
  ≔ BG sh c ↦ set_trunc_constant_contractible X BG sh
      (f ↦ ac (x ↦ Id BG sh (f x)) (x ↦ c .snd sh (f x)))

{` From contractibility of ‖X → BG‖₀ back to a mere pointwise identification
   with the constant map. `}
def contractible_set_trunc_constant (X BG : Type) (sh : BG) (h : BookIsContr (SetTrunc (X → BG))) (f : X → BG)
  : Mere ((x : X) → Id BG sh (f x))
  ≔ trunc_map native_truncation (Id (X → BG) (_ ↦ sh) f) ((x : X) → Id BG sh (f x))
      (happly X (_ ↦ BG) (_ ↦ sh) f)
      (set_trunc_paths (X → BG) (_ ↦ sh) f .map
        (concat (SetTrunc (X → BG)) (set_trunc (X → BG) (_ ↦ sh)) (h .center) (set_trunc (X → BG) f)
          (inverse (SetTrunc (X → BG)) (h .center) (set_trunc (X → BG) (_ ↦ sh)) (h .contract (set_trunc (X → BG) (_ ↦ sh))))
          (h .contract (set_trunc (X → BG) f))))

{` BAut(S): the component of S in Set, pointed at S (component_point of
   module 400); Aut(S) = automorphism_group SetTypes sets_groupoid S. `}
def set_component_transport (S : SetTypes) (T : NativeComponent SetTypes S)
  (p : Id (NativeComponent SetTypes S) (component_point SetTypes S) T) (s : S .fst) : T .fst .fst
  ≔ transport (NativeComponent SetTypes S) (U ↦ U .fst .fst) (component_point SetTypes S) T p s

{` thm:Blass-1 with the family given as h : X → BAut(S) for a non-empty set S
   (the proof's reading of "factors through a connected component of Set");
   the family is P = pr1 ∘ h. Only the group Aut(S) is used. `}
def blass_component_sections (X : Type) (hX : isSet X) (H : GroupTorsorsTrivial X)
  (S : SetTypes) (ne : Mere (S .fst)) (h : X → NativeComponent SetTypes S)
  : Mere ((x : X) → h x .fst .fst)
  ≔ let BG ≔ NativeComponent SetTypes S in
    let sh ≔ component_point SetTypes S in
    mere_rec ((x : X) → Id BG sh (h x)) (Mere ((x : X) → h x .fst .fst))
      (mere_isprop ((x : X) → h x .fst .fst))
      (e ↦ trunc_map native_truncation (S .fst) ((x : X) → h x .fst .fst)
        (s x ↦ set_component_transport S (h x) (e x) s) ne)
      (contractible_set_trunc_constant X BG sh
        (H (automorphism_group SetTypes sets_groupoid S)) h)

def FactorsThroughNonemptyComponent (X : Type) (P : X → SetTypes) : Type
  ≔ Σ SetTypes (S ↦ Product (Mere (S .fst))
      (Σ (X → NativeComponent SetTypes S) (h ↦ Id (X → SetTypes) (x ↦ h x .fst) P)))

{` thm:Blass-1 for a family P : X → Set of sets: if P merely factors through
   the component BAut(S) of a non-empty set S, it merely has a section. `}
def blass_one (X : Type) (hX : isSet X) (H : GroupTorsorsTrivial X) (P : X → SetTypes)
  (ne : (x : X) → Mere (P x .fst)) (fac : Mere (FactorsThroughNonemptyComponent X P))
  : Mere ((x : X) → P x .fst)
  ≔ mere_rec (FactorsThroughNonemptyComponent X P) (Mere ((x : X) → P x .fst)) (mere_isprop ((x : X) → P x .fst))
      (w ↦ transport (X → SetTypes) (Q ↦ Mere ((x : X) → Q x .fst)) (x ↦ w .snd .snd .fst x .fst) P (w .snd .snd .snd)
        (blass_component_sections X hX H (w .fst) (w .snd .fst) (w .snd .snd .fst)))
      fac

{` If X is merely inhabited, non-emptiness of S in the factorization follows
   from non-emptiness of the P(x). `}
def blass_one_inhabited (X : Type) (hX : isSet X) (H : GroupTorsorsTrivial X) (P : X → SetTypes)
  (ne : (x : X) → Mere (P x .fst)) (inh : Mere X)
  (fac : Mere (Σ SetTypes (S ↦ Σ (X → NativeComponent SetTypes S) (h ↦ Id (X → SetTypes) (x ↦ h x .fst) P))))
  : Mere ((x : X) → P x .fst)
  ≔ blass_one X hX H P ne
      (mere_rec (Σ SetTypes (S ↦ Σ (X → NativeComponent SetTypes S) (h ↦ Id (X → SetTypes) (x ↦ h x .fst) P)))
        (Mere (FactorsThroughNonemptyComponent X P)) (mere_isprop (FactorsThroughNonemptyComponent X P))
        (w ↦ mere_rec X (Mere (FactorsThroughNonemptyComponent X P)) (mere_isprop (FactorsThroughNonemptyComponent X P))
          (x ↦ mere_rec (Id SetTypes (w .fst) (w .snd .fst x .fst)) (Mere (FactorsThroughNonemptyComponent X P))
            (mere_isprop (FactorsThroughNonemptyComponent X P))
            (p ↦ mere (FactorsThroughNonemptyComponent X P)
              (w .fst, (trunc_map native_truncation (P x .fst) (w .fst .fst)
                  (u ↦ transport Type (T ↦ T) (P x .fst) (w .fst .fst)
                    (inverse Type (w .fst .fst) (P x .fst)
                      (concat Type (w .fst .fst) (w .snd .fst x .fst .fst) (P x .fst)
                        (map_path SetTypes Type (T ↦ T .fst) (w .fst) (w .snd .fst x .fst) p)
                        (map_path SetTypes Type (T ↦ T .fst) (w .snd .fst x .fst) (P x)
                          (w .snd .snd (refl x))))) u) (ne x),
                w .snd)))
            (w .snd .fst x .snd)) inh)
        fac)

{` Text after thm:Blass-1: the same argument for ∞-groups and families of
   types that are all merely equivalent to a non-empty type S. `}
def blass_component_sections_infinity (X : Type) (H : InfinityGroupTorsorsTrivial X)
  (S : Type) (ne : Mere S) (h : X → NativeComponent Type S) : Mere ((x : X) → h x .fst)
  ≔ mere_rec ((x : X) → Id (NativeComponent Type S) (S, mere (Id Type S S) (refl S)) (h x))
      (Mere ((x : X) → h x .fst)) (mere_isprop ((x : X) → h x .fst))
      (e ↦ trunc_map native_truncation S ((x : X) → h x .fst)
        (s x ↦ transport (NativeComponent Type S) (U ↦ U .fst) (S, mere (Id Type S S) (refl S)) (h x) (e x) s) ne)
      (contractible_set_trunc_constant X (NativeComponent Type S) (S, mere (Id Type S S) (refl S))
        (H (NativeComponent Type S) (S, mere (Id Type S S) (refl S)) (native_component_connected Type S)) h)

{` Litmus: a finite set (here Bool) has trivial G-torsors for every group. `}
def bool_torsors_trivial : GroupTorsorsTrivial Bool
  ≔ local_choice_torsors_trivial Bool bool_set bool_local_choice
