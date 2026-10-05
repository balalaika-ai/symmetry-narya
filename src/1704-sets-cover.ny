export "1703-choice-and-torsors"

{` xca after pri:sc: AC_∞ is equivalent to AC together with SC.
   AC_∞ ⇒ SC: choose a preimage under A → ‖A‖₀ for every component; the
   chosen map ‖A‖₀ → A is surjective because |a|₀ = |a'|₀ gives ‖a = a'‖. `}
def set_trunc_section_surjective (A : Type)
  (sec : (z : SetTrunc A) → BookFiber A (SetTrunc A) (set_trunc A) z)
  : Surjective (SetTrunc A) A (z ↦ sec z .fst)
  ≔ a ↦ trunc_map native_truncation (Id A a (sec (set_trunc A a) .fst))
      (BookFiber (SetTrunc A) A (z ↦ sec z .fst) a)
      (q ↦ (set_trunc A a, q))
      (set_trunc_paths A a (sec (set_trunc A a) .fst) .map (sec (set_trunc A a) .snd))

def untruncated_choice_sets_cover (ac : UntruncatedChoice) : SetsCover
  ≔ A ↦ trunc_map native_truncation ((z : SetTrunc A) → BookFiber A (SetTrunc A) (set_trunc A) z) (SetCovers A)
      (sec ↦ ((SetTrunc A, set_trunc_set A), ((z ↦ sec z .fst), set_trunc_section_surjective A sec)))
      (ac (SetTrunc A, set_trunc_set A) (z ↦ BookFiber A (SetTrunc A) (set_trunc A) z) (set_trunc_surjective A))

{` AC ∧ SC ⇒ AC_∞: cover Σ_x P(x) by a set Y, choose for every x a y : Y
   over x with AC (a family of sets), and transport the second component. `}
def CoverOver (X : Type) (P : X → Type) (Y : SetTypes) (g : Y .fst → Σ X P) (x : X) : Type
  ≔ Σ (Y .fst) (y ↦ Id X x (g y .fst))

def cover_over_set (X : SetTypes) (P : X .fst → Type) (Y : SetTypes) (g : Y .fst → Σ (X .fst) P) (x : X .fst)
  : isSet (CoverOver (X .fst) P Y g x)
  ≔ sigma_set (Y .fst) (y ↦ Id (X .fst) x (g y .fst)) (Y .snd)
      (y ↦ prop_is_set (Id (X .fst) x (g y .fst)) (X .snd x (g y .fst)))

def cover_over_inhabited (X : Type) (P : X → Type) (Y : SetTypes) (g : Y .fst → Σ X P)
  (gs : Surjective (Y .fst) (Σ X P) g) (h : (x : X) → Mere (P x)) (x : X) : Mere (CoverOver X P Y g x)
  ≔ mere_rec (P x) (Mere (CoverOver X P Y g x)) (mere_isprop (CoverOver X P Y g x))
      (u ↦ trunc_map native_truncation (BookFiber (Y .fst) (Σ X P) g (x, u)) (CoverOver X P Y g x)
        (w ↦ (w .fst, map_path (Σ X P) X (t ↦ t .fst) (x, u) (g (w .fst)) (w .snd))) (gs (x, u)))
      (h x)

def cover_over_point (X : Type) (P : X → Type) (Y : SetTypes) (g : Y .fst → Σ X P) (x : X)
  (c : CoverOver X P Y g x) : P x
  ≔ transport X P (g (c .fst) .fst) x (inverse X x (g (c .fst) .fst) (c .snd)) (g (c .fst) .snd)

def choice_and_cover_untruncated (ac : AxiomOfChoice) (sc : SetsCover) : UntruncatedChoice
  ≔ X P h ↦ mere_rec (SetCovers (Σ (X .fst) P)) (Mere ((x : X .fst) → P x)) (mere_isprop ((x : X .fst) → P x))
      (cov ↦ trunc_map native_truncation ((x : X .fst) → CoverOver (X .fst) P (cov .fst) (cov .snd .fst) x)
        ((x : X .fst) → P x)
        (t x ↦ cover_over_point (X .fst) P (cov .fst) (cov .snd .fst) x (t x))
        (ac X (x ↦ (CoverOver (X .fst) P (cov .fst) (cov .snd .fst) x,
                    cover_over_set X P (cov .fst) (cov .snd .fst) x))
          (cover_over_inhabited (X .fst) P (cov .fst) (cov .snd .fst) (cov .snd .snd) h)))
      (sc (Σ (X .fst) P))

def untruncated_choice_iff : Equiv UntruncatedChoice (Product AxiomOfChoice SetsCover)
  ≔ iff_equiv UntruncatedChoice (Product AxiomOfChoice SetsCover) untruncated_choice_prop
      (product_prop AxiomOfChoice SetsCover axiom_of_choice_prop sets_cover_prop)
      (ac ↦ (untruncated_choice_restrict ac, untruncated_choice_sets_cover ac))
      (h ↦ choice_and_cover_untruncated (h .fst) (h .snd))

{` Litmus: every set is covered by itself (identity map). `}
def set_covers_itself (A : SetTypes) : SetCovers (A .fst)
  ≔ (A, ((a ↦ a), a ↦ mere (BookFiber (A .fst) (A .fst) (a ↦ a) a) (a, refl a)))
