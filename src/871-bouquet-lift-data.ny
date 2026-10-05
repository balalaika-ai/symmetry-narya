export "870-free-s-sets"

{` The nondependent universal property of a bouquet, generically
   (generalizing module 222 from the circle to S-indexed loops).

   A FreeLoopsBouquet is a type B with a point b and loops l : S → b = b
   such that every x : B is merely connected to b and the S-set of loops
   (b = b, a ↦ l_a · −) is weakly free (S-maps from it to every (Y, F) are
   equivalent to Y, for EVERY type Y).  Then for EVERY type A evaluation
   (B → A) → Σ (y : A) (S → y = y), f ↦ (f b, a ↦ ap_f(l_a)) is an
   equivalence (bouquet_universal_equiv): the lift data
   T(x) = Σ (y : A) S-maps ((b = x), l·−) → ((a = y), l'·−) are
   contractible at b by freeness, hence everywhere by connectedness. `}

def fsc_bouquet_eval (S C : Type) (b0 : C) (l0 : S → Id C b0 b0) (A : Type) (f : C → A) : BouquetData S A
  ≔ (f b0, a ↦ refl f (l0 a))

{` Left composition with the loops, on paths starting at b. `}
def loop_sset (S B : Type) (b : B) (l : S → Id B b b) (x : B) : S → Equiv (Id B b x) (Id B b x)
  ≔ a ↦ loop_concat_equiv B b x (l a)

def FreeLoopsBouquet (S : Type) : Type ≔ sig (
  carrier : Type,
  base : carrier,
  loop : S → Id carrier base base,
  merely_based : (x : carrier) → Mere (Id carrier base x),
  loops_free : SSetIsWeaklyFree S (Id carrier base base, loop_sset S carrier base loop base))

def BouquetLiftData (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A) (x : Q .carrier) : Type
  ≔ Σ A (y ↦ SSetMaps S (Id (Q .carrier) (Q .base) x) (Id A (u .fst) y)
      (loop_sset S (Q .carrier) (Q .base) (Q .loop) x) (loop_sset S A (u .fst) (u .snd) y))

def bouquet_lift_base_contractible (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A)
  : isContr (BouquetLiftData S Q A u (Q .base))
  ≔ let B ≔ Q .carrier in let b ≔ Q .base in
    hlevel_equiv zero. (Σ A (y ↦ Id A (u .fst) y)) (BouquetLiftData S Q A u b)
      (canonical_inverse_equiv (BouquetLiftData S Q A u b) (Σ A (y ↦ Id A (u .fst) y))
        (family_equiv A
          (y ↦ SSetMaps S (Id B b b) (Id A (u .fst) y) (loop_sset S B b (Q .loop) b) (loop_sset S A (u .fst) (u .snd) y))
          (y ↦ Id A (u .fst) y)
          (y ↦ Q .loops_free (Id A (u .fst) y) (loop_sset S A (u .fst) (u .snd) y))))
      (based_paths_from_contractible A (u .fst))

def bouquet_lift_contractible (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A)
  (x : Q .carrier) : BookIsContr (BouquetLiftData S Q A u x)
  ≔ let B ≔ Q .carrier in let b ≔ Q .base in
    mere_rec (Id B b x) (BookIsContr (BouquetLiftData S Q A u x)) (book_iscontr_isprop (BouquetLiftData S Q A u x))
      (p ↦ transport B (y ↦ BookIsContr (BouquetLiftData S Q A u y)) b x p
        (book_contraction (BouquetLiftData S Q A u b) (bouquet_lift_base_contractible S Q A u)))
      (Q .merely_based x)

def bouquet_extension (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A) (x : Q .carrier) : A
  ≔ bouquet_lift_contractible S Q A u x .center .fst

def bouquet_lift_path (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A) (x : Q .carrier)
  (t : Id (Q .carrier) (Q .base) x) : Id A (u .fst) (bouquet_extension S Q A u x)
  ≔ bouquet_lift_contractible S Q A u x .center .snd .fst t

def bouquet_extension_evaluation (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (f : Q .carrier → A)
  : Id (Q .carrier → A) (bouquet_extension S Q A (fsc_bouquet_eval S (Q .carrier) (Q .base) (Q .loop) A f)) f
  ≔ let B ≔ Q .carrier in let b ≔ Q .base in
    let u ≔ fsc_bouquet_eval S B b (Q .loop) A f in
    funext B (_ ↦ A) (bouquet_extension S Q A u) f (x ↦
      refl ((w ↦ w .fst) : BouquetLiftData S Q A u x → A)
        (bouquet_lift_contractible S Q A u x .contract
          (f x, ((t ↦ refl f t), (a t ↦ map_path_concat B A f b b x (Q .loop a) t)))))

def bouquet_lift_naturality (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A)
  (x x' : Q .carrier) (al : Id (Q .carrier) x x') (t : Id (Q .carrier) (Q .base) x)
  : Id (Id A (u .fst) (bouquet_extension S Q A u x'))
      (concat A (u .fst) (bouquet_extension S Q A u x) (bouquet_extension S Q A u x')
        (bouquet_lift_path S Q A u x t) (refl (bouquet_extension S Q A u) al))
      (bouquet_lift_path S Q A u x' (concat (Q .carrier) (Q .base) x x' t al))
  ≔ let B ≔ Q .carrier in let b ≔ Q .base in
    let a ≔ u .fst in let F ≔ bouquet_extension S Q A u in
    let pi ≔ bouquet_lift_path S Q A u in
    J B x (x' al ↦ Id (Id A a (F x')) (concat A a (F x) (F x') (pi x t) (refl F al)) (pi x' (concat B b x x' t al)))
      (concat (Id A a (F x)) (concat A a (F x) (F x) (pi x t) (refl (F x))) (pi x t) (pi x (concat B b x x t (refl x)))
        (concat_p1 A a (F x) (pi x t))
        (refl (pi x) (inverse (Id B b x) (concat B b x x t (refl x)) t (concat_p1 B b x t))))
      x' al

def bouquet_lift_coherence (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A) (c : S)
  : Id (Id A (u .fst) (bouquet_extension S Q A u (Q .base)))
      (concat A (u .fst) (bouquet_extension S Q A u (Q .base)) (bouquet_extension S Q A u (Q .base))
        (bouquet_lift_path S Q A u (Q .base) (refl (Q .base))) (refl (bouquet_extension S Q A u) (Q .loop c)))
      (concat A (u .fst) (u .fst) (bouquet_extension S Q A u (Q .base)) (u .snd c)
        (bouquet_lift_path S Q A u (Q .base) (refl (Q .base))))
  ≔ let B ≔ Q .carrier in let b ≔ Q .base in
    let pi ≔ bouquet_lift_path S Q A u b in
    let E ≔ bouquet_extension S Q A u in
    calc
      concat A (u .fst) (E b) (E b) (pi (refl b)) (refl E (Q .loop c))
      = pi (concat B b b b (refl b) (Q .loop c)) by bouquet_lift_naturality S Q A u b b (Q .loop c) (refl b)
      = pi (Q .loop c) by refl pi (concat_1p B b b (Q .loop c))
      = pi (concat B b b b (Q .loop c) (refl b))
        by refl pi (inverse (Id B b b) (concat B b b b (Q .loop c) (refl b)) (Q .loop c) (concat_p1 B b b (Q .loop c)))
      = concat A (u .fst) (u .fst) (E b) (u .snd c) (pi (refl b))
        by bouquet_lift_contractible S Q A u b .center .snd .snd c (refl b) ∎

{` A path (y, L) = (a, l) in bouquet data from P : a = y with P·L_c = l_c·P
   (written concat P (L c) = concat (l c) P) for every c : S. `}
def bouquet_path_from_coherence (S A : Type) (u : BouquetData S A) (y : A) (P : Id A (u .fst) y)
  (L : S → Id A y y)
  (coh : (c : S) → Id (Id A (u .fst) y) (concat A (u .fst) y y P (L c)) (concat A (u .fst) (u .fst) y (u .snd c) P))
  : Id (BouquetData S A) (y, L) u
  ≔ let a ≔ u .fst in
    J A a
      (y P ↦ (L : S → Id A y y)
        → ((c : S) → Id (Id A a y) (concat A a y y P (L c)) (concat A a a y (u .snd c) P))
        → Id (BouquetData S A) (y, L) u)
      (L coh ↦ (refl a, funext S (_ ↦ Id A a a) L (u .snd) (c ↦ calc
        L c = concat A a a a (refl a) (L c) by inverse (Id A a a) (concat A a a a (refl a) (L c)) (L c) (concat_1p A a a (L c))
        = concat A a a a (u .snd c) (refl a) by coh c
        = u .snd c by concat_p1 A a a (u .snd c) ∎)))
      y P L coh

def bouquet_evaluation_extension (S : Type) (Q : FreeLoopsBouquet S) (A : Type) (u : BouquetData S A)
  : Id (BouquetData S A) (fsc_bouquet_eval S (Q .carrier) (Q .base) (Q .loop) A (bouquet_extension S Q A u)) u
  ≔ bouquet_path_from_coherence S A u (bouquet_extension S Q A u (Q .base))
      (bouquet_lift_path S Q A u (Q .base) (refl (Q .base)))
      (c ↦ refl (bouquet_extension S Q A u) (Q .loop c))
      (bouquet_lift_coherence S Q A u)

{` For EVERY type A: (B → A) ≃ Σ (y : A) (S → y = y), by evaluation. `}
def bouquet_universal_equiv (S : Type) (Q : FreeLoopsBouquet S) (A : Type)
  : Equiv (Q .carrier → A) (BouquetData S A)
  ≔ quasi_inverse_equiv (Q .carrier → A) (BouquetData S A)
      (fsc_bouquet_eval S (Q .carrier) (Q .base) (Q .loop) A) (bouquet_extension S Q A)
      (bouquet_extension_evaluation S Q A) (bouquet_evaluation_extension S Q A)
