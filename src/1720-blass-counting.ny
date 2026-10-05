export "1704-sets-cover"

{` Blass's Theorem 6 (choicefin.tex:301), counting part. Decidable subsets
   of Fin n are counted with true_count (module 178): the count is at most n,
   and it equals n only if the subset is everything. Consequences: an
   injection Fin k → Fin N forces k ≤ N, and k = N makes it surjective;
   injective and surjective endomaps of finite types coincide. `}

def bsix_bool_to_nat_le (b : Bool) : Le (bool_to_nat b) (suc. zero.)
  ≔ match b [ false. ↦ star. | true. ↦ star. ]

def bsix_true_count_le (n : Nat) (D : Fin n → Bool) : Le (true_count n D) n
  ≔ match n [
  | zero. ↦ star.
  | suc. m ↦ le_add_both (true_count m (a ↦ D (inl. a))) m (bool_to_nat (D (inr. star.))) (suc. zero.)
      (bsix_true_count_le m (a ↦ D (inl. a))) (bsix_bool_to_nat_le (D (inr. star.))) ]

def bsix_count_step (m c : Nat) (hc : Le c m) (b : Bool) (h : Id Nat (add c (bool_to_nat b)) (suc. m))
  : Product (Id Nat c m) (Id Bool b true.)
  ≔ match b [
  | false. ↦ absurd (Product (Id Nat c m) (Id Bool false. true.))
      (lt_irrefl m (transport Nat (k ↦ Le k m) c (suc. m) h hc))
  | true. ↦ (refl nat_pred h, refl (true. : Bool)) ]

def bsix_count_full (n : Nat) (D : Fin n → Bool) (h : Id Nat (true_count n D) n) (i : Fin n)
  : Id Bool (D i) true.
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦
      let st ≔ bsix_count_step m (true_count m (a ↦ D (inl. a))) (bsix_true_count_le m (a ↦ D (inl. a)))
        (D (inr. star.)) h in
      match i [
      | inl. a ↦ bsix_count_full m (b ↦ D (inl. b)) (st .fst) a
      | inr. u ↦ match u [ star. ↦ st .snd ] ] ]

{` Litmus: the full subset of Fin 3 has count 3 and the empty one count 0. `}
def bsix_count_litmus_full : Id Nat (true_count (suc. (suc. (suc. zero.))) (_ ↦ true.)) (suc. (suc. (suc. zero.)))
  ≔ refl (suc. (suc. (suc. zero.)) : Nat)
def bsix_count_litmus_empty : Id Nat (true_count (suc. (suc. (suc. zero.))) (_ ↦ false.)) zero.
  ≔ refl (zero. : Nat)

{` The image of a map g : Fin k → Fin N as a boolean predicate. `}
def bsix_image_decidable (k N : Nat) (g : Fin k → Fin N) (i : Fin N)
  : Decidable (Σ (Fin k) (j ↦ Id (Fin N) i (g j)))
  ≔ fin_sigma_decidable k (j ↦ Id (Fin N) i (g j)) (j ↦ fin_decidable_equality N i (g j))

def bsix_image_bool (k N : Nat) (g : Fin k → Fin N) : Fin N → Bool
  ≔ i ↦ decision_bool (Σ (Fin k) (j ↦ Id (Fin N) i (g j))) (bsix_image_decidable k N g i)

def bsix_image_carrier_equiv (k N : Nat) (g : Fin k → Fin N) (inj : PathReflecting (Fin k) (Fin N) g)
  : Equiv (Fin k) (BoolCarrier N (bsix_image_bool k N g))
  ≔ let D ≔ bsix_image_bool k N g in
    let W : Fin N → Type ≔ i ↦ Σ (Fin k) (j ↦ Id (Fin N) i (g j)) in
    let back : BoolCarrier N D → Fin k
      ≔ u ↦ decision_bool_reflect (W (u .fst)) (bsix_image_decidable k N g (u .fst)) (u .snd) .fst in
    quasi_inverse_equiv (Fin k) (BoolCarrier N D)
      (j ↦ (g j, decision_bool_true (W (g j)) (bsix_image_decidable k N g (g j)) (j, refl (g j))))
      back
      (j ↦ let w ≔ decision_bool_reflect (W (g j)) (bsix_image_decidable k N g (g j))
          (decision_bool_true (W (g j)) (bsix_image_decidable k N g (g j)) (j, refl (g j))) in
        inj (w .fst) j (inverse (Fin N) (g j) (g (w .fst)) (w .snd)))
      (u ↦ let w ≔ decision_bool_reflect (W (u .fst)) (bsix_image_decidable k N g (u .fst)) (u .snd) in
        subtype_equal (Fin N) (i ↦ Id Bool (D i) true.) (i ↦ bool_set (D i) true.)
          (g (w .fst), decision_bool_true (W (g (w .fst))) (bsix_image_decidable k N g (g (w .fst)))
            (w .fst, refl (g (w .fst)))) u
          (inverse (Fin N) (u .fst) (g (w .fst)) (w .snd)))

def bsix_image_count (k N : Nat) (g : Fin k → Fin N) (inj : PathReflecting (Fin k) (Fin N) g)
  : Id Nat (true_count N (bsix_image_bool k N g)) k
  ≔ fin_equiv_cardinality (true_count N (bsix_image_bool k N g)) k
      (compose_equiv (Fin (true_count N (bsix_image_bool k N g))) (BoolCarrier N (bsix_image_bool k N g)) (Fin k)
        (canonical_inverse_equiv (BoolCarrier N (bsix_image_bool k N g)) (Fin (true_count N (bsix_image_bool k N g)))
          (bool_carrier_fin N (bsix_image_bool k N g)))
        (canonical_inverse_equiv (Fin k) (BoolCarrier N (bsix_image_bool k N g))
          (bsix_image_carrier_equiv k N g inj)))

{` An injection Fin k → Fin N gives k ≤ N, and is surjective when k = N. `}
def bsix_injection_le (k N : Nat) (g : Fin k → Fin N) (inj : PathReflecting (Fin k) (Fin N) g) : Le k N
  ≔ transport Nat (c ↦ Le c N) (true_count N (bsix_image_bool k N g)) k (bsix_image_count k N g inj)
      (bsix_true_count_le N (bsix_image_bool k N g))

def bsix_injection_full (N : Nat) (g : Fin N → Fin N) (inj : PathReflecting (Fin N) (Fin N) g) (i : Fin N)
  : BookFiber (Fin N) (Fin N) g i
  ≔ decision_bool_reflect (Σ (Fin N) (j ↦ Id (Fin N) i (g j))) (bsix_image_decidable N N g i)
      (bsix_count_full N (bsix_image_bool N N g) (bsix_image_count N N g inj) i)

{` Endomaps of Fin N: surjective implies injective (via a section, which is
   injective, hence surjective). `}
def bsix_fin_surjective_injective (N : Nat) (f : Fin N → Fin N) (s : Surjective (Fin N) (Fin N) f)
  : PathReflecting (Fin N) (Fin N) f
  ≔ let sec : Fin N → Fin N ≔ i ↦ fin_surjection_section N (Fin N) f (fin_decidable_equality N) s i .fst in
    let back : (i : Fin N) → Id (Fin N) i (f (sec i))
      ≔ i ↦ fin_surjection_section N (Fin N) f (fin_decidable_equality N) s i .snd in
    let secinj : PathReflecting (Fin N) (Fin N) sec
      ≔ i j e ↦ concat (Fin N) i (f (sec i)) j (back i)
          (concat (Fin N) (f (sec i)) (f (sec j)) j (map_path (Fin N) (Fin N) f (sec i) (sec j) e)
            (inverse (Fin N) j (f (sec j)) (back j))) in
    y y' e ↦
      let u ≔ bsix_injection_full N sec secinj y in
      let v ≔ bsix_injection_full N sec secinj y' in
      concat (Fin N) y (sec (u .fst)) y' (u .snd)
        (concat (Fin N) (sec (u .fst)) (sec (v .fst)) y'
          (map_path (Fin N) (Fin N) sec (u .fst) (v .fst)
            (concat (Fin N) (u .fst) (f (sec (u .fst))) (v .fst) (back (u .fst))
              (concat (Fin N) (f (sec (u .fst))) (f (sec (v .fst))) (v .fst)
                (concat (Fin N) (f (sec (u .fst))) (f y) (f (sec (v .fst)))
                  (map_path (Fin N) (Fin N) f (sec (u .fst)) y (inverse (Fin N) y (sec (u .fst)) (u .snd)))
                  (concat (Fin N) (f y) (f y') (f (sec (v .fst))) e
                    (map_path (Fin N) (Fin N) f y' (sec (v .fst)) (v .snd))))
                (inverse (Fin N) (v .fst) (f (sec (v .fst))) (back (v .fst))))))
          (inverse (Fin N) y' (sec (v .fst)) (v .snd)))

def bsix_fin_injective_surjective (N : Nat) (f : Fin N → Fin N) (inj : PathReflecting (Fin N) (Fin N) f)
  : Surjective (Fin N) (Fin N) f
  ≔ i ↦ mere (BookFiber (Fin N) (Fin N) f i) (bsix_injection_full N f inj i)

{` Transport to an arbitrary type merely identified with Fin N. `}
def BsixSurjInj (A : Type) : Type
  ≔ (f : A → A) → Surjective A A f → PathReflecting A A f
def BsixInjSurj (A : Type) : Type
  ≔ (f : A → A) → PathReflecting A A f → Surjective A A f

def bsix_surjective_injective (N : Nat) (A : Type) (hA : isSet A) (p : Mere (Id Type (Fin N) A))
  (f : A → A) (s : Surjective A A f) : PathReflecting A A f
  ≔ x y e ↦ mere_rec (Id Type (Fin N) A) (Id A x y) (hA x y)
      (q ↦ transport Type BsixSurjInj (Fin N) A q (bsix_fin_surjective_injective N) f s x y e) p

def bsix_injective_surjective (N : Nat) (A : Type) (p : Mere (Id Type (Fin N) A))
  (f : A → A) (inj : PathReflecting A A f) : Surjective A A f
  ≔ y ↦ mere_rec (Id Type (Fin N) A) (Mere (BookFiber A A f y)) (mere_isprop (BookFiber A A f y))
      (q ↦ transport Type BsixInjSurj (Fin N) A q (bsix_fin_injective_surjective N) f inj y) p

{` Decidable subsets of Fin N that are not everything have fewer than N
   elements; sizes are recorded with CardBound (the cardinality is bounded). `}
def CardBound (n : Nat) (T : Type) : Type ≔ Σ Nat (k ↦ Product (Le k n) (Mere (Id Type (Fin k) T)))

def card_bound_prop (n : Nat) (T : Type) : isProp (CardBound n T)
  ≔ u v ↦ subtype_equal Nat (k ↦ Product (Le k n) (Mere (Id Type (Fin k) T)))
      (k ↦ product_prop (Le k n) (Mere (Id Type (Fin k) T)) (le_prop k n) (mere_isprop (Id Type (Fin k) T)))
      u v
      (mere_rec (Id Type (Fin (u .fst)) T) (Id Nat (u .fst) (v .fst)) (nat_set (u .fst) (v .fst))
        (p ↦ mere_rec (Id Type (Fin (v .fst)) T) (Id Nat (u .fst) (v .fst)) (nat_set (u .fst) (v .fst))
          (q ↦ fin_path_cardinality (u .fst) (v .fst) (concat Type (Fin (u .fst)) T (Fin (v .fst)) p
            (inverse Type (Fin (v .fst)) T q))) (v .snd .snd)) (u .snd .snd))

def bsix_bool_subset_bound (n : Nat) (D : Fin (suc. n) → Bool)
  (proper : ((i : Fin (suc. n)) → Id Bool (D i) true.) → Empty)
  : CardBound n (BoolCarrier (suc. n) D)
  ≔ (true_count (suc. n) D,
      (match le_split (true_count (suc. n) D) (suc. n) (bsix_true_count_le (suc. n) D) [
       | inl. lt ↦ lt
       | inr. e ↦ absurd (Le (true_count (suc. n) D) n) (proper (bsix_count_full (suc. n) D e)) ],
       mere (Id Type (Fin (true_count (suc. n) D)) (BoolCarrier (suc. n) D))
         (ua (Fin (true_count (suc. n) D)) (BoolCarrier (suc. n) D)
           (canonical_inverse_equiv (BoolCarrier (suc. n) D) (Fin (true_count (suc. n) D))
             (bool_carrier_fin (suc. n) D)))))

{` A decidable proposition-valued predicate on Fin (n+1) that does not hold
   everywhere carves out a type with at most n elements. `}
def bsix_decidable_subset_bound (n : Nat) (Q : Fin (suc. n) → Type) (hQ : (i : Fin (suc. n)) → isProp (Q i))
  (d : (i : Fin (suc. n)) → Decidable (Q i)) (proper : ((i : Fin (suc. n)) → Q i) → Empty)
  : CardBound n (Σ (Fin (suc. n)) Q)
  ≔ let D : Fin (suc. n) → Bool ≔ i ↦ decision_bool (Q i) (d i) in
    let b ≔ bsix_bool_subset_bound n D (h ↦ proper (i ↦ decision_bool_reflect (Q i) (d i) (h i))) in
    (b .fst, (b .snd .fst,
      trunc_map native_truncation (Id Type (Fin (b .fst)) (BoolCarrier (suc. n) D))
        (Id Type (Fin (b .fst)) (Σ (Fin (suc. n)) Q))
        (p ↦ concat Type (Fin (b .fst)) (BoolCarrier (suc. n) D) (Σ (Fin (suc. n)) Q) p
          (ua (BoolCarrier (suc. n) D) (Σ (Fin (suc. n)) Q)
            (family_equiv (Fin (suc. n)) (i ↦ Id Bool (D i) true.) Q
              (i ↦ iff_equiv (Id Bool (D i) true.) (Q i) (bool_set (D i) true.) (hQ i)
                (decision_bool_reflect (Q i) (d i)) (decision_bool_true (Q i) (d i))))))
        (b .snd .snd)))
