export "1710-quartet-basics"

{` thm:lAC-2-3-4. A 2+2 partition of a 4-element set A is encoded by the
   fixed-point-free involution exchanging the two elements of each part
   (the partition {{a,b},{c,d}} is the involution (a b)(c d)). The parts of
   a partition σ are the σ-invariant boolean subsets B : A → Bool that are not
   constant, and the elements of a part B are Σ_{a:A} (B a = true). `}
def QuartetInvolution (A : Type) (σ : A → A) : Type
  ≔ Product ((a : A) → Id A (σ (σ a)) a) ((a : A) → Not (Id A (σ a) a))

def QuartetPartitions (A : Type) : Type ≔ Σ (A → A) (σ ↦ QuartetInvolution A σ)

def quartet_involution_prop (A : Type) (sA : isSet A) (σ : A → A) : isProp (QuartetInvolution A σ)
  ≔ product_prop ((a : A) → Id A (σ (σ a)) a) ((a : A) → Not (Id A (σ a) a))
      (pi_prop A (a ↦ Id A (σ (σ a)) a) (a ↦ sA (σ (σ a)) a))
      (pi_prop A (a ↦ Not (Id A (σ a) a)) (a ↦ negation_prop (Id A (σ a) a)))

def quartet_partitions_set (A : Type) (sA : isSet A) : isSet (QuartetPartitions A)
  ≔ sigma_set (A → A) (σ ↦ QuartetInvolution A σ) (pi_set A (_ ↦ A) (_ ↦ sA))
      (σ ↦ prop_is_set (QuartetInvolution A σ) (quartet_involution_prop A sA σ))

def QuartetBlockCondition (A : Type) (σ : A → A) (B : A → Bool) : Type
  ≔ Product ((a : A) → Id Bool (B (σ a)) (B a)) (Not ((a a' : A) → Id Bool (B a) (B a')))

def QuartetBlocks (A : Type) (σ : A → A) : Type ≔ Σ (A → Bool) (B ↦ QuartetBlockCondition A σ B)

def QuartetBlockPoints (A : Type) (B : A → Bool) : Type ≔ Σ A (a ↦ Id Bool (B a) true.)

def quartet_block_condition_prop (A : Type) (σ : A → A) (B : A → Bool) : isProp (QuartetBlockCondition A σ B)
  ≔ product_prop ((a : A) → Id Bool (B (σ a)) (B a)) (Not ((a a' : A) → Id Bool (B a) (B a')))
      (pi_prop A (a ↦ Id Bool (B (σ a)) (B a)) (a ↦ bool_set (B (σ a)) (B a)))
      (negation_prop ((a a' : A) → Id Bool (B a) (B a')))

{` The involution identities used below. `}
def quartet_partner (A : Type) (σ : A → A) (inv : (a : A) → Id A (σ (σ a)) a) (a b : A) (e : Id A (σ a) b)
  : Id A a (σ b)
  ≔ concat A a (σ (σ a)) (σ b) (inverse A (σ (σ a)) a (inv a)) (map_path A A σ (σ a) b e)

{` The three partitions of Fin 4: (0 1)(2 3), (0 2)(1 3), (0 3)(1 2). `}
def quartet_swap1 : Fin quartet_four → Fin quartet_four
  ≔ quartet_cases (_ ↦ Fin quartet_four) quartet_e1 quartet_e0 quartet_e3 quartet_e2
def quartet_swap2 : Fin quartet_four → Fin quartet_four
  ≔ quartet_cases (_ ↦ Fin quartet_four) quartet_e2 quartet_e3 quartet_e0 quartet_e1
def quartet_swap3 : Fin quartet_four → Fin quartet_four
  ≔ quartet_cases (_ ↦ Fin quartet_four) quartet_e3 quartet_e2 quartet_e1 quartet_e0

def quartet_swap1_involution : QuartetInvolution (Fin quartet_four) quartet_swap1
  ≔ (quartet_cases (a ↦ Id (Fin quartet_four) (quartet_swap1 (quartet_swap1 a)) a)
        (refl quartet_e0) (refl quartet_e1) (refl quartet_e2) (refl quartet_e3),
      quartet_cases (a ↦ Not (Id (Fin quartet_four) (quartet_swap1 a) a))
        (quartet_ne quartet_e1 quartet_e0 (refl (false. : Bool))) (quartet_ne quartet_e0 quartet_e1 (refl (false. : Bool)))
        (quartet_ne quartet_e3 quartet_e2 (refl (false. : Bool))) (quartet_ne quartet_e2 quartet_e3 (refl (false. : Bool))))

def quartet_swap2_involution : QuartetInvolution (Fin quartet_four) quartet_swap2
  ≔ (quartet_cases (a ↦ Id (Fin quartet_four) (quartet_swap2 (quartet_swap2 a)) a)
        (refl quartet_e0) (refl quartet_e1) (refl quartet_e2) (refl quartet_e3),
      quartet_cases (a ↦ Not (Id (Fin quartet_four) (quartet_swap2 a) a))
        (quartet_ne quartet_e2 quartet_e0 (refl (false. : Bool))) (quartet_ne quartet_e3 quartet_e1 (refl (false. : Bool)))
        (quartet_ne quartet_e0 quartet_e2 (refl (false. : Bool))) (quartet_ne quartet_e1 quartet_e3 (refl (false. : Bool))))

def quartet_swap3_involution : QuartetInvolution (Fin quartet_four) quartet_swap3
  ≔ (quartet_cases (a ↦ Id (Fin quartet_four) (quartet_swap3 (quartet_swap3 a)) a)
        (refl quartet_e0) (refl quartet_e1) (refl quartet_e2) (refl quartet_e3),
      quartet_cases (a ↦ Not (Id (Fin quartet_four) (quartet_swap3 a) a))
        (quartet_ne quartet_e3 quartet_e0 (refl (false. : Bool))) (quartet_ne quartet_e2 quartet_e1 (refl (false. : Bool)))
        (quartet_ne quartet_e1 quartet_e2 (refl (false. : Bool))) (quartet_ne quartet_e0 quartet_e3 (refl (false. : Bool))))

def quartet_partition1 : QuartetPartitions (Fin quartet_four) ≔ (quartet_swap1, quartet_swap1_involution)
def quartet_partition2 : QuartetPartitions (Fin quartet_four) ≔ (quartet_swap2, quartet_swap2_involution)
def quartet_partition3 : QuartetPartitions (Fin quartet_four) ≔ (quartet_swap3, quartet_swap3_involution)

def quartet_partition_of_index : Fin quartet_three → QuartetPartitions (Fin quartet_four)
  ≔ quartet_trio_cases (_ ↦ QuartetPartitions (Fin quartet_four))
      quartet_partition1 quartet_partition2 quartet_partition3

{` A partition of Fin 4 is classified by the partner of 0. `}
def quartet_partition_index_at (y : Fin quartet_four) : Not (Id (Fin quartet_four) y quartet_e0) → Fin quartet_three
  ≔ quartet_cases (y ↦ Not (Id (Fin quartet_four) y quartet_e0) → Fin quartet_three)
      (n ↦ absurd (Fin quartet_three) (n (refl quartet_e0)))
      (_ ↦ quartet_t0) (_ ↦ quartet_t1) (_ ↦ quartet_t2) y

def quartet_partition_index (s : QuartetPartitions (Fin quartet_four)) : Fin quartet_three
  ≔ quartet_partition_index_at (s .fst quartet_e0) (s .snd .snd quartet_e0)

def quartet_partition_index_roundtrip (t : Fin quartet_three)
  : Id (Fin quartet_three) (quartet_partition_index (quartet_partition_of_index t)) t
  ≔ quartet_trio_cases (t ↦ Id (Fin quartet_three) (quartet_partition_index (quartet_partition_of_index t)) t)
      (refl quartet_t0) (refl quartet_t1) (refl quartet_t2) t

def quartet_partition_ext (s : QuartetPartitions (Fin quartet_four)) (σ : Fin quartet_four → Fin quartet_four)
  (hσ : QuartetInvolution (Fin quartet_four) σ)
  (h : (x : Fin quartet_four) → Id (Fin quartet_four) (σ x) (s .fst x))
  : Id (QuartetPartitions (Fin quartet_four)) (σ, hσ) s
  ≔ subtype_equal (Fin quartet_four → Fin quartet_four) (QuartetInvolution (Fin quartet_four))
      (quartet_involution_prop (Fin quartet_four) (fin_set quartet_four)) (σ, hσ) s
      (funext (Fin quartet_four) (_ ↦ Fin quartet_four) σ (s .fst) h)

def quartet_partition1_eq (s : QuartetPartitions (Fin quartet_four))
  (e : Id (Fin quartet_four) (s .fst quartet_e0) quartet_e1)
  : Id (QuartetPartitions (Fin quartet_four)) quartet_partition1 s
  ≔ let F ≔ Fin quartet_four in
    let σ ≔ s .fst in
    let inv ≔ s .snd .fst in
    let p1 : Id F quartet_e0 (σ quartet_e1) ≔ quartet_partner F σ inv quartet_e0 quartet_e1 e in
    let p2 : Id F (σ quartet_e2) quartet_e3
      ≔ quartet_pin (σ quartet_e2) quartet_e3
          (quartet_cases (z ↦ Not (Id F z quartet_e3) → Not (Id F (σ quartet_e2) z))
            (_ q ↦ quartet_ne quartet_e2 quartet_e1 (refl (false. : Bool))
              (concat F quartet_e2 (σ quartet_e0) quartet_e1 (quartet_partner F σ inv quartet_e2 quartet_e0 q) e))
            (_ q ↦ quartet_ne quartet_e2 quartet_e0 (refl (false. : Bool))
              (concat F quartet_e2 (σ quartet_e1) quartet_e0 (quartet_partner F σ inv quartet_e2 quartet_e1 q)
                (inverse F quartet_e0 (σ quartet_e1) p1)))
            (_ ↦ s .snd .snd quartet_e2)
            (n ↦ absurd (Not (Id F (σ quartet_e2) quartet_e3)) (n (refl quartet_e3)))) in
    let p3 : Id F quartet_e2 (σ quartet_e3) ≔ quartet_partner F σ inv quartet_e2 quartet_e3 p2 in
    quartet_partition_ext s quartet_swap1 quartet_swap1_involution
      (quartet_cases (x ↦ Id F (quartet_swap1 x) (σ x))
        (inverse F (σ quartet_e0) quartet_e1 e) p1 (inverse F (σ quartet_e2) quartet_e3 p2) p3)

def quartet_partition2_eq (s : QuartetPartitions (Fin quartet_four))
  (e : Id (Fin quartet_four) (s .fst quartet_e0) quartet_e2)
  : Id (QuartetPartitions (Fin quartet_four)) quartet_partition2 s
  ≔ let F ≔ Fin quartet_four in
    let σ ≔ s .fst in
    let inv ≔ s .snd .fst in
    let pa : Id F quartet_e0 (σ quartet_e2) ≔ quartet_partner F σ inv quartet_e0 quartet_e2 e in
    let pb : Id F (σ quartet_e1) quartet_e3
      ≔ quartet_pin (σ quartet_e1) quartet_e3
          (quartet_cases (z ↦ Not (Id F z quartet_e3) → Not (Id F (σ quartet_e1) z))
            (_ q ↦ quartet_ne quartet_e1 quartet_e2 (refl (false. : Bool))
              (concat F quartet_e1 (σ quartet_e0) quartet_e2 (quartet_partner F σ inv quartet_e1 quartet_e0 q) e))
            (_ ↦ s .snd .snd quartet_e1)
            (_ q ↦ quartet_ne quartet_e1 quartet_e0 (refl (false. : Bool))
              (concat F quartet_e1 (σ quartet_e2) quartet_e0 (quartet_partner F σ inv quartet_e1 quartet_e2 q)
                (inverse F quartet_e0 (σ quartet_e2) pa)))
            (n ↦ absurd (Not (Id F (σ quartet_e1) quartet_e3)) (n (refl quartet_e3)))) in
    let pc : Id F quartet_e1 (σ quartet_e3) ≔ quartet_partner F σ inv quartet_e1 quartet_e3 pb in
    quartet_partition_ext s quartet_swap2 quartet_swap2_involution
      (quartet_cases (x ↦ Id F (quartet_swap2 x) (σ x))
        (inverse F (σ quartet_e0) quartet_e2 e) (inverse F (σ quartet_e1) quartet_e3 pb) pa pc)

def quartet_partition3_eq (s : QuartetPartitions (Fin quartet_four))
  (e : Id (Fin quartet_four) (s .fst quartet_e0) quartet_e3)
  : Id (QuartetPartitions (Fin quartet_four)) quartet_partition3 s
  ≔ let F ≔ Fin quartet_four in
    let σ ≔ s .fst in
    let inv ≔ s .snd .fst in
    let pa : Id F quartet_e0 (σ quartet_e3) ≔ quartet_partner F σ inv quartet_e0 quartet_e3 e in
    let pb : Id F (σ quartet_e1) quartet_e2
      ≔ quartet_pin (σ quartet_e1) quartet_e2
          (quartet_cases (z ↦ Not (Id F z quartet_e2) → Not (Id F (σ quartet_e1) z))
            (_ q ↦ quartet_ne quartet_e1 quartet_e3 (refl (false. : Bool))
              (concat F quartet_e1 (σ quartet_e0) quartet_e3 (quartet_partner F σ inv quartet_e1 quartet_e0 q) e))
            (_ ↦ s .snd .snd quartet_e1)
            (n ↦ absurd (Not (Id F (σ quartet_e1) quartet_e2)) (n (refl quartet_e2)))
            (_ q ↦ quartet_ne quartet_e1 quartet_e0 (refl (false. : Bool))
              (concat F quartet_e1 (σ quartet_e3) quartet_e0 (quartet_partner F σ inv quartet_e1 quartet_e3 q)
                (inverse F quartet_e0 (σ quartet_e3) pa)))) in
    let pc : Id F quartet_e1 (σ quartet_e2) ≔ quartet_partner F σ inv quartet_e1 quartet_e2 pb in
    quartet_partition_ext s quartet_swap3 quartet_swap3_involution
      (quartet_cases (x ↦ Id F (quartet_swap3 x) (σ x))
        (inverse F (σ quartet_e0) quartet_e3 e) (inverse F (σ quartet_e1) quartet_e2 pb) pc pa)

def quartet_partition_classify_at (s : QuartetPartitions (Fin quartet_four))
  : (y : Fin quartet_four) → Id (Fin quartet_four) (s .fst quartet_e0) y → (n : Not (Id (Fin quartet_four) y quartet_e0))
    → Id (QuartetPartitions (Fin quartet_four)) (quartet_partition_of_index (quartet_partition_index_at y n)) s
  ≔ quartet_cases (y ↦ Id (Fin quartet_four) (s .fst quartet_e0) y → (n : Not (Id (Fin quartet_four) y quartet_e0))
      → Id (QuartetPartitions (Fin quartet_four)) (quartet_partition_of_index (quartet_partition_index_at y n)) s)
      (_ n ↦ absurd (Id (QuartetPartitions (Fin quartet_four))
          (quartet_partition_of_index (quartet_partition_index_at quartet_e0 n)) s) (n (refl quartet_e0)))
      (e _ ↦ quartet_partition1_eq s e)
      (e _ ↦ quartet_partition2_eq s e)
      (e _ ↦ quartet_partition3_eq s e)

def quartet_partition_classify (s : QuartetPartitions (Fin quartet_four))
  : Id (QuartetPartitions (Fin quartet_four)) (quartet_partition_of_index (quartet_partition_index s)) s
  ≔ quartet_partition_classify_at s (s .fst quartet_e0) (refl (s .fst quartet_e0)) (s .snd .snd quartet_e0)

{` The set of 2+2 partitions of Fin 4 has exactly three elements. `}
def quartet_partitions_fin_equiv : Equiv (Fin quartet_three) (QuartetPartitions (Fin quartet_four))
  ≔ quasi_inverse_equiv (Fin quartet_three) (QuartetPartitions (Fin quartet_four))
      quartet_partition_of_index quartet_partition_index
      quartet_partition_index_roundtrip quartet_partition_classify

{` Every 4-element set has a 3-element set of 2+2 partitions. `}
def quartet_partitions_three (A : Type) (h : Mere (Id Type (Fin quartet_four) A))
  : Mere (Id Type (Fin quartet_three) (QuartetPartitions A))
  ≔ quartet_transfer (T ↦ Mere (Id Type (Fin quartet_three) (QuartetPartitions T))) A
      (mere_isprop (Id Type (Fin quartet_three) (QuartetPartitions A)))
      (mere (Id Type (Fin quartet_three) (QuartetPartitions (Fin quartet_four)))
        (ua (Fin quartet_three) (QuartetPartitions (Fin quartet_four)) quartet_partitions_fin_equiv)) h

{` The two parts of each partition of Fin 4, indexed by the value b at 0. `}
def quartet_block1 (b : Bool) : Fin quartet_four → Bool
  ≔ quartet_cases (_ ↦ Bool) b b (bool_not b) (bool_not b)
def quartet_block2 (b : Bool) : Fin quartet_four → Bool
  ≔ quartet_cases (_ ↦ Bool) b (bool_not b) b (bool_not b)
def quartet_block3 (b : Bool) : Fin quartet_four → Bool
  ≔ quartet_cases (_ ↦ Bool) b (bool_not b) (bool_not b) b

def quartet_block1_condition (b : Bool) : QuartetBlockCondition (Fin quartet_four) quartet_swap1 (quartet_block1 b)
  ≔ (quartet_cases (a ↦ Id Bool (quartet_block1 b (quartet_swap1 a)) (quartet_block1 b a))
        (refl b) (refl b) (refl (bool_not b)) (refl (bool_not b)),
      h ↦ bool_not_no_fixed_point b (h quartet_e2 quartet_e0))
def quartet_block2_condition (b : Bool) : QuartetBlockCondition (Fin quartet_four) quartet_swap2 (quartet_block2 b)
  ≔ (quartet_cases (a ↦ Id Bool (quartet_block2 b (quartet_swap2 a)) (quartet_block2 b a))
        (refl b) (refl (bool_not b)) (refl b) (refl (bool_not b)),
      h ↦ bool_not_no_fixed_point b (h quartet_e1 quartet_e0))
def quartet_block3_condition (b : Bool) : QuartetBlockCondition (Fin quartet_four) quartet_swap3 (quartet_block3 b)
  ≔ (quartet_cases (a ↦ Id Bool (quartet_block3 b (quartet_swap3 a)) (quartet_block3 b a))
        (refl b) (refl (bool_not b)) (refl (bool_not b)) (refl b),
      h ↦ bool_not_no_fixed_point b (h quartet_e1 quartet_e0))

{` A non-constant function Fin 4 → Bool cannot agree with its value at 0 everywhere. `}
def quartet_constant_contra (B : Fin quartet_four → Bool)
  (nc : Not ((a a' : Fin quartet_four) → Id Bool (B a) (B a')))
  (h1 : Id Bool (B quartet_e1) (B quartet_e0)) (h2 : Id Bool (B quartet_e2) (B quartet_e0))
  (h3 : Id Bool (B quartet_e3) (B quartet_e0)) : Empty
  ≔ let all ≔ quartet_cases (a ↦ Id Bool (B a) (B quartet_e0)) (refl (B quartet_e0)) h1 h2 h3 in
    nc (a a' ↦ concat Bool (B a) (B quartet_e0) (B a') (all a) (inverse Bool (B a') (B quartet_e0) (all a')))

def quartet_block1_rigid (B : QuartetBlocks (Fin quartet_four) quartet_swap1)
  : Id (Fin quartet_four → Bool) (quartet_block1 (B .fst quartet_e0)) (B .fst)
  ≔ let f ≔ B .fst in
    let inv ≔ B .snd .fst in
    let b1 : Id Bool (f quartet_e1) (f quartet_e0) ≔ inv quartet_e0 in
    let b32 : Id Bool (f quartet_e3) (f quartet_e2) ≔ inv quartet_e2 in
    let c2 : Id Bool (f quartet_e2) (bool_not (f quartet_e0))
      ≔ quartet_bool_other (f quartet_e2) (f quartet_e0)
          (q ↦ quartet_constant_contra f (B .snd .snd) b1 q (concat Bool (f quartet_e3) (f quartet_e2) (f quartet_e0) b32 q)) in
    funext (Fin quartet_four) (_ ↦ Bool) (quartet_block1 (f quartet_e0)) f
      (quartet_cases (x ↦ Id Bool (quartet_block1 (f quartet_e0) x) (f x))
        (refl (f quartet_e0)) (inverse Bool (f quartet_e1) (f quartet_e0) b1)
        (inverse Bool (f quartet_e2) (bool_not (f quartet_e0)) c2)
        (inverse Bool (f quartet_e3) (bool_not (f quartet_e0))
          (concat Bool (f quartet_e3) (f quartet_e2) (bool_not (f quartet_e0)) b32 c2)))

def quartet_block2_rigid (B : QuartetBlocks (Fin quartet_four) quartet_swap2)
  : Id (Fin quartet_four → Bool) (quartet_block2 (B .fst quartet_e0)) (B .fst)
  ≔ let f ≔ B .fst in
    let inv ≔ B .snd .fst in
    let b2 : Id Bool (f quartet_e2) (f quartet_e0) ≔ inv quartet_e0 in
    let b31 : Id Bool (f quartet_e3) (f quartet_e1) ≔ inv quartet_e1 in
    let c1 : Id Bool (f quartet_e1) (bool_not (f quartet_e0))
      ≔ quartet_bool_other (f quartet_e1) (f quartet_e0)
          (q ↦ quartet_constant_contra f (B .snd .snd) q b2 (concat Bool (f quartet_e3) (f quartet_e1) (f quartet_e0) b31 q)) in
    funext (Fin quartet_four) (_ ↦ Bool) (quartet_block2 (f quartet_e0)) f
      (quartet_cases (x ↦ Id Bool (quartet_block2 (f quartet_e0) x) (f x))
        (refl (f quartet_e0))
        (inverse Bool (f quartet_e1) (bool_not (f quartet_e0)) c1)
        (inverse Bool (f quartet_e2) (f quartet_e0) b2)
        (inverse Bool (f quartet_e3) (bool_not (f quartet_e0))
          (concat Bool (f quartet_e3) (f quartet_e1) (bool_not (f quartet_e0)) b31 c1)))

def quartet_block3_rigid (B : QuartetBlocks (Fin quartet_four) quartet_swap3)
  : Id (Fin quartet_four → Bool) (quartet_block3 (B .fst quartet_e0)) (B .fst)
  ≔ let f ≔ B .fst in
    let inv ≔ B .snd .fst in
    let b3 : Id Bool (f quartet_e3) (f quartet_e0) ≔ inv quartet_e0 in
    let b21 : Id Bool (f quartet_e2) (f quartet_e1) ≔ inv quartet_e1 in
    let c1 : Id Bool (f quartet_e1) (bool_not (f quartet_e0))
      ≔ quartet_bool_other (f quartet_e1) (f quartet_e0)
          (q ↦ quartet_constant_contra f (B .snd .snd) q (concat Bool (f quartet_e2) (f quartet_e1) (f quartet_e0) b21 q) b3) in
    funext (Fin quartet_four) (_ ↦ Bool) (quartet_block3 (f quartet_e0)) f
      (quartet_cases (x ↦ Id Bool (quartet_block3 (f quartet_e0) x) (f x))
        (refl (f quartet_e0))
        (inverse Bool (f quartet_e1) (bool_not (f quartet_e0)) c1)
        (inverse Bool (f quartet_e2) (bool_not (f quartet_e0))
          (concat Bool (f quartet_e2) (f quartet_e1) (bool_not (f quartet_e0)) b21 c1))
        (inverse Bool (f quartet_e3) (f quartet_e0) b3))

def quartet_blocks1_equiv : Equiv (QuartetBlocks (Fin quartet_four) quartet_swap1) Bool
  ≔ quasi_inverse_equiv (QuartetBlocks (Fin quartet_four) quartet_swap1) Bool
      (B ↦ B .fst quartet_e0) (b ↦ (quartet_block1 b, quartet_block1_condition b))
      (B ↦ subtype_equal (Fin quartet_four → Bool) (QuartetBlockCondition (Fin quartet_four) quartet_swap1)
        (quartet_block_condition_prop (Fin quartet_four) quartet_swap1)
        (quartet_block1 (B .fst quartet_e0), quartet_block1_condition (B .fst quartet_e0)) B (quartet_block1_rigid B))
      (b ↦ refl b)

def quartet_blocks2_equiv : Equiv (QuartetBlocks (Fin quartet_four) quartet_swap2) Bool
  ≔ quasi_inverse_equiv (QuartetBlocks (Fin quartet_four) quartet_swap2) Bool
      (B ↦ B .fst quartet_e0) (b ↦ (quartet_block2 b, quartet_block2_condition b))
      (B ↦ subtype_equal (Fin quartet_four → Bool) (QuartetBlockCondition (Fin quartet_four) quartet_swap2)
        (quartet_block_condition_prop (Fin quartet_four) quartet_swap2)
        (quartet_block2 (B .fst quartet_e0), quartet_block2_condition (B .fst quartet_e0)) B (quartet_block2_rigid B))
      (b ↦ refl b)

def quartet_blocks3_equiv : Equiv (QuartetBlocks (Fin quartet_four) quartet_swap3) Bool
  ≔ quasi_inverse_equiv (QuartetBlocks (Fin quartet_four) quartet_swap3) Bool
      (B ↦ B .fst quartet_e0) (b ↦ (quartet_block3 b, quartet_block3_condition b))
      (B ↦ subtype_equal (Fin quartet_four → Bool) (QuartetBlockCondition (Fin quartet_four) quartet_swap3)
        (quartet_block_condition_prop (Fin quartet_four) quartet_swap3)
        (quartet_block3 (B .fst quartet_e0), quartet_block3_condition (B .fst quartet_e0)) B (quartet_block3_rigid B))
      (b ↦ refl b)

def quartet_two_path (T : Type) (e : Equiv T Bool) : Mere (Id Type (Fin two) T)
  ≔ mere (Id Type (Fin two) T) (concat Type (Fin two) Bool T fin_two_path (inverse Type T Bool (ua T Bool e)))

def quartet_blocks_two_index
  : (t : Fin quartet_three) → Mere (Id Type (Fin two) (QuartetBlocks (Fin quartet_four) (quartet_partition_of_index t .fst)))
  ≔ quartet_trio_cases (t ↦ Mere (Id Type (Fin two) (QuartetBlocks (Fin quartet_four) (quartet_partition_of_index t .fst))))
      (quartet_two_path (QuartetBlocks (Fin quartet_four) quartet_swap1) quartet_blocks1_equiv)
      (quartet_two_path (QuartetBlocks (Fin quartet_four) quartet_swap2) quartet_blocks2_equiv)
      (quartet_two_path (QuartetBlocks (Fin quartet_four) quartet_swap3) quartet_blocks3_equiv)

def quartet_blocks_two_fin (s : QuartetPartitions (Fin quartet_four))
  : Mere (Id Type (Fin two) (QuartetBlocks (Fin quartet_four) (s .fst)))
  ≔ transport (QuartetPartitions (Fin quartet_four))
      (s' ↦ Mere (Id Type (Fin two) (QuartetBlocks (Fin quartet_four) (s' .fst))))
      (quartet_partition_of_index (quartet_partition_index s)) s (quartet_partition_classify s)
      (quartet_blocks_two_index (quartet_partition_index s))

{` Every part of a partition of Fin 4 has two elements. `}
def quartet_points_count (f : Fin quartet_four → Bool) (e : Id Nat (true_count quartet_four f) two)
  : Mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) f))
  ≔ mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) f))
      (inverse Type (QuartetBlockPoints (Fin quartet_four) f) (Fin two)
        (transport Nat (n ↦ Id Type (QuartetBlockPoints (Fin quartet_four) f) (Fin n)) (true_count quartet_four f) two e
          (ua (QuartetBlockPoints (Fin quartet_four) f) (Fin (true_count quartet_four f)) (bool_carrier_fin quartet_four f))))

def quartet_block1_points (b : Bool) : Mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) (quartet_block1 b)))
  ≔ match b [
  | false. ↦ quartet_points_count (quartet_block1 false.) (refl two)
  | true. ↦ quartet_points_count (quartet_block1 true.) (refl two) ]
def quartet_block2_points (b : Bool) : Mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) (quartet_block2 b)))
  ≔ match b [
  | false. ↦ quartet_points_count (quartet_block2 false.) (refl two)
  | true. ↦ quartet_points_count (quartet_block2 true.) (refl two) ]
def quartet_block3_points (b : Bool) : Mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) (quartet_block3 b)))
  ≔ match b [
  | false. ↦ quartet_points_count (quartet_block3 false.) (refl two)
  | true. ↦ quartet_points_count (quartet_block3 true.) (refl two) ]

def QuartetPointsTwo (f : Fin quartet_four → Bool) : Type
  ≔ Mere (Id Type (Fin two) (QuartetBlockPoints (Fin quartet_four) f))

def quartet_block_points_index
  : (t : Fin quartet_three) (B : QuartetBlocks (Fin quartet_four) (quartet_partition_of_index t .fst))
    → QuartetPointsTwo (B .fst)
  ≔ quartet_trio_cases (t ↦ (B : QuartetBlocks (Fin quartet_four) (quartet_partition_of_index t .fst))
      → QuartetPointsTwo (B .fst))
      (B ↦ transport (Fin quartet_four → Bool) QuartetPointsTwo (quartet_block1 (B .fst quartet_e0)) (B .fst)
        (quartet_block1_rigid B) (quartet_block1_points (B .fst quartet_e0)))
      (B ↦ transport (Fin quartet_four → Bool) QuartetPointsTwo (quartet_block2 (B .fst quartet_e0)) (B .fst)
        (quartet_block2_rigid B) (quartet_block2_points (B .fst quartet_e0)))
      (B ↦ transport (Fin quartet_four → Bool) QuartetPointsTwo (quartet_block3 (B .fst quartet_e0)) (B .fst)
        (quartet_block3_rigid B) (quartet_block3_points (B .fst quartet_e0)))

def quartet_block_points_two_fin (s : QuartetPartitions (Fin quartet_four))
  : (B : QuartetBlocks (Fin quartet_four) (s .fst)) → QuartetPointsTwo (B .fst)
  ≔ transport (QuartetPartitions (Fin quartet_four))
      (s' ↦ (B : QuartetBlocks (Fin quartet_four) (s' .fst)) → QuartetPointsTwo (B .fst))
      (quartet_partition_of_index (quartet_partition_index s)) s (quartet_partition_classify s)
      (quartet_block_points_index (quartet_partition_index s))

{` Transfer to every 4-element set. `}
def quartet_blocks_two (A : Type) (h : Mere (Id Type (Fin quartet_four) A))
  : (s : QuartetPartitions A) → Mere (Id Type (Fin two) (QuartetBlocks A (s .fst)))
  ≔ quartet_transfer (T ↦ (s : QuartetPartitions T) → Mere (Id Type (Fin two) (QuartetBlocks T (s .fst)))) A
      (pi_prop (QuartetPartitions A) (s ↦ Mere (Id Type (Fin two) (QuartetBlocks A (s .fst))))
        (s ↦ mere_isprop (Id Type (Fin two) (QuartetBlocks A (s .fst)))))
      quartet_blocks_two_fin h

def quartet_block_points_two (A : Type) (h : Mere (Id Type (Fin quartet_four) A))
  : (s : QuartetPartitions A) (B : QuartetBlocks A (s .fst)) → Mere (Id Type (Fin two) (QuartetBlockPoints A (B .fst)))
  ≔ quartet_transfer
      (T ↦ (s : QuartetPartitions T) (B : QuartetBlocks T (s .fst)) → Mere (Id Type (Fin two) (QuartetBlockPoints T (B .fst))))
      A
      (pi_prop (QuartetPartitions A)
        (s ↦ (B : QuartetBlocks A (s .fst)) → Mere (Id Type (Fin two) (QuartetBlockPoints A (B .fst))))
        (s ↦ pi_prop (QuartetBlocks A (s .fst)) (B ↦ Mere (Id Type (Fin two) (QuartetBlockPoints A (B .fst))))
          (B ↦ mere_isprop (Id Type (Fin two) (QuartetBlockPoints A (B .fst))))))
      quartet_block_points_two_fin h

{` thm:lAC-2-3-4: for every set X, X-AC(2) and X-AC(3) imply X-AC(4).
   Choose a 2+2 partition with X-AC(3), one of its two parts with X-AC(2),
   and an element of the chosen part with X-AC(2). `}
def local_choice_two_three_four (X : Type) (hX : isSet X)
  (c2 : LocalChoiceOfSize X two) (c3 : LocalChoiceOfSize X quartet_three) : LocalChoiceOfSize X quartet_four
  ≔ P ne ↦
    let A : X → Type ≔ x ↦ P x .fst .fst in
    let h4 : (x : X) → Mere (Id Type (Fin quartet_four) (A x)) ≔ x ↦ P x .snd in
    let PF : X → FiniteSetsAt quartet_three
      ≔ x ↦ quartet_sized quartet_three (QuartetPartitions (A x)) (quartet_partitions_three (A x) (h4 x)) in
    mere_rec ((x : X) → QuartetPartitions (A x)) (Mere ((x : X) → A x)) (mere_isprop ((x : X) → A x))
      (s ↦
        let BF : X → FiniteSetsAt two
          ≔ x ↦ quartet_sized two (QuartetBlocks (A x) (s x .fst)) (quartet_blocks_two (A x) (h4 x) (s x)) in
        mere_rec ((x : X) → QuartetBlocks (A x) (s x .fst)) (Mere ((x : X) → A x)) (mere_isprop ((x : X) → A x))
          (B ↦
            let EF : X → FiniteSetsAt two
              ≔ x ↦ quartet_sized two (QuartetBlockPoints (A x) (B x .fst))
                  (quartet_block_points_two (A x) (h4 x) (s x) (B x)) in
            trunc_map native_truncation ((x : X) → QuartetBlockPoints (A x) (B x .fst)) ((x : X) → A x)
              (e x ↦ e x .fst)
              (c2 EF (x ↦ quartet_sized_point (suc. zero.) (QuartetBlockPoints (A x) (B x .fst))
                (quartet_block_points_two (A x) (h4 x) (s x) (B x)))))
          (c2 BF (x ↦ quartet_sized_point (suc. zero.) (QuartetBlocks (A x) (s x .fst))
            (quartet_blocks_two (A x) (h4 x) (s x)))))
      (c3 PF (x ↦ quartet_sized_point two (QuartetPartitions (A x)) (quartet_partitions_three (A x) (h4 x))))

{` Litmus checks: the three partitions of Fin 4 are pairwise distinct, and
   the part of (0 1)(2 3) containing 0 is {0, 1}. `}
def quartet_partitions_distinct12 : Not (Id (QuartetPartitions (Fin quartet_four)) quartet_partition1 quartet_partition2)
  ≔ p ↦ quartet_ne quartet_e1 quartet_e2 (refl (false. : Bool))
      (map_path (QuartetPartitions (Fin quartet_four)) (Fin quartet_four) (s ↦ s .fst quartet_e0)
        quartet_partition1 quartet_partition2 p)
def quartet_partitions_distinct13 : Not (Id (QuartetPartitions (Fin quartet_four)) quartet_partition1 quartet_partition3)
  ≔ p ↦ quartet_ne quartet_e1 quartet_e3 (refl (false. : Bool))
      (map_path (QuartetPartitions (Fin quartet_four)) (Fin quartet_four) (s ↦ s .fst quartet_e0)
        quartet_partition1 quartet_partition3 p)
def quartet_partitions_distinct23 : Not (Id (QuartetPartitions (Fin quartet_four)) quartet_partition2 quartet_partition3)
  ≔ p ↦ quartet_ne quartet_e2 quartet_e3 (refl (false. : Bool))
      (map_path (QuartetPartitions (Fin quartet_four)) (Fin quartet_four) (s ↦ s .fst quartet_e0)
        quartet_partition2 quartet_partition3 p)
def quartet_block_example
  : Id (Fin quartet_four → Bool) (quartet_block1 true.)
      (x ↦ quartet_or (quartet_eqb x quartet_e0) (quartet_eqb x quartet_e1))
  ≔ funext (Fin quartet_four) (_ ↦ Bool) (quartet_block1 true.)
      (x ↦ quartet_or (quartet_eqb x quartet_e0) (quartet_eqb x quartet_e1))
      (quartet_cases (x ↦ Id Bool (quartet_block1 true. x) (quartet_or (quartet_eqb x quartet_e0) (quartet_eqb x quartet_e1)))
        (refl (true. : Bool)) (refl (true. : Bool)) (refl (false. : Bool)) (refl (false. : Bool)))
