export "175-permutation-factorial"

{` Transpositions (a b) with a ≠ b, and the composite t_1 t_2 ... t_k of
   a word of them (t_k applied first). `}
def Transpositions (A : Type) : Type ≔ Σ A (a ↦ Σ A (b ↦ Not (Id A a b)))

def transposition_word_map (A : Type) (d : DecidableEquality A) (w : List (Transpositions A)) : A → A
  ≔ match w [
  | nil. ↦ identity A
  | cons. t rest ↦ compose A A A (transposition A d (t .fst) (t .snd .fst)) (transposition_word_map A d rest) ]

def TranspositionWord (A : Type) (d : DecidableEquality A) (s : Equiv A A) : Type
  ≔ Σ (List (Transpositions A)) (w ↦ (x : A) → Id A (s .map x) (transposition_word_map A d w x))

def transposition_diagonal (A : Type) (d : DecidableEquality A) (a x : A)
  : Id A (transposition A d a a x) x
  ≔ match d x a [
  | inl. p ↦ concat A (transposition A d a a x) (transposition A d a a a) x
      (refl (transposition A d a a) p)
      (concat A (transposition A d a a a) a x (transposition_left A d a a) (inverse A x a p))
  | inr. n ↦ transposition_fixed A d a a x n n ]

def option_extend (A : Type) (f : A → A) : Sum A Unit → Sum A Unit
  ≔ [ inl. a ↦ inl. (f a) | inr. u ↦ inr. u ]

def option_extend_homotopy (A : Type) (f g : A → A) (h : (a : A) → Id A (f a) (g a)) (x : Sum A Unit)
  : Id (Sum A Unit) (option_extend A f x) (option_extend A g x)
  ≔ match x [ inl. a ↦ inl. (h a) | inr. u ↦ refl (inr. u : Sum A Unit) ]

def lift_transposition (A : Type) (t : Transpositions A) : Transpositions (Sum A Unit)
  ≔ (inl. (t .fst), (inl. (t .snd .fst), p ↦ t .snd .snd (inl_injective A (t .fst) (t .snd .fst) p)))

def lift_word (A : Type) (w : List (Transpositions A)) : List (Transpositions (Sum A Unit))
  ≔ match w [ nil. ↦ nil. | cons. t rest ↦ cons. (lift_transposition A t) (lift_word A rest) ]

def inl_ne_inr (A : Type) (a : A) (p : Id (Sum A Unit) (inr. star.) (inl. a)) : Empty
  ≔ sum_encode A Unit (inr. star.) (inl. a) p

{` A transposition of inl-points acts as the transposition of A extended by the point. `}
def lift_transposition_at (A : Type) (d : DecidableEquality A) (a b : A) (x : Sum A Unit)
  : Id (Sum A Unit) (transposition (Sum A Unit) (option_decidable_equality A d) (inl. a) (inl. b) x)
      (option_extend A (transposition A d a b) x)
  ≔ let dB ≔ option_decidable_equality A d in
    let T ≔ transposition (Sum A Unit) dB (inl. a) (inl. b) in
    match x [
    | inr. u ↦ match u [ star. ↦ transposition_fixed (Sum A Unit) dB (inl. a) (inl. b) (inr. star.)
        (inl_ne_inr A a) (inl_ne_inr A b) ]
    | inl. y ↦ match d y a [
      | inl. p ↦ calc
          T (inl. y) = inl. b
            by concat (Sum A Unit) (T (inl. y)) (T (inl. a)) (inl. b) (refl T (inl. p : Id (Sum A Unit) (inl. y) (inl. a)))
              (transposition_left (Sum A Unit) dB (inl. a) (inl. b))
          = inl. (transposition A d a b y)
            by inverse (Sum A Unit) (inl. (transposition A d a b y)) (inl. b)
              (inl. (concat A (transposition A d a b y) (transposition A d a b a) b
                (refl (transposition A d a b) p) (transposition_left A d a b))) ∎
      | inr. na ↦ match d y b [
        | inl. q ↦ calc
            T (inl. y) = inl. a
              by transposition_at_b (Sum A Unit) dB (inl. a) (inl. b) (inl. y)
                (r ↦ na (inl_injective A y a r)) (inl. q)
            = inl. (transposition A d a b y)
              by inverse (Sum A Unit) (inl. (transposition A d a b y)) (inl. a)
                (inl. (transposition_at_b A d a b y na q)) ∎
        | inr. nb ↦ calc
            T (inl. y) = inl. y
              by transposition_fixed (Sum A Unit) dB (inl. a) (inl. b) (inl. y)
                (r ↦ na (inl_injective A y a r)) (r ↦ nb (inl_injective A y b r))
            = inl. (transposition A d a b y)
              by inverse (Sum A Unit) (inl. (transposition A d a b y)) (inl. y)
                (inl. (transposition_fixed A d a b y na nb)) ∎ ] ] ]

def lift_word_at (A : Type) (d : DecidableEquality A) (w : List (Transpositions A)) (x : Sum A Unit)
  : Id (Sum A Unit) (transposition_word_map (Sum A Unit) (option_decidable_equality A d) (lift_word A w) x)
      (option_extend A (transposition_word_map A d w) x)
  ≔ let dB ≔ option_decidable_equality A d in
    match w [
    | nil. ↦ match x [ inl. a ↦ refl (inl. a : Sum A Unit) | inr. u ↦ refl (inr. u : Sum A Unit) ]
    | cons. t rest ↦ calc
        transposition_word_map (Sum A Unit) dB (lift_word A (cons. t rest)) x
        = transposition (Sum A Unit) dB (inl. (t .fst)) (inl. (t .snd .fst))
            (option_extend A (transposition_word_map A d rest) x)
          by refl (transposition (Sum A Unit) dB (inl. (t .fst)) (inl. (t .snd .fst))) (lift_word_at A d rest x)
        = option_extend A (transposition A d (t .fst) (t .snd .fst))
            (option_extend A (transposition_word_map A d rest) x)
          by lift_transposition_at A d (t .fst) (t .snd .fst) (option_extend A (transposition_word_map A d rest) x)
        = option_extend A (transposition_word_map A d (cons. t rest)) x
          by match x [ inl. a ↦ refl (inl. (transposition A d (t .fst) (t .snd .fst) (transposition_word_map A d rest a)) : Sum A Unit)
                     | inr. u ↦ refl (inr. u : Sum A Unit) ] ∎ ]

def option_extension_extend (A : Type) (r : Equiv A A) (x : Sum A Unit)
  : Id (Sum A Unit) (option_extension A r .map x) (option_extend A (r .map) x)
  ≔ match x [ inl. a ↦ refl (inl. (r .map a) : Sum A Unit) | inr. u ↦ refl (inr. u : Sum A Unit) ]

{` One inductive step: s is the transposition (pt s(pt)) after the lifted
   word of its restriction. `}
def option_word_step (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  (w : List (Transpositions A))
  (hw : (a : A) → Id A (permutation_option_to A d s .snd .map a) (transposition_word_map A d w a))
  (x : Sum A Unit)
  : Id (Sum A Unit) (s .map x)
      (transposition (Sum A Unit) (option_decidable_equality A d) (inr. star.) (s .map (inr. star.))
        (transposition_word_map (Sum A Unit) (option_decidable_equality A d) (lift_word A w) x))
  ≔ let dB ≔ option_decidable_equality A d in
    let sw ≔ transposition (Sum A Unit) dB (inr. star.) (s .map (inr. star.)) in
    let r ≔ permutation_option_to A d s .snd in
    calc
      s .map x = sw (option_extension A r .map x)
        by inverse (Sum A Unit) (sw (option_extension A r .map x)) (s .map x)
          (refl ((e ↦ e .map x) : Equiv (Sum A Unit) (Sum A Unit) → Sum A Unit) (permutation_option_eta A d s))
      = sw (option_extend A (r .map) x) by refl sw (option_extension_extend A r x)
      = sw (option_extend A (transposition_word_map A d w) x)
        by refl sw (option_extend_homotopy A (r .map) (transposition_word_map A d w) hw x)
      = sw (transposition_word_map (Sum A Unit) dB (lift_word A w) x)
        by refl sw (inverse (Sum A Unit) (transposition_word_map (Sum A Unit) dB (lift_word A w) x)
          (option_extend A (transposition_word_map A d w) x) (lift_word_at A d w x)) ∎

def option_transposition_word (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  (w : TranspositionWord A d (permutation_option_to A d s .snd))
  : TranspositionWord (Sum A Unit) (option_decidable_equality A d) s
  ≔ let dB ≔ option_decidable_equality A d in
    let pt : Sum A Unit ≔ inr. star. in
    let W ≔ transposition_word_map (Sum A Unit) dB (lift_word A (w .fst)) in
    match dB pt (s .map pt) [
    | inl. same ↦ (lift_word A (w .fst), x ↦
        concat (Sum A Unit) (s .map x) (transposition (Sum A Unit) dB pt (s .map pt) (W x)) (W x)
          (option_word_step A d s (w .fst) (w .snd) x)
          (concat (Sum A Unit) (transposition (Sum A Unit) dB pt (s .map pt) (W x))
            (transposition (Sum A Unit) dB pt pt (W x)) (W x)
            (refl ((b ↦ transposition (Sum A Unit) dB pt b (W x)) : Sum A Unit → Sum A Unit)
              (inverse (Sum A Unit) pt (s .map pt) same))
            (transposition_diagonal (Sum A Unit) dB pt (W x))))
    | inr. moved ↦ (cons. (pt, (s .map pt, moved)) (lift_word A (w .fst)), option_word_step A d s (w .fst) (w .snd)) ]

{` Every permutation of Fin n has an explicit transposition word, by
   induction using eq:type-factorial. `}
def fin_transposition_word (n : Nat) (s : Equiv (Fin n) (Fin n))
  : TranspositionWord (Fin n) (fin_decidable_equality n) s
  ≔ match n [
  | zero. ↦ (nil., x ↦ match x [])
  | suc. k ↦ option_transposition_word (Fin k) (fin_decidable_equality k) s
      (fin_transposition_word k (permutation_option_to (Fin k) (fin_decidable_equality k) s .snd)) ]

def TranspositionGenerated (A : Type) (d : DecidableEquality A) (s : Equiv A A) : Type
  ≔ Mere (Σ (List (Transpositions A)) (w ↦ Id (A → A) (s .map) (transposition_word_map A d w)))

def transposition_generated_of_word (A : Type) (d : DecidableEquality A) (s : Equiv A A)
  (w : TranspositionWord A d s) : TranspositionGenerated A d s
  ≔ mere (Σ (List (Transpositions A)) (w ↦ Id (A → A) (s .map) (transposition_word_map A d w)))
      (w .fst, funext A (_ ↦ A) (s .map) (transposition_word_map A d (w .fst)) (w .snd))

def AllTranspositionGenerated (A : Type) : Type
  ≔ (d : DecidableEquality A) (s : Equiv A A) → TranspositionGenerated A d s

def fin_all_transposition_generated (n : Nat) : AllTranspositionGenerated (Fin n)
  ≔ d s ↦ transport (DecidableEquality (Fin n)) (e ↦ TranspositionGenerated (Fin n) e s)
      (fin_decidable_equality n) d
      (decidable_equality_prop (Fin n) (fin_set n) (fin_decidable_equality n) d)
      (transposition_generated_of_word (Fin n) (fin_decidable_equality n) s (fin_transposition_word n s))

{` The corollary after xca:perm-prod-transpositions: every permutation of a
   finite set is a composite of transpositions.  The proof is by induction
   via eq:type-factorial, not via the cycle decomposition used in the book. `}
def finite_transposition_generated (A : Type) (ha : IsFinite A) (s : Equiv A A)
  : TranspositionGenerated A (finite_decidable_equality A ha) s
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (TranspositionGenerated A (finite_decidable_equality A ha) s)
      (mere_isprop (Σ (List (Transpositions A))
        (w ↦ Id (A → A) (s .map) (transposition_word_map A (finite_decidable_equality A ha) w))))
      (p ↦ transport Type AllTranspositionGenerated (Fin (p .fst)) A
        (inverse Type A (Fin (p .fst)) (p .snd)) (fin_all_transposition_generated (p .fst))
        (finite_decidable_equality A ha) s) ha
