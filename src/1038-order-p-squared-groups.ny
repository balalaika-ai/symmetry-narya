export "1037-order-p-squared-elements"

{` Chapter 10, cor:orderpsquaredgroups (fingp.tex 218-226): a noncyclic
   group G of order p^2 (p prime) is of the form C_p × C_p, i.e. merely
   G = C_p × C_p in the type of groups.

   The book's proof stops after "g^p = e for all g" (footnote: "the
   classical proof involves choosing nontrivial elements -- see what can
   be done about that"). The completion: choose (merely; the goal is a
   proposition) a central g ≠ e (module 1037) and h not a power of g. The
   map C_p × C_p → G, (s, t) ↦ f_g(s) f_h(t), with f_g, f_h the
   homomorphisms C_p → G sending the generator to g, h (module 1011), is
   an abstract homomorphism because g is central; it deloops to a group
   homomorphism (lem:homomabstrconcr, module 710). Its kernel is trivial:
   g^j h^k = e with 0 < k < p would make h a power of g (Bézout:
   k x = y p + 1). So it is a monomorphism between groups with p^2
   symmetries, hence (lem:Lagrangeascounting) an identification. `}

def usym_interchange (G : Group) (a a' b b' : USym G)
  (c : Id (USym G) (usym_mul G a' b) (usym_mul G b a'))
  : Id (USym G) (usym_mul G (usym_mul G a a') (usym_mul G b b')) (usym_mul G (usym_mul G a b) (usym_mul G a' b'))
  ≔ let U ≔ USym G in
    let m ≔ usym_mul G in
    let L ≔ usym_abstract_laws G in
    calc
      m (m a a') (m b b')
      = m a (m a' (m b b')) by inverse U (m a (m a' (m b b'))) (m (m a a') (m b b')) (L .assoc a a' (m b b'))
      = m a (m (m a' b) b') by map_path U U (m a) (m a' (m b b')) (m (m a' b) b') (L .assoc a' b b')
      = m a (m (m b a') b') by map_path U U (u ↦ m a (m u b')) (m a' b) (m b a') c
      = m a (m b (m a' b')) by map_path U U (m a) (m (m b a') b') (m b (m a' b')) (inverse U (m b (m a' b')) (m (m b a') b') (L .assoc b a' b'))
      = m (m a b) (m a' b') by L .assoc a b (m a' b') ∎

{` Powers of a central symmetry are central. `}
def central_power (G : Group) (g : USym G) (cen : (h : USym G) → Id (USym G) (usym_mul G h g) (usym_mul G g h))
  (k : Nat) (h : USym G) : Id (USym G) (usym_mul G h (usym_power G g k)) (usym_mul G (usym_power G g k) h)
  ≔ let U ≔ USym G in
    let m ≔ usym_mul G in
    let L ≔ usym_abstract_laws G in
    match k [
    | zero. ↦ concat U (m h (usym_unit G)) h (m (usym_unit G) h) (L .unit_right h)
        (inverse U (m (usym_unit G) h) h (L .unit_left h))
    | suc. k ↦
      let gk ≔ usym_power G g k in
      calc
        m h (usym_power G g (suc. k))
        = m h (m g gk) by map_path U U (m h) (usym_power G g (suc. k)) (m g gk) (usym_power_suc G g k)
        = m (m h g) gk by L .assoc h g gk
        = m (m g h) gk by map_path U U (u ↦ m u gk) (m h g) (m g h) (cen h)
        = m g (m h gk) by inverse U (m g (m h gk)) (m (m g h) gk) (L .assoc g h gk)
        = m g (m gk h) by map_path U U (m g) (m h gk) (m gk h) (central_power G g cen k h)
        = m (m g gk) h by L .assoc g gk h
        = m (usym_power G g (suc. k)) h
          by map_path U U (u ↦ m u h) (m g gk) (usym_power G g (suc. k))
            (inverse U (usym_power G g (suc. k)) (m g gk) (usym_power_suc G g k)) ∎ ]

def prod_usym_fst (G H : Group) (r : USym (product_group G H)) : USym G ≔ r .fst
def prod_usym_snd (G H : Group) (r : USym (product_group G H)) : USym H ≔ r .snd

{` The homomorphisms C_p → G of g and h, and their values on generator powers. `}
def cyclic_value_power (b : Nat) (G : Group) (g : USym G) (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (s : USym (cyclic_group (suc. b)))
  : Σ Nat (k ↦ Product (BookLt k (suc. b))
      (Id (USym G) (usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G g hg) s) (usym_power G g k)))
  ≔ let C ≔ cyclic_group (suc. b) in
    let f ≔ cyclic_hom_of_element b G g hg in
    let w ≔ cyclic_symmetry_power_index b s in
    (w .fst, (w .snd .fst,
      concat (USym G) (usym_hom C G f s) (usym_hom C G f (usym_power C (cyclic_group_generator b) (w .fst))) (usym_power G g (w .fst))
        (map_path (USym C) (USym G) (usym_hom C G f) s (usym_power C (cyclic_group_generator b) (w .fst))
          (inverse (USym C) (usym_power C (cyclic_group_generator b) (w .fst)) s (w .snd .snd)))
        (cyclic_hom_generator_power b G g hg (w .fst))))

def cyclic_value_central (b : Nat) (G : Group) (g : USym G) (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
  (cen : (h : USym G) → Id (USym G) (usym_mul G h g) (usym_mul G g h)) (s : USym (cyclic_group (suc. b))) (x : USym G)
  : Id (USym G) (usym_mul G x (usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G g hg) s))
      (usym_mul G (usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G g hg) s) x)
  ≔ let v ≔ cyclic_value_power b G g hg s in
    let a ≔ usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G g hg) s in
    transport (USym G) (u ↦ Id (USym G) (usym_mul G x u) (usym_mul G u x)) (usym_power G g (v .fst)) a
      (inverse (USym G) a (usym_power G g (v .fst)) (v .snd .snd))
      (central_power G g cen (v .fst) x)

{` The map F : C_p × C_p → G, (s, t) ↦ f_g(s) f_h(t). `}
def pair_map (b : Nat) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (r : USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))) : USym G
  ≔ usym_mul G (usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G g hg) (prod_usym_fst (cyclic_group (suc. b)) (cyclic_group (suc. b)) r))
      (usym_hom (cyclic_group (suc. b)) G (cyclic_hom_of_element b G h hh) (prod_usym_snd (cyclic_group (suc. b)) (cyclic_group (suc. b)) r))

def pair_map_hom (b : Nat) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x))
  : IsAbstractHom (abstr (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))) (abstr G) (pair_map b G g h hg hh)
  ≔ s s' ↦
    let C ≔ cyclic_group (suc. b) in
    let P ≔ product_group C C in
    let U ≔ USym G in
    let m ≔ usym_mul G in
    let fg ≔ usym_hom C G (cyclic_hom_of_element b G g hg) in
    let fh ≔ usym_hom C G (cyclic_hom_of_element b G h hh) in
    let s1 ≔ prod_usym_fst C C s in let s2 ≔ prod_usym_snd C C s in
    let t1 ≔ prod_usym_fst C C s' in let t2 ≔ prod_usym_snd C C s' in
    let ss ≔ usym_mul P s s' in
    calc
      m (fg (prod_usym_fst C C ss)) (fh (prod_usym_snd C C ss))
      = m (fg (usym_mul C s1 t1)) (fh (prod_usym_snd C C ss))
        by map_path (USym C) U (x ↦ m (fg x) (fh (prod_usym_snd C C ss))) (prod_usym_fst C C ss) (usym_mul C s1 t1)
          (product_group_mul_fst C C s s')
      = m (fg (usym_mul C s1 t1)) (fh (usym_mul C s2 t2))
        by map_path (USym C) U (y ↦ m (fg (usym_mul C s1 t1)) (fh y)) (prod_usym_snd C C ss) (usym_mul C s2 t2)
          (product_group_mul_snd C C s s')
      = m (m (fg s1) (fg t1)) (fh (usym_mul C s2 t2))
        by map_path U U (x ↦ m x (fh (usym_mul C s2 t2))) (fg (usym_mul C s1 t1)) (m (fg s1) (fg t1))
          (usym_hom_mul C G (cyclic_hom_of_element b G g hg) s1 t1)
      = m (m (fg s1) (fg t1)) (m (fh s2) (fh t2))
        by map_path U U (m (m (fg s1) (fg t1))) (fh (usym_mul C s2 t2)) (m (fh s2) (fh t2))
          (usym_hom_mul C G (cyclic_hom_of_element b G h hh) s2 t2)
      = m (m (fg s1) (fh s2)) (m (fg t1) (fh t2))
        by usym_interchange G (fg s1) (fg t1) (fh s2) (fh t2)
          (inverse U (m (fh s2) (fg t1)) (m (fg t1) (fh s2)) (cyclic_value_central b G g hg cen t1 (fh s2))) ∎

def pair_hom (b : Nat) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x))
  : GroupHom (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G
  ≔ deloop_hom (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G
      (pair_map b G g h hg hh, pair_map_hom b G g h hg hh cen)

def abstract_hom_map (G H : AbstractGroup) (f : AbstractHom G H) : G .carrier → H .carrier ≔ f .fst

def pair_hom_usym (b : Nat) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x))
  (r : USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))))
  : Id (USym G) (usym_hom (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G (pair_hom b G g h hg hh cen) r)
      (pair_map b G g h hg hh r)
  ≔ let P ≔ product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)) in
    let F : AbstractHom (abstr P) (abstr G) ≔ (pair_map b G g h hg hh, pair_map_hom b G g h hg hh cen) in
    happly (USym P) (_ ↦ USym G) (usym_hom P G (pair_hom b G g h hg hh cen)) (pair_map b G g h hg hh)
      (map_path (AbstractHom (abstr P) (abstr G)) (USym P → USym G) (abstract_hom_map (abstr P) (abstr G))
        (abstr_hom P G (pair_hom b G g h hg hh cen)) F (deloop_hom_section P G F))
      r

{` Reduction of exponents modulo p. `}
def usym_power_reduce (b : Nat) (G : Group) (g : USym G) (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (M : Nat)
  : Σ (Remainder (suc. b)) (r ↦ Id (USym G) (usym_power G g M) (usym_power G g (r .fst)))
  ≔ let d ≔ euclidean_division M (suc. b) (nat_positive_book b) in
    ((d .fst .snd, d .snd .fst),
     concat (USym G) (usym_power G g M) (usym_power G g (add (mul (d .fst .fst) (suc. b)) (d .fst .snd))) (usym_power G g (d .fst .snd))
       (map_path Nat (USym G) (usym_power G g) M (add (mul (d .fst .fst) (suc. b)) (d .fst .snd)) (d .snd .snd))
       (usym_power_period_left G g (suc. b) hg (d .fst .fst) (d .fst .snd)))

{` If g^j h^k = e with 0 < k < p, then h is a power of g. `}
def pair_kernel_power (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (j k : Nat) (k0 : Not (Id Nat k zero.)) (kp : BookLt k (suc. b))
  (e : Id (USym G) (usym_mul G (usym_power G g j) (usym_power G h k)) (usym_unit G))
  : Σ (Remainder (suc. b)) (r ↦ Id (USym G) h (usym_power G g (r .fst)))
  ≔ let p : Nat ≔ suc. b in
    let U ≔ USym G in
    let A ≔ abstr G in
    let gj ≔ usym_power G g j in
    let hk ≔ usym_power G h k in
    let ginv : Id U (usym_power G g (mul j b)) (usym_inv G gj)
      ≔ ag_inv_unique_left A gj (usym_power G g (mul j b))
          (calc
            usym_mul G (usym_power G g (mul j b)) gj
            = usym_power G g (add (mul j b) j)
              by inverse U (usym_power G g (add (mul j b) j)) (usym_mul G (usym_power G g (mul j b)) gj)
                (usym_power_add_left G g (mul j b) j)
            = usym_unit G by usym_power_multiple_unit G g p hg j ∎) in
    let hk_eq : Id U hk (usym_power G g (mul j b))
      ≔ concat U hk (usym_inv G gj) (usym_power G g (mul j b)) (ag_inv_unique_right A gj hk e)
          (inverse U (usym_power G g (mul j b)) (usym_inv G gj) ginv) in
    let kpos : Lt zero. k ≔ match k [ zero. ↦ absurd (Lt zero. zero.) (k0 (refl (zero. : Nat))) | suc. k' ↦ star. ] in
    let ndiv : Not (NatDivides p k)
      ≔ dv ↦ usym_book_le_lt_absurd p k (le_to_book p k (nat_divides_le_positive p k kpos dv)) kp in
    let bz ≔ coprime_bezout_nat k p (nat_coprime_sym p k (prime_not_divides_coprime p k hp ndiv)) kpos (prime_positive p hp) in
    let x ≔ bz .fst in
    let y ≔ bz .snd .fst in
    let hpow : Id U h (usym_power G g (mul (mul j b) x))
      ≔ calc
          h
          = usym_mul G h (usym_unit G) by inverse U (usym_mul G h (usym_unit G)) h ((usym_abstract_laws G) .unit_right h)
          = usym_mul G h (usym_power G h (mul y p))
            by map_path U U (usym_mul G h) (usym_unit G) (usym_power G h (mul y p))
              (inverse U (usym_power G h (mul y p)) (usym_unit G) (usym_power_multiple_unit G h p hh y))
          = usym_power G h (suc. (mul y p))
            by inverse U (usym_power G h (suc. (mul y p))) (usym_mul G h (usym_power G h (mul y p))) (usym_power_suc G h (mul y p))
          = usym_power G h (mul k x)
            by map_path Nat U (usym_power G h) (suc. (mul y p)) (mul k x) (inverse Nat (mul k x) (suc. (mul y p)) (bz .snd .snd))
          = usym_power G hk x by usym_power_mul G h k x
          = usym_power G (usym_power G g (mul j b)) x by map_path U U (u ↦ usym_power G u x) hk (usym_power G g (mul j b)) hk_eq
          = usym_power G g (mul (mul j b) x)
            by inverse U (usym_power G g (mul (mul j b) x)) (usym_power G (usym_power G g (mul j b)) x) (usym_power_mul G g (mul j b) x) ∎ in
    let red ≔ usym_power_reduce b G g hg (mul (mul j b) x) in
    (red .fst, concat U h (usym_power G g (mul (mul j b) x)) (usym_power G g (red .fst .fst)) hpow (red .snd))

{` The kernel of F is trivial. `}
def pair_map_kernel (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (gne : Not (Id (USym G) g (usym_unit G)))
  (out : (r : Remainder (suc. b)) → Not (Id (USym G) h (usym_power G g (r .fst))))
  (r : USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))))
  (e : Id (USym G) (pair_map b G g h hg hh r) (usym_unit G))
  : Id (USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))) r
      (usym_unit (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))))
  ≔ let p : Nat ≔ suc. b in
    let C ≔ cyclic_group p in
    let P ≔ product_group C C in
    let U ≔ USym G in
    let vg ≔ cyclic_value_power b G g hg (prod_usym_fst C C r) in
    let vh ≔ cyclic_value_power b G h hh (prod_usym_snd C C r) in
    let j ≔ vg .fst in
    let k ≔ vh .fst in
    let fg ≔ usym_hom C G (cyclic_hom_of_element b G g hg) in
    let fh ≔ usym_hom C G (cyclic_hom_of_element b G h hh) in
    let e2 : Id U (usym_mul G (usym_power G g j) (usym_power G h k)) (usym_unit G)
      ≔ calc
          usym_mul G (usym_power G g j) (usym_power G h k)
          = usym_mul G (fg (prod_usym_fst C C r)) (usym_power G h k)
            by map_path U U (u ↦ usym_mul G u (usym_power G h k)) (usym_power G g j) (fg (prod_usym_fst C C r))
              (inverse U (fg (prod_usym_fst C C r)) (usym_power G g j) (vg .snd .snd))
          = usym_mul G (fg (prod_usym_fst C C r)) (fh (prod_usym_snd C C r))
            by map_path U U (usym_mul G (fg (prod_usym_fst C C r))) (usym_power G h k) (fh (prod_usym_snd C C r))
              (inverse U (fh (prod_usym_snd C C r)) (usym_power G h k) (vh .snd .snd))
          = usym_unit G by e ∎ in
    match nat_dec_eq k zero. [
    | inl. k0 ↦
      let gj : Id U (usym_power G g j) (usym_unit G)
        ≔ concat U (usym_power G g j) (usym_mul G (usym_power G g j) (usym_power G h k)) (usym_unit G)
            (concat U (usym_power G g j) (usym_mul G (usym_power G g j) (usym_unit G)) (usym_mul G (usym_power G g j) (usym_power G h k))
              (inverse U (usym_mul G (usym_power G g j) (usym_unit G)) (usym_power G g j) ((usym_abstract_laws G) .unit_right (usym_power G g j)))
              (map_path Nat U (n ↦ usym_mul G (usym_power G g j) (usym_power G h n)) zero. k (inverse Nat k zero. k0)))
            e2 in
      let j0 : Id Nat j zero.
        ≔ usym_power_injective_below G g p (prime_order_powers_nontrivial p hp G g hg gne) j zero. (vg .snd .fst)
            (nat_positive_book b) gj in
      let gen ≔ cyclic_group_generator b in
      let w1 ≔ cyclic_symmetry_power_index b (prod_usym_fst C C r) in
      let w2 ≔ cyclic_symmetry_power_index b (prod_usym_snd C C r) in
      product_symmetries_ext C C r (usym_unit P)
        (calc
          prod_usym_fst C C r
          = usym_power C gen (w1 .fst) by inverse (USym C) (usym_power C gen (w1 .fst)) (prod_usym_fst C C r) (w1 .snd .snd)
          = usym_power C gen zero. by map_path Nat (USym C) (usym_power C gen) (w1 .fst) zero. j0
          = usym_unit C by usym_power_zero C gen ∎)
        (calc
          prod_usym_snd C C r
          = usym_power C gen (w2 .fst) by inverse (USym C) (usym_power C gen (w2 .fst)) (prod_usym_snd C C r) (w2 .snd .snd)
          = usym_power C gen zero. by map_path Nat (USym C) (usym_power C gen) (w2 .fst) zero. k0
          = usym_unit C by usym_power_zero C gen ∎)
    | inr. kn ↦
      let red ≔ pair_kernel_power b hp G g h hg hh j k kn (vh .snd .fst) e2 in
      absurd (Id (USym P) r (usym_unit P)) (out (red .fst) (red .snd)) ]

{` The homomorphism is a monomorphism. `}
def pair_hom_injective (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x)) (gne : Not (Id (USym G) g (usym_unit G)))
  (out : (r : Remainder (suc. b)) → Not (Id (USym G) h (usym_power G g (r .fst))))
  : PathReflecting (USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))) (USym G)
      (usym_hom (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G (pair_hom b G g h hg hh cen))
  ≔ r r' q ↦
    let P ≔ product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)) in
    let UP ≔ USym P in
    let U ≔ USym G in
    let f ≔ pair_hom b G g h hg hh cen in
    let F ≔ usym_hom P G f in
    let LP ≔ usym_abstract_laws P in
    let ir ≔ usym_inv P r' in
    let k : Id UP (usym_mul P r ir) (usym_unit P)
      ≔ pair_map_kernel b hp G g h hg hh gne out (usym_mul P r ir)
          (calc
            pair_map b G g h hg hh (usym_mul P r ir)
            = F (usym_mul P r ir)
              by inverse U (F (usym_mul P r ir)) (pair_map b G g h hg hh (usym_mul P r ir)) (pair_hom_usym b G g h hg hh cen (usym_mul P r ir))
            = usym_mul G (F r) (F ir) by usym_hom_mul P G f r ir
            = usym_mul G (F r) (usym_inv G (F r')) by map_path U U (usym_mul G (F r)) (F ir) (usym_inv G (F r')) (usym_hom_inv P G f r')
            = usym_mul G (F r') (usym_inv G (F r')) by map_path U U (u ↦ usym_mul G u (usym_inv G (F r'))) (F r) (F r') q
            = usym_unit G by (usym_abstract_laws G) .inv_right (F r') ∎) in
    calc
      r
      = usym_mul P r (usym_unit P) by inverse UP (usym_mul P r (usym_unit P)) r (LP .unit_right r)
      = usym_mul P r (usym_mul P ir r')
        by map_path UP UP (usym_mul P r) (usym_unit P) (usym_mul P ir r') (inverse UP (usym_mul P ir r') (usym_unit P) (ag_inv_left (abstr P) r'))
      = usym_mul P (usym_mul P r ir) r' by LP .assoc r ir r'
      = usym_mul P (usym_unit P) r' by map_path UP UP (u ↦ usym_mul P u r') (usym_mul P r ir) (usym_unit P) k
      = r' by LP .unit_left r' ∎

def pair_hom_mono (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x)) (gne : Not (Id (USym G) g (usym_unit G)))
  (out : (r : Remainder (suc. b)) → Not (Id (USym G) h (usym_power G g (r .fst))))
  : IsGroupMono (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G (pair_hom b G g h hg hh cen)
  ≔ injective_into_set_embedding (USym (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))) (USym G)
      (usym_hom (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))) G (pair_hom b G g h hg hh cen))
      (usym_set G) (pair_hom_injective b hp G g h hg hh cen gne out)

{` A monomorphism C_p × C_p → G with |G| = p^2 identifies G with C_p × C_p. `}
def pair_hom_identification (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power (suc. b) (suc. (suc. zero.)))) (g h : USym G)
  (hg : Id (USym G) (usym_power G g (suc. b)) (usym_unit G)) (hh : Id (USym G) (usym_power G h (suc. b)) (usym_unit G))
  (cen : (x : USym G) → Id (USym G) (usym_mul G x g) (usym_mul G g x)) (gne : Not (Id (USym G) g (usym_unit G)))
  (out : (r : Remainder (suc. b)) → Not (Id (USym G) h (usym_power G g (r .fst))))
  : Id Group G (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b)))
  ≔ let p : Nat ≔ suc. b in
    let C ≔ cyclic_group p in
    let P ≔ product_group C C in
    let hC ≔ cyclic_group_finite b in
    let hP ≔ product_group_finite C C hC hC in
    let m : GroupMonos G ≔ (P, (pair_hom b G g h hg hh cen, pair_hom_mono b hp G g h hg hh cen gne out)) in
    let S ≔ mono_to_subgroup G m in
    let pth : Id Group (subgroup_group G S) P ≔ mono_subgroup_group_path G m in
    let hS ≔ group_finite_path P (subgroup_group G S) (inverse Group (subgroup_group G S) P pth) hP in
    let cS : Id Nat (group_card (subgroup_group G S) hS) (group_card G hG)
      ≔ calc
          group_card (subgroup_group G S) hS
          = group_card P hP by group_card_path (subgroup_group G S) P pth hS hP
          = mul (group_card C hC) (group_card C hC) by product_group_card C C hC hC hP
          = mul p (group_card C hC) by map_path Nat Nat (x ↦ mul x (group_card C hC)) (group_card C hC) p (cyclic_group_card b hC)
          = mul p p by map_path Nat Nat (mul p) (group_card C hC) p (cyclic_group_card b hC)
          = nat_power p (suc. (suc. zero.))
            by map_path Nat Nat (x ↦ mul x p) p (mul (suc. zero.) p) (inverse Nat (mul (suc. zero.) p) p (mul_one_left p))
          = group_card G hG by inverse Nat (group_card G hG) (nat_power p (suc. (suc. zero.))) hc ∎ in
    concat Group G (subgroup_group G S) P
      (inverse Group (subgroup_group G S) G (subgroup_full_order_group_path G hG S hS cS)) pth

{` cor:orderpsquaredgroups: a noncyclic group of order p^2 is C_p × C_p. `}
def order_p_squared_noncyclic (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power (suc. b) (suc. (suc. zero.)))) (nc : NotCyclicGroup G)
  : Mere (Id Group G (product_group (cyclic_group (suc. b)) (cyclic_group (suc. b))))
  ≔ let p : Nat ≔ suc. b in
    let U ≔ USym G in
    let T ≔ Id Group G (product_group (cyclic_group p) (cyclic_group p)) in
    mere_rec (Σ U (g ↦ Product ((x : U) → Id U (usym_mul G x g) (usym_mul G g x)) (Not (Id U g (usym_unit G)))))
      (Mere T) (mere_isprop T)
      (w ↦
        let g ≔ w .fst in
        let hg ≔ order_p_squared_exponent b hp G hG hc nc g in
        mere_rec (Σ U (h ↦ (r : Remainder p) → Not (Id U h (usym_power G g (r .fst))))) (Mere T) (mere_isprop T)
          (v ↦ mere T (pair_hom_identification b hp G hG hc g (v .fst) hg (order_p_squared_exponent b hp G hG hc nc (v .fst))
            (w .snd .fst) (w .snd .snd) (v .snd)))
          (order_p_squared_outside b hp G hG hc nc g (w .snd .snd)))
      (p_group_central_nontrivial p hp (suc. zero.) G hG hc)

{` Litmus: the hypothesis "noncyclic" is needed: C_4 has order 2^2 but is
   not C_2 × C_2 (every symmetry of C_2 × C_2 squares to e, the generator
   of C_4 does not). `}
def cyclic_two_exponent_two : ExponentTwo (cyclic_group (suc. (suc. zero.)))
  ≔ t ↦
    let C ≔ cyclic_group (suc. (suc. zero.)) in
    calc
      usym_mul C t t
      = usym_mul C t (usym_power C t (suc. zero.))
        by map_path (USym C) (USym C) (usym_mul C t) t (usym_power C t (suc. zero.))
          (inverse (USym C) (usym_power C t (suc. zero.)) t (usym_power_one C t))
      = usym_power C t (suc. (suc. zero.))
        by inverse (USym C) (usym_power C t (suc. (suc. zero.))) (usym_mul C t (usym_power C t (suc. zero.)))
          (usym_power_suc C t (suc. zero.))
      = usym_unit C by cyclic_group_power_order (suc. zero.) t ∎

def cyclic_four_not_klein
  (e : Id Group (cyclic_group (suc. (suc. (suc. (suc. zero.))))) (product_group (cyclic_group (suc. (suc. zero.))) (cyclic_group (suc. (suc. zero.)))))
  : Empty
  ≔ let C4 ≔ cyclic_group (suc. (suc. (suc. (suc. zero.)))) in
    let C2 ≔ cyclic_group (suc. (suc. zero.)) in
    let ex : ExponentTwo C4
      ≔ transport Group ExponentTwo (product_group C2 C2) C4 (inverse Group C4 (product_group C2 C2) e)
          (product_exponent_two C2 C2 cyclic_two_exponent_two cyclic_two_exponent_two) in
    let s ≔ cyclic_group_generator (suc. (suc. (suc. zero.))) in
    cyclic_group_generator_powers_nontrivial (suc. (suc. (suc. zero.))) (suc. (suc. zero.))
      (lt_to_book zero. (suc. (suc. zero.)) star.) (lt_to_book (suc. (suc. zero.)) (suc. (suc. (suc. (suc. zero.)))) star.)
      (calc
        usym_power C4 s (suc. (suc. zero.))
        = usym_mul C4 s (usym_power C4 s (suc. zero.)) by usym_power_suc C4 s (suc. zero.)
        = usym_mul C4 s s by map_path (USym C4) (USym C4) (usym_mul C4 s) (usym_power C4 s (suc. zero.)) s (usym_power_one C4 s)
        = usym_unit C4 by ex s ∎)
