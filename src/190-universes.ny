export "148-order-gcd-lcm"
export "153-heavy-transport"

{` Universes.  Narya has a single Type : Type, so a univalent universe U
   of the book is modelled by the image of its decoding map: a
   proposition-valued predicate `small` on Type, closed under the type
   formers that the book assumes of every universe (including the
   propositional truncation, which the book postulates in each universe).
   Results below hold for every such universe, not only for Type itself. `}
def Universe : Type ≔ sig (
  small : Type → Type,
  small_prop : (A : Type) → isProp (small A),
  empty_small : small Empty,
  unit_small : small Unit,
  bool_small : small Bool,
  nat_small : small Nat,
  sum_small : (A B : Type) → small A → small B → small (Sum A B),
  sigma_small : (A : Type) (B : A → Type) → small A → ((a : A) → small (B a)) → small (Σ A B),
  pi_small : (A : Type) (B : A → Type) → small A → ((a : A) → small (B a)) → small ((a : A) → B a),
  id_small : (A : Type) → small A → (x y : A) → small (Id A x y),
  trunc_small : (A : Type) → small A → small (Mere A) )

{` The universe as a type: a subtype of Type, hence univalent. `}
def UniverseType (U : Universe) : Type ≔ Σ Type (U .small)

{` A nested pair U : U', with cumulativity. `}
def NestedUniverses : Type ≔ sig (
  lower : Universe,
  upper : Universe,
  cumulative : (A : Type) → lower .small A → upper .small A,
  lower_in_upper : upper .small (UniverseType lower) )

{` Example: the universe of all types, into which every universe nests. `}
def total_universe : Universe
  ≔ (_ ↦ Unit, _ ↦ unit_prop, star., star., star., star.,
      (A B _ _ ↦ star.), (A B _ _ ↦ star.), (A B _ _ ↦ star.), (A _ x y ↦ star.), (A _ ↦ star.))

def total_nested (U : Universe) : NestedUniverses ≔ (U, total_universe, (A _ ↦ star.), star.)

def small_equiv (U : Universe) (A B : Type) (e : Equiv A B) (s : U .small A) : U .small B
  ≔ transport Type (U .small) A B (ua A B e) s

{` def:ess-loc-small. Equivalences are native; the book's notion is
   equivalent (equivalence_conventions_equiv). `}
def EssentiallySmall (U : Universe) (A : Type) : Type ≔ Σ (UniverseType U) (X ↦ Equiv A (X .fst))
def LocallySmall (U : Universe) (A : Type) : Type ≔ (x y : A) → EssentiallySmall U (Id A x y)

def essentially_small_book_equiv (U : Universe) (A : Type)
  : Equiv (EssentiallySmall U A) (Σ (UniverseType U) (X ↦ BookEquiv A (X .fst)))
  ≔ family_equiv (UniverseType U) (X ↦ Equiv A (X .fst)) (X ↦ BookEquiv A (X .fst))
      (X ↦ equivalence_conventions_equiv A (X .fst))

def equiv_singleton_contractible (A : Type) : isContr (Σ Type (X ↦ Equiv A X))
  ≔ hlevel_equiv zero. (Σ Type (X ↦ Id Type A X)) (Σ Type (X ↦ Equiv A X))
      (family_equiv Type (X ↦ Id Type A X) (X ↦ Equiv A X) (X ↦ univalence_equiv A X))
      (iscontr_idfrom Type A)

{` Essential smallness is a proposition, by univalence. `}
def essentially_small_prop (U : Universe) (A : Type) : isProp (EssentiallySmall U A)
  ≔ let T ≔ Σ (Σ Type (X ↦ Equiv A X)) (p ↦ U .small (p .fst)) in
    let hT : isProp T ≔ sigma_prop (Σ Type (X ↦ Equiv A X)) (p ↦ U .small (p .fst))
      (contractible_prop (Σ Type (X ↦ Equiv A X)) (equiv_singleton_contractible A)) (p ↦ U .small_prop (p .fst)) in
    let f ≔ ((v ↦ ((v .fst .fst, v .snd), v .fst .snd)) : EssentiallySmall U A → T) in
    let g ≔ ((t ↦ ((t .fst .fst, t .snd), t .fst .snd)) : T → EssentiallySmall U A) in
    u v ↦ refl g (hT (f u) (f v))

def small_essentially_small (U : Universe) (A : Type) (s : U .small A) : EssentiallySmall U A
  ≔ ((A, s), identity_equiv A)

def essentially_small_equiv (U : Universe) (A B : Type) (e : Equiv A B) (h : EssentiallySmall U A)
  : EssentiallySmall U B
  ≔ (h .fst, compose_equiv B A (h .fst .fst) (canonical_inverse_equiv A B e) (h .snd))

{` In this model a type is essentially small iff it lies in the image
   of the universe; the predicate is replete. `}
def essentially_small_is_small (U : Universe) (A : Type) (h : EssentiallySmall U A) : U .small A
  ≔ small_equiv U (h .fst .fst) A (canonical_inverse_equiv A (h .fst .fst) (h .snd)) (h .fst .snd)

def essentially_small_locally_small (U : Universe) (A : Type) (h : EssentiallySmall U A) : LocallySmall U A
  ≔ x y ↦ ((Id (h .fst .fst) (h .snd .map x) (h .snd .map y), U .id_small (h .fst .fst) (h .fst .snd) (h .snd .map x) (h .snd .map y)),
      equivalence_on_paths A (h .fst .fst) (h .snd) x y)

def small_locally_small (U : Universe) (A : Type) (s : U .small A) : LocallySmall U A
  ≔ essentially_small_locally_small U A (small_essentially_small U A s)

def locally_small_prop (U : Universe) (A : Type) : isProp (LocallySmall U A)
  ≔ pi_prop A (x ↦ (y : A) → EssentiallySmall U (Id A x y))
      (x ↦ pi_prop A (y ↦ EssentiallySmall U (Id A x y)) (y ↦ essentially_small_prop U (Id A x y)))

{` The criterion after def:ess-loc-small: a reflexive U-valued relation
   whose induced maps (x = y) → Eq(x,y) are equivalences. `}
def relation_paths_map (A : Type) (E : A → A → Type) (r : (x : A) → E x x) (x y : A) (p : Id A x y) : E x y
  ≔ transport A (E x) x y p (r x)

def locally_small_from_relation (U : Universe) (A : Type) (E : A → A → UniverseType U)
  (r : (x : A) → E x x .fst)
  (h : (x y : A) → isEquiv (Id A x y) (E x y .fst) (relation_paths_map A (x y ↦ E x y .fst) r x y))
  : LocallySmall U A
  ≔ x y ↦ (E x y, (relation_paths_map A (x y ↦ E x y .fst) r x y, h x y))

def locally_small_relation_path (U : Universe) (A : Type) (ls : LocallySmall U A) (x y : A) (p : Id A x y)
  : Id (ls x y .fst .fst) (relation_paths_map A (x y ↦ ls x y .fst .fst) (x ↦ ls x x .snd .map (refl x)) x y p)
      (ls x y .snd .map p)
  ≔ J A x (y p ↦ Id (ls x y .fst .fst) (relation_paths_map A (x y ↦ ls x y .fst .fst) (x ↦ ls x x .snd .map (refl x)) x y p)
        (ls x y .snd .map p))
      (transport_refl A (y ↦ ls x y .fst .fst) x (ls x x .snd .map (refl x))) y p

{` Conversely every locally small type has such a relation. `}
def locally_small_relation (U : Universe) (A : Type) (ls : LocallySmall U A)
  : Σ (A → A → UniverseType U) (E ↦ Σ ((x : A) → E x x .fst)
      (r ↦ (x y : A) → isEquiv (Id A x y) (E x y .fst) (relation_paths_map A (x y ↦ E x y .fst) r x y)))
  ≔ ((x y ↦ ls x y .fst), ((x ↦ ls x x .snd .map (refl x)),
      x y ↦ equiv_change_map (Id A x y) (ls x y .fst .fst) (ls x y .snd)
        (relation_paths_map A (x y ↦ ls x y .fst .fst) (x ↦ ls x x .snd .map (refl x)) x y)
        (p ↦ inverse (ls x y .fst .fst)
          (relation_paths_map A (x y ↦ ls x y .fst .fst) (x ↦ ls x x .snd .map (refl x)) x y p)
          (ls x y .snd .map p) (locally_small_relation_path U A ls x y p)) .equiv))
