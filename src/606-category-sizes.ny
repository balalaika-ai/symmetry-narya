export "605-preorders-and-posets"
export "191-small-closure"

{` Chapter 6 (cats.tex), rem:cat-sizes. Universes are modelled as in
   modules 190-193 by smallness predicates: U .small A says A : U, and a
   nested pair N says U : U'. A wild precategory has objects in some
   universe U' and hom types in some universe U. `}

{` "If they coincide, then we call C a U-small category." `}
def IsSmallWildPrecat (U : Universe) (C : WildPrecat) : Type
  ≔ Product (U .small (C .ob)) ((a b : C .ob) → U .small (C .hom a b))

{` "The other common case is where U : U', in which case we call C locally
   U-small": the hom types lie in U, the type of objects in U'. The hom
   condition alone is what is used later (ex:repr-functors). `}
def IsLocallySmallWildPrecat (U : Universe) (C : WildPrecat) : Type
  ≔ (a b : C .ob) → U .small (C .hom a b)

def IsLocallySmallOver (N : NestedUniverses) (C : WildPrecat) : Type
  ≔ Product (N .upper .small (C .ob)) (IsLocallySmallWildPrecat (N .lower) C)

def small_wild_precat_locally_small (U : Universe) (C : WildPrecat) (h : IsSmallWildPrecat U C)
  : IsLocallySmallWildPrecat U C
  ≔ h .snd

{` A U-small wild precategory is locally U-small over every U : U'. `}
def small_wild_precat_locally_small_over (N : NestedUniverses) (C : WildPrecat)
  (h : IsSmallWildPrecat (N .lower) C) : IsLocallySmallOver N C
  ≔ (N .cumulative (C .ob) (h .fst), h .snd)

{` "For instance, a path groupoid for a type X : U is U-small." `}
def path_wild_small (U : Universe) (X : Type) (sX : U .small X) : IsSmallWildPrecat U (PathWild X)
  ≔ (sX, x y ↦ U .id_small X sX x y)

{` "The (wild) categories of types, sets, pointed types ... built from types
   in U are all locally U-small." The wild category of types in U is the
   full subcategory of TypeWild on the U-small types; its objects are
   judgmentally UniverseType U. `}
def SmallTypePredicate (U : Universe) : Subtypes Type ≔ A ↦ (U .small A, U .small_prop A)

def TypeWildIn (U : Universe) : WildPrecat ≔ FullSubcat TypeWild (SmallTypePredicate U)

def type_wild_in_objects (U : Universe) : Id Type (TypeWildIn U .ob) (UniverseType U)
  ≔ refl (UniverseType U)

def type_wild_in_locally_small (U : Universe) : IsLocallySmallWildPrecat U (TypeWildIn U)
  ≔ A B ↦ U .pi_small (A .fst) (_ ↦ B .fst) (A .snd) (_ ↦ B .snd)

def type_wild_in_locally_small_over (N : NestedUniverses) : IsLocallySmallOver N (TypeWildIn (N .lower))
  ≔ (N .lower_in_upper, type_wild_in_locally_small (N .lower))

def type_wild_in_univalent (U : Universe) : IsUnivalentCat (TypeWildIn U)
  ≔ full_subcat_univalent TypeWild (SmallTypePredicate U) type_wild_univalent

{` Sets in U: the full subcategory of TypeWildIn U on the sets; its objects
   are judgmentally SetU U (module 191). `}
def SetWildIn (U : Universe) : WildPrecat
  ≔ FullSubcat (TypeWildIn U) (X ↦ (isSet (X .fst), isset_isprop (X .fst)))

def set_wild_in_objects (U : Universe) : Id Type (SetWildIn U .ob) (SetU U) ≔ refl (SetU U)

def set_wild_in_locally_small (U : Universe) : IsLocallySmallWildPrecat U (SetWildIn U)
  ≔ A B ↦ type_wild_in_locally_small U (A .fst) (B .fst)

def set_wild_in_locally_small_over (N : NestedUniverses) : IsLocallySmallOver N (SetWildIn (N .lower))
  ≔ (set_u_in_upper N, set_wild_in_locally_small (N .lower))

{` Pointed types in U: the full subcategory of PointedWild on pointed types
   with U-small carrier. Its type of objects is equivalent to
   Σ_{X : U} X, which lies in U'. `}
def PointedWildIn (U : Universe) : WildPrecat
  ≔ FullSubcat PointedWild (X ↦ (U .small (X .carrier), U .small_prop (X .carrier)))

def pointed_wild_in_hom_small (U : Universe) (X Y : Pointed) (sX : U .small (X .carrier))
  (sY : U .small (Y .carrier)) : U .small (BookPointedMap X Y)
  ≔ U .sigma_small (X .carrier → Y .carrier) (f ↦ Id (Y .carrier) (Y .point) (f (X .point)))
      (U .pi_small (X .carrier) (_ ↦ Y .carrier) sX (_ ↦ sY))
      (f ↦ U .id_small (Y .carrier) sY (Y .point) (f (X .point)))

def pointed_wild_in_locally_small (U : Universe) : IsLocallySmallWildPrecat U (PointedWildIn U)
  ≔ X Y ↦ pointed_wild_in_hom_small U (X .fst) (Y .fst) (X .snd) (Y .snd)

def pointed_wild_in_objects_equiv (U : Universe)
  : Equiv (Σ (UniverseType U) (X ↦ X .fst)) (PointedWildIn U .ob)
  ≔ quasi_inverse_equiv (Σ (UniverseType U) (X ↦ X .fst)) (PointedWildIn U .ob)
      (w ↦ ((w .fst .fst, w .snd), w .fst .snd))
      (v ↦ ((v .fst .carrier, v .snd), v .fst .point))
      (w ↦ refl w) (v ↦ refl v)

def pointed_wild_in_locally_small_over (N : NestedUniverses)
  : IsLocallySmallOver N (PointedWildIn (N .lower))
  ≔ (small_equiv (N .upper) (Σ (UniverseType (N .lower)) (X ↦ X .fst)) (PointedWildIn (N .lower) .ob)
       (pointed_wild_in_objects_equiv (N .lower))
       (N .upper .sigma_small (UniverseType (N .lower)) (X ↦ X .fst) (N .lower_in_upper)
         (X ↦ N .cumulative (X .fst) (X .snd))),
     pointed_wild_in_locally_small (N .lower))

{` "This generalizes def:ess-loc-small for the case of path groupoids": the
   path groupoid of X is a locally U-small wild precategory exactly when X
   is a locally U-small type. `}
def path_wild_locally_small_to_type (U : Universe) (X : Type)
  (h : IsLocallySmallWildPrecat U (PathWild X)) : LocallySmall U X
  ≔ x y ↦ small_essentially_small U (Id X x y) (h x y)

def type_locally_small_to_path_wild (U : Universe) (X : Type) (h : LocallySmall U X)
  : IsLocallySmallWildPrecat U (PathWild X)
  ≔ x y ↦ essentially_small_is_small U (Id X x y) (h x y)

def path_wild_locally_small_iff (U : Universe) (X : Type)
  : Product (IsLocallySmallWildPrecat U (PathWild X) → LocallySmall U X)
      (LocallySmall U X → IsLocallySmallWildPrecat U (PathWild X))
  ≔ (path_wild_locally_small_to_type U X, type_locally_small_to_path_wild U X)

{` Litmus: the path groupoid of Nat is small in every universe, and the
   wild category of all types is locally small for the total universe. `}
def nat_path_wild_small (U : Universe) : IsSmallWildPrecat U (PathWild Nat)
  ≔ path_wild_small U Nat (U .nat_small)

def type_wild_total_locally_small : IsLocallySmallWildPrecat total_universe TypeWild
  ≔ A B ↦ star.
