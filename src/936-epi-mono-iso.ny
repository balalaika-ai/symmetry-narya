export "934-epi-connected-fibers"

{` Chapter 9 (subgroups.tex), lem:epimonoiso (line 238, printed inside
   \wip): a homomorphism f : Hom(G, H) is an isomorphism (def:groupisomorphism,
   IsGroupIso: Bf÷ is an equivalence) iff it is both a monomorphism and an
   epimorphism (IsMono / IsEpi in the category of groups). The book's proof
   goes through the equivalence of groups and abstract groups (a TODO
   reference); we use the classifying maps instead: a monomorphism has set
   fibers (a covering, module 502 via module 687), an epimorphism has
   connected fibers (module 934), so all fibers are contractible. `}

def gepi_contractible_fibers_set (A B : Type) (f : A → B) (h : BookIsEquiv A B f) (b : B)
  : isSet (BookFiber A B f b)
  ≔ prop_is_set (BookFiber A B f b) (contractible_prop (BookFiber A B f b) (native_contraction (BookFiber A B f b) (h b)))

{` An isomorphism is a monomorphism and an epimorphism. `}
def gepi_iso_mono (G H : Group) (f : GroupHom G H) (h : IsGroupIso G H f) : IsMono (GroupCat .wild) G H f
  ≔ usym_injective_group_mono G H f
      (covering_group_mono G H f (gepi_contractible_fibers_set (BG G .carrier) (BG H .carrier) (hom_function G H f) h))

def gepi_iso_epi (G H : Group) (f : GroupHom G H) (h : IsGroupIso G H f) : IsEpi (GroupCat .wild) G H f
  ≔ gepi_connected_fibers_epi G H f
      (w ↦ contractible_connected (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w) (h w))

{` A monomorphism that is an epimorphism is an isomorphism. `}
def gepi_mono_epi_iso (G H : Group) (f : GroupHom G H) (m : IsMono (GroupCat .wild) G H f)
  (e : IsEpi (GroupCat .wild) G H f) : IsGroupIso G H f
  ≔ w ↦ native_connected_set_contractible (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w)
      (gepi_epi_connected_fibers G H f e w)
      (group_mono_covering G H f (group_mono_usym_injective G H f m) w)

{` lem:epimonoiso as an equivalence of propositions. `}
def gepi_iso_mono_epi_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupIso G H f) (Product (IsMono (GroupCat .wild) G H f) (IsEpi (GroupCat .wild) G H f))
  ≔ iff_equiv (IsGroupIso G H f) (Product (IsMono (GroupCat .wild) G H f) (IsEpi (GroupCat .wild) G H f))
      (is_group_iso_prop G H f)
      (product_prop (IsMono (GroupCat .wild) G H f) (IsEpi (GroupCat .wild) G H f)
        (is_mono_prop (GroupCat .wild) G H f) (is_epi_prop (GroupCat .wild) G H f))
      (h ↦ (gepi_iso_mono G H f h, gepi_iso_epi G H f h))
      (me ↦ gepi_mono_epi_iso G H f (me .fst) (me .snd))

{` The same with the categorical isomorphisms of GroupCat (module 686). `}
def gepi_cat_iso_mono_epi_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (CatIsIso (GroupCat .wild) G H f) (Product (IsMono (GroupCat .wild) G H f) (IsEpi (GroupCat .wild) G H f))
  ≔ compose_equiv (CatIsIso (GroupCat .wild) G H f) (IsGroupIso G H f)
      (Product (IsMono (GroupCat .wild) G H f) (IsEpi (GroupCat .wild) G H f))
      (iff_equiv (CatIsIso (GroupCat .wild) G H f) (IsGroupIso G H f)
        (cat_is_iso_prop (GroupCat .wild) G H f) (is_group_iso_prop G H f)
        (group_cat_is_iso_to_group_iso G H f) (group_iso_to_cat_is_iso G H f))
      (gepi_iso_mono_epi_equiv G H f)
