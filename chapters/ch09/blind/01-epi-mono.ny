{` Blind statements for chapter 9 (subgroups.tex), section "Epimorphisms, and an equivalent take on monomorphisms". `}
export "../../../src/508-stabilizer-subgroups"
export "../../../src/230-higher-images"
export "../../../src/110-truncated-map-levels"

{` Helper: logical equivalence of two types (used for every "if and only if"). `}
def BlindIff (A B : Type) : Type ≔ Product (A → B) (B → A)

{` lem:injmonosurjepiSet (1). f : B → C of sets is an injection iff for every set A and g, h : A → B,
   f g = f h implies g = h. `}
def blind_injmono_set : Type
  ≔ (B C : SetTypes) (f : B .fst → C .fst)
    → BlindIff (IsEmbedding (B .fst) (C .fst) f)
        ((A : SetTypes) (g h : A .fst → B .fst)
          → Id (A .fst → C .fst) (x ↦ f (g x)) (x ↦ f (h x)) → Id (A .fst → B .fst) g h)

{` lem:injmonosurjepiSet (2). f is a surjection iff for every set D and g, h : C → D, g f = h f implies g = h. `}
def blind_surjepi_set : Type
  ≔ (B C : SetTypes) (f : B .fst → C .fst)
    → BlindIff (Surjective (B .fst) (C .fst) f)
        ((D : SetTypes) (g h : C .fst → D .fst)
          → Id (B .fst → D .fst) (x ↦ g (f x)) (x ↦ h (f x)) → Id (C .fst → D .fst) g h)

{` def:monomorphism. f : Hom(G,H) is a monomorphism if for every group F postcomposition by f is an injection
   Hom(F,G) → Hom(F,H). (group_hom_compose F G H k f is f ∘ k.) `}
def BlindIsMono (G H : Group) (f : GroupHom G H) : Type
  ≔ (F : Group) → IsEmbedding (GroupHom F G) (GroupHom F H) (k ↦ group_hom_compose F G H k f)

{` def:epimorphism. f is an epimorphism if for every group I precomposition by f is an injection Hom(H,I) → Hom(G,I). `}
def BlindIsEpi (G H : Group) (f : GroupHom G H) : Type
  ≔ (I : Group) → IsEmbedding (GroupHom H I) (GroupHom G I) (k ↦ group_hom_compose G H I f k)

{` def:monomorphism: "the corresponding families of propositions" ismono, isepi : Hom(G,H) → Prop. `}
def blind_is_mono_prop : Type ≔ (G H : Group) (f : GroupHom G H) → isProp (BlindIsMono G H f)
def blind_is_epi_prop : Type ≔ (G H : Group) (f : GroupHom G H) → isProp (BlindIsEpi G H f)

{` def:monomorphism: proper monomorphism / epimorphism (not an isomorphism). `}
def BlindIsProperMono (G H : Group) (f : GroupHom G H) : Type ≔ Product (BlindIsMono G H f) (Not (IsGroupIso G H f))
def BlindIsProperEpi (G H : Group) (f : GroupHom G H) : Type ≔ Product (BlindIsEpi G H f) (Not (IsGroupIso G H f))

{` def:monomorphism: Mono(H) ≔ Σ_{G:Group} Σ_{i:Hom(G,H)} ismono(i) with the predicate of this chapter.
   (Elsewhere in these files Mono(G) is chapter 5's GroupMonos G, def:typeofmono, which the book declares
   to be the same thing via lem:eq-mono-cover.) `}
def BlindMonoType (H : Group) : Type ≔ Σ Group (G ↦ Σ (GroupHom G H) (i ↦ BlindIsMono G H i))

{` def:epimorphism: Epi(G) ≔ Σ_{H:Group} Σ_{f:Hom(G,H)} isepi(f). `}
def BlindEpi (G : Group) : Type ≔ Σ Group (H ↦ Σ (GroupHom G H) (f ↦ BlindIsEpi G H f))

{` exa:projections-epi. Both projections G1 × G2 → G_i are epimorphisms. `}
def blind_projections_epi : Type
  ≔ (G1 G2 : Group)
    → Product (BlindIsEpi (product_group G1 G2) G1 (product_group_proj1 G1 G2))
        (BlindIsEpi (product_group G1 G2) G2 (product_group_proj2 G1 G2))

{` xca:mono1st-epi2nd. Composites of monos are monos, of epis are epis; for f = f2 f1,
   f epi ⇒ f2 epi and f mono ⇒ f1 mono. `}
def blind_mono_compose : Type
  ≔ (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
    → BlindIsMono G H f → BlindIsMono H K g → BlindIsMono G K (group_hom_compose G H K f g)

def blind_epi_compose : Type
  ≔ (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
    → BlindIsEpi G H f → BlindIsEpi H K g → BlindIsEpi G K (group_hom_compose G H K f g)

def blind_epi_second : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → BlindIsEpi G0 G2 (group_hom_compose G0 G1 G2 f1 f2) → BlindIsEpi G1 G2 f2

def blind_mono_first : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → BlindIsMono G0 G2 (group_hom_compose G0 G1 G2 f1 f2) → BlindIsMono G0 G1 f1

{` lem:eq-mono-cover. (i) f mono ⇔ (ii) USym f injection ⇔ (iii) Bf÷ is a covering ⇔ Bf÷ 0-truncated. `}
def blind_eq_mono_cover : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Product (BlindIff (BlindIsMono G H f) (IsEmbedding (USym G) (USym H) (usym_hom G H f)))
        (Product (BlindIff (IsEmbedding (USym G) (USym H) (usym_hom G H f))
                     (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f)))
                 (BlindIff (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
                     (TruncatedMap (suc. (suc. zero.)) (BG G .carrier) (BG H .carrier) (hom_function G H f))))

{` lem:epi-surj. (1') f epi ⇔ (2') USym f surjection ⇔ (3') Bf÷ has connected fibers ⇔ Bf÷ 0-connected. `}
def blind_epi_surj : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Product (BlindIff (BlindIsEpi G H f) (Surjective (USym G) (USym H) (usym_hom G H f)))
        (Product (BlindIff (Surjective (USym G) (USym H) (usym_hom G H f))
                     ((w : BG H .carrier) → Connected (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w)))
                 (BlindIff ((w : BG H .carrier) → Connected (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w))
                     (NConnectedMap (suc. zero.) (BG G .carrier) (BG H .carrier) (hom_function G H f))))

{` Equalizers in the category of groups: i : Hom(H,G) is an equalizer of φ, ψ : Hom(G,W) if φ i = ψ i and every
   k : Hom(K,G) with φ k = ψ k factors uniquely as k = i k'. `}
def BlindIsEqualizer (G H W : Group) (i : GroupHom H G) (φ ψ : GroupHom G W) : Type
  ≔ Product (Id (GroupHom H W) (group_hom_compose H G W i φ) (group_hom_compose H G W i ψ))
      ((K : Group) (k : GroupHom K G)
        → Id (GroupHom K W) (group_hom_compose K G W k φ) (group_hom_compose K G W k ψ)
        → BookIsContr (Σ (GroupHom K H) (k' ↦ Id (GroupHom K G) (group_hom_compose K H G k' i) k)))

{` con:monos-are-equalizers. For a monomorphism i : H → G there are a group W and φ, ψ : Hom(G,W)
   such that i is an equalizer of φ and ψ. `}
def blind_monos_are_equalizers : Type
  ≔ (G H : Group) (i : GroupHom H G) → BlindIsMono H G i
    → Σ Group (W ↦ Σ (GroupHom G W) (φ ↦ Σ (GroupHom G W) (ψ ↦ BlindIsEqualizer G H W i φ ψ)))

{` lem:epimonoiso. f is an isomorphism iff it is both a monomorphism and an epimorphism. `}
def blind_epimonoiso : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → BlindIff (IsGroupIso G H f) (Product (BlindIsMono G H f) (BlindIsEpi G H f))
