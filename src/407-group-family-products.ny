export "404-group-examples"

{` ex:bigproductofgroups and xca:bigproductfunext (i): products of finite
   families of groups. The index type S is finite (IsFinite S, hence a set);
   connectedness of the product uses finite choice (module 34). `}
def connected_pi_finite (S : Type) (hS : IsFinite S) (B : S → Type) (hB : (s : S) → Connected (B s))
  : Connected ((s : S) → B s)
  ≔ (finite_choice S hS B (s ↦ hB s .fst),
     f g ↦ mere_rec ((s : S) → Id (B s) (f s) (g s)) (Mere (Id ((s : S) → B s) f g))
       (mere_isprop (Id ((s : S) → B s) f g))
       (h ↦ mere (Id ((s : S) → B s) f g) (funext S B f g h))
       (finite_choice S hS (s ↦ Id (B s) (f s) (g s)) (s ↦ hB s .snd (f s) (g s))))

def groupoid_pi (S : Type) (B : S → Type) (hB : (s : S) → isGroupoid (B s)) : isGroupoid ((s : S) → B s)
  ≔ hlevel_to_groupoid ((s : S) → B s)
      (hlevel_pi (suc. (suc. (suc. zero.))) S B (s ↦ groupoid_to_hlevel (B s) (hB s)))

{` Π_{s:S} G(s) ≔ mkgroup (Π_{s:S} BG(s), s ↦ sh_{G(s)}). `}
def family_product_group (S : Type) (hS : IsFinite S) (G : S → Group) : Group
  ≔ mkgroup ((s : S) → BG (G s) .carrier, s ↦ shape (G s),
      connected_pi_finite S hS (s ↦ BG (G s) .carrier) (s ↦ bg_connected (G s)),
      groupoid_pi S (s ↦ BG (G s) .carrier) (s ↦ bg_groupoid (G s)))

{` Function extensionality: ptw (= happly) is an equivalence
   USym(Π_s G(s)) ≃ Π_s USym G(s). `}
def family_product_usym_equiv (S : Type) (hS : IsFinite S) (G : S → Group)
  : Equiv (USym (family_product_group S hS G)) ((s : S) → USym (G s))
  ≔ function_extensionality S (s ↦ BG (G s) .carrier) (s ↦ shape (G s)) (s ↦ shape (G s))

{` The power G^S of a group (constant family), used for Σ_2^E in the sign section. `}
def power_group (S : Type) (hS : IsFinite S) (G : Group) : Group ≔ family_product_group S hS (_ ↦ G)

def power_group_usym_equiv (S : Type) (hS : IsFinite S) (G : Group)
  : Equiv (USym (power_group S hS G)) (S → USym G)
  ≔ family_product_usym_equiv S hS (_ ↦ G)
