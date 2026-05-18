import Init.Data.Int.Lemmas
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Quotient
set_option linter.style.docString false
set_option linter.style.multiGoal false
--set_option diagnostics true
/-

    An exercise in creating a custom implementation of groups
    to strengthen my knowledge of and intuition for groups (and Lean).
    From around December 2025.

    -- Will Sweet

-/
universe u
/-


    Prologue : Permutations.


-/
structure Permutation (T : Type*) where
    map : T -> T
    inv : T -> T
    left_inv : inv ∘ map = id
    right_inv : map ∘ inv = id
instance {T : Type*} : FunLike (Permutation T) T T where
    coe f := f.map
    coe_injective' f g h := by
        simp at h
        have h' : f.inv = g.inv := by
            calc
                f.inv = f.inv ∘ id := by rfl
                _ = f.inv ∘ (g.map ∘ g.inv) := by rw [Permutation.right_inv]
                _ = (f.inv ∘ g.map) ∘ g.inv := by rfl
                _ = (f.inv ∘ f.map) ∘ g.inv := by rw [h]
                _ = id ∘ g.inv := by rw [Permutation.left_inv]
                _ = g.inv := by rfl
        rcases f with ⟨f_map, f_inv, f_left, f_right⟩
        rcases g with ⟨g_map, g_inv, g_left, g_right⟩
        have h0 : f_map = g_map := by subst h' h ; simp_all only
        have h1 : f_inv = g_inv := by subst h' h ; simp_all only
        subst h' h ; simp_all only
@[ext]
theorem Permutation.ext {T : Type*} {f g : Permutation T}
    (h : ∀ x, f x = g x) : f = g := by
        apply DFunLike.ext
        exact h

namespace Permutation

variable {T : Type*}

def moves (f : Permutation T) (x : T) := f x ≠ x

def fixes (f : Permutation T) (x : T) := f x = x

/--
    0.1. The composition of two permutations is a permutation.
-/
def compose (σ : Permutation T) (τ : Permutation T) : Permutation T where
    map := σ ∘ τ
    inv := τ.inv ∘ σ.inv
    left_inv := by
        change τ.inv ∘ (σ.inv ∘ σ.map) ∘ τ.map = id
        rw [σ.left_inv]
        simp
        apply τ.left_inv
    right_inv := by
        change σ.map ∘ (τ.map ∘ τ.inv) ∘ σ.inv = id
        rw [τ.right_inv]
        simp
        apply σ.right_inv
/--
    0.2. The identity permutation is a permutation.
-/
def identity : Permutation T where
    map := id
    inv := id
    left_inv := rfl
    right_inv := rfl
/--
    0.3. A permutation has an inverse permutation.
-/
def inverse (f : Permutation T) : Permutation T where
    map := f.inv
    inv := f.map
    left_inv := f.right_inv
    right_inv := f.left_inv
instance : Inv (Permutation T) where
    inv := inverse
end Permutation
/-


    Section 1 : Groups.


-/
class Group (G : Type*) where
    mul : G → G → G
    one : G
    inv : G → G
    mul_assoc : ∀ a b c : G, mul a (mul b c) = mul (mul a b) c
    one_mul : ∀ a : G, mul one a = a
    inv_left : ∀ a : G, mul (inv a) a = one
class AbGroup (G : Type*) extends Group G where
    mul_comm : ∀ a b : G, mul a b = mul b a

namespace Group

instance {G : Type*} [Group G] : Mul G where
    mul := mul
instance {G : Type*} [Group G] : Inv G where
    inv := inv
instance {G : Type*} [Group G] : One G where
    one := one
instance {G : Type*} [Group G] : Inhabited G := ⟨1⟩
theorem assoc {G : Type*} [Group G] (a b c : G) : a * (b * c) = (a * b) * c := by
    change mul a (mul b c) = mul (mul a b) c
    apply mul_assoc
theorem left_id {G : Type*} [Group G] : ∀ a : G, 1 * a = a := by
    change ∀ a : G, mul one a = a
    apply one_mul
theorem left_inv {G : Type*} [Group G] : ∀ a : G, a⁻¹ * a = 1 := by
    change ∀ a : G, mul (inv a) a = one
    apply inv_left
theorem comm {A : Type*} [AbGroup A] : ∀ a b : A, a * b = b * a := by
    change ∀ a b : A, mul a b = mul b a
    apply AbGroup.mul_comm
variable {G : Type*} [Group G]
/--
    1.1. If a * a = a, then a = 1.
-/
theorem unique_self_id : ∀ a : G, a * a = a → a = 1 := by
    intro a ha
    calc
        a = a * a := by rw [ha]
        _ = 1 * a := by rw [left_id, ha]
        _ = a⁻¹ * a * a := by rw [left_inv]
        _ = a⁻¹ * (a * a) := by rw [assoc]
        _ = a⁻¹ * a := by rw [ha]
        _ = 1 := by rw [left_inv]
/--
    1.2. a * a⁻¹ = 1.
-/
theorem right_inv : ∀ a : G, a * a⁻¹ = 1 := by
    intro a
    let b := a⁻¹
    change mul a b = one
    have h : (a * b) * (a * b) = (a * b) := by
        calc
            (a * b) * (a * b) = a * (b * (a * b)) := by rw [<- assoc]
            _ = a * ((b * a) * b) := by rw [<- assoc]
            _ = a * (1 * b) := by rw [left_inv]
            _ = a * b := by rw [left_id]
    apply unique_self_id (a * b)
    exact h
/--
    1.3. a * 1 = a.
-/
theorem right_id : ∀ a : G, a * 1 = a := by
    intro a
    calc
        a * 1 = a * (a⁻¹ * a) := by rw [left_inv]
        _ = a * a⁻¹ * a := by rw [assoc]
        _ = a := by rw [right_inv, left_id]
/--
    1.4. (a⁻¹)⁻¹ = a.
-/
theorem involuted_inv : ∀ a : G, (a⁻¹)⁻¹ = a := by
    intro a
    calc
        a⁻¹⁻¹ = a⁻¹⁻¹ * a⁻¹ * a := by rw [<- assoc, left_inv, right_id]
        _ = a := by rw [left_inv, left_id]
/--
    1.6. Injectivity of the inverse map.
-/
theorem injective_inv : ∀ a b : G, a = b ↔ a⁻¹ = b⁻¹ := by
    intro a b
    apply Iff.intro
    case mp =>
        intro heq
        calc
            a⁻¹ = a⁻¹ * 1 := by rw [right_id]
            _ = a⁻¹ * b * b⁻¹ := by rw [<- right_inv b, assoc]
            _ = a⁻¹ * a * b⁻¹ := by rw [heq]
            _ = b⁻¹ := by rw [left_inv, left_id]
    case mpr =>
        intro heq
        calc
            a = a * 1 := by rw [right_id]
            _ = a * b⁻¹ * b := by rw [<- left_inv b, assoc]
            _ = a * a⁻¹ * b := by rw [heq]
            _ = b := by rw [right_inv, left_id]
/--
    1.7. Left cancellation law.
-/
theorem left_cancel : ∀ a b c : G, a * b = a * c → b = c := by
    intro a b c ha
    calc
        b = 1 * b := by rw [left_id]
        _ = (a⁻¹ * a) * b := by rw [<- left_inv]
        _ = a⁻¹ * (a * b) := by rw [assoc]
        _ = a⁻¹ * (a * c) := by rw [ha]
        _ = (a⁻¹ * a) * c := by rw [assoc]
        _ = 1 * c := by rw [left_inv]
        _ = c := by rw [left_id]
/--
    1.8. Right cancellation law.
-/
theorem right_cancel : ∀ a b c : G, b * a = c * a → b = c := by
    intro a b c ha
    calc
        b = b * 1 := by rw [right_id]
        _ = b * (a * a⁻¹) := by rw [<- right_inv]
        _ = (b * a) * a⁻¹ := by rw [assoc]
        _ = (c * a) * a⁻¹ := by rw [ha]
        _ = c * (a * a⁻¹) := by rw [assoc]
        _ = c * 1 := by rw [right_inv]
        _ = c := by rw [right_id]
/--
    1.9. (ab)⁻¹ = b⁻¹a⁻¹
-/
theorem inverted_inv : ∀ a b : G, b⁻¹ * a⁻¹ = (a * b)⁻¹ := by
    intro a b
    have mirror : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
        calc
            (a * b) * (b⁻¹ * a⁻¹) = a * (b * b⁻¹) * a⁻¹ := by rw [assoc, assoc]
            _ = a * 1 * a⁻¹ := by rw [right_inv]
            _ = a * a⁻¹ := by rw [right_id]
            _ = 1 := by rw [right_inv]
    have inverse : (a * b) * (a * b)⁻¹ = 1 := by rw [right_inv]
    rw [<- inverse] at mirror
    apply left_cancel (a * b) (b⁻¹ * a⁻¹) (a * b)⁻¹ mirror
/--
    1.10. ab = ba ↔ b⁻¹ab = a
-/
theorem conj_fixes_iff_commutes : ∀ a b : G, a * b = b * a ↔ b⁻¹ * a * b = a := by
        intro a b
        apply Iff.intro
        case mp =>
            intro ha
            calc
                b⁻¹ * a * b = b⁻¹ * (a * b) := by rw [assoc]
                _ = b⁻¹ * (b * a) := by rw [ha]
                _ = (b⁻¹ * b) * a := by rw [assoc]
                _ = 1 * a := by rw [left_inv]
                _ = a := by rw [left_id]
        case mpr =>
            intro ha
            rw [<- ha, assoc, assoc, right_inv, left_id, ha]
/--
    1.11. ab = ba ↔ a⁻¹b⁻¹ab = e
-/
theorem commutator_id_iff_commutes :
    ∀ a b : G, a * b = b * a ↔ a⁻¹ * b⁻¹ * a * b = 1 := by
        intro a b
        apply Iff.intro
        case mp =>
            intro ha
            calc
                a⁻¹ * b⁻¹ * a * b = a⁻¹ * b⁻¹ * (b * a) := by rw [<- assoc, ha]
                _ = a⁻¹ * (b⁻¹ * b) * a := by rw [assoc, assoc]
                _ = a⁻¹ * 1 * a := by rw [left_inv]
                _ = a⁻¹ * a := by rw [right_id]
                _ = 1 := by rw [left_inv]
        case mpr =>
            intro ha
            have : b⁻¹ * a * b = a := by
                calc
                    b⁻¹ * a * b = 1 * b⁻¹ * a * b := by rw [left_id]
                    _ = (a * a⁻¹) * b⁻¹ * a * b := by rw [<- right_inv]
                    _ = a * (a⁻¹ * b⁻¹ * a * b) := by repeat rw [assoc]
                    _ = a * 1 := by rw [ha]
                    _ = a := by rw [right_id]
            rw [<- this, assoc, assoc, right_inv, left_id, this]
/--
    1.12. If ab = 1, then b = a⁻¹.
-/
theorem inv_is_inv (a b : G) : a * b = 1 -> b = a⁻¹ := by
    intro h
    apply left_cancel a b a⁻¹
    rw [h, right_inv]
/--
    1.13. The identity is its own inverse.
-/
theorem inv_one : (1 : G)⁻¹ = 1 := by
    have h : (1 : G) * 1 = 1 := by
        rw [left_id]
    have h' : (1 : G) = 1⁻¹ := by
        apply inv_is_inv
        exact h
    apply Eq.symm ; exact h'
/--
    1.14. Conjugate form.
-/
theorem conj_of_conj (a x y : G) : y = a * x * a⁻¹ -> a⁻¹ * y * a = x := by
    intro hy
    subst hy
    calc
        a⁻¹ * (a * x * a⁻¹) * a = (a⁻¹ * a) * x * (a⁻¹ * a) := by
            repeat rw [assoc]
        _ = x := by rw [left_inv, left_id, right_id]
/--
    1.15. Direct product construction.
-/
instance DirectProduct (A B : Type u) [Group A] [Group B] : Group (A × B) where
    mul := fun ⟨a, b⟩ => fun ⟨x, y⟩ => ⟨a * x, b * y⟩
    one := ⟨1, 1⟩
    inv := fun ⟨a, x⟩ => ⟨a⁻¹, x⁻¹⟩
    mul_assoc := by
        intro a b c
        simp_all
        split_ands
        apply assoc ; apply assoc
    one_mul := by
        intro a
        simp_all
        rw [left_id, left_id]
    inv_left := by
        intro a
        simp_all
        split_ands
        apply left_inv ; apply left_inv
/--
    1.16. The symmetric group on a finite set.
-/
instance Sym (T : Type*) : Group (Permutation T) where
    mul := Permutation.compose
    one := Permutation.identity
    inv := Permutation.inverse
    mul_assoc := by intro _ _ _ ; rfl
    one_mul := by intro _ ; rfl
    inv_left := by
        intro f ; ext g
        change (f.inv ∘ f.map) g = id g
        rw [f.left_inv]
/-


    Section 2 : Subgroups and normal subgroups.


-/
structure Subgroup (G : Type*) [Group G] where
    carrier : Set G
    has_one : (1 : G) ∈ carrier
    is_closed {a b : G} : a ∈ carrier → b ∈ carrier → Group.mul a b ∈ carrier
    has_inv {a : G} : a ∈ carrier → Group.inv a ∈ carrier
structure NormalSubgroup (G : Type*) [Group G] extends Subgroup G where
    normal : ∀ a ∈ carrier, ∀ x : G, x * a * x⁻¹ ∈ carrier
instance (G : Type*) [Group G] : SetLike (Subgroup G) G where
    coe H := H.carrier
    coe_injective' H1 H2 h := by
        cases H1
        cases H2
        congr
@[ext]
theorem Subgroup.ext {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := by
        apply SetLike.ext
        exact h
instance (G : Type*) [Group G] : SetLike (NormalSubgroup G) G where
    coe H := H.carrier
    coe_injective' H1 H2 h := by
        rcases H1 with ⟨H, fh⟩
        rcases H2 with ⟨K, fk⟩
        congr
        apply Subgroup.ext
        intro x
        simp_all only
        simp_all only [implies_true]
        apply Iff.intro
        case e_toSubgroup.h.mp =>
            intro xh
            change x ∈ H.carrier at xh
            change x ∈ K.carrier
            rw [h] at xh
            exact xh
        case e_toSubgroup.h.mpr =>
            intro xk
            change x ∈ H.carrier
            change x ∈ K.carrier at xk
            rw [<- h] at xk
            exact xk
@[ext]
theorem NormalSubgroup.ext {G : Type*} [Group G] {H K : NormalSubgroup G}
    (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := by
        apply SetLike.ext
        exact h
/--
    Subgroup type.
-/
def SubgroupType (G : Type u) [Group G] (H : Subgroup G) : Type u :=
    {x : G // x ∈ H}
instance (G : Type u) [Group G] (H : Subgroup G) : Group (SubgroupType G H) where
    mul := fun a b => ⟨a.val * b.val, H.is_closed a.property b.property⟩
    one := ⟨1, H.has_one⟩
    inv := fun a => ⟨a.val⁻¹, H.has_inv a.property⟩
    mul_assoc := by
        intro a b c
        apply Subtype.ext
        exact Group.assoc _ _ _
    one_mul := by
        intro a
        apply Subtype.ext
        exact Group.left_id _
    inv_left := by
        intro a
        apply Subtype.ext
        exact Group.left_inv _
instance (G : Type u) [Group G] [Finite G] (H : Subgroup G) :
    Finite (SubgroupType G H) :=
        Subtype.finite
/--
    Normal subgroup type.
-/
def NormalType (G : Type u) [Group G] (H : NormalSubgroup G) : Type u :=
    {x : G // x ∈ H}
namespace Subgroup
/--
    2.1. Any group is a subgroup of itself.
-/
instance Improper (G : Type*) [Group G] : Subgroup G where
    carrier := Set.univ
    has_one := by simp_all only [Set.mem_univ]
    is_closed := by intro _ _ _ _ ; simp_all only [Set.mem_univ]
    has_inv := by intro _ _ ; simp_all only [Set.mem_univ]
/--
    2.2. The trivial group is a subgroup of any group.
-/
instance Trivial (G : Type*) [Group G] : Subgroup G where
    carrier := {1}
    has_one := rfl
    is_closed := by
        intro _ _ ha hb
        simp at *
        rw [ha, hb]
        calc
            Group.mul (1 : G) 1 = 1 * 1 := by rfl
            _ = 1 := by rw [Group.left_id]
    has_inv := by
        intro _ _
        simp_all only [Set.mem_singleton_iff]
        apply Group.inv_one
/--
    2.3. The set of elements commuting with all elements in G is a normal subgroup of G.
-/
instance Center (G : Type*) [Group G] : NormalSubgroup G where
    carrier := fun a : G => ∀ (b : G), a * b = b * a
    has_one := by
        intro b
        rw [Group.left_id, Group.right_id]
    is_closed := by
        intro a b ha hb c
        specialize ha c
        specialize hb c
        change a * b * c = c * (a * b)
        calc
            a * b * c = a * (b * c) := by rw [Group.assoc]
            _ = a * (c * b) := by rw [hb]
            _ = (a * c) * b := by rw [Group.assoc]
            _ = (c * a) * b := by rw [ha]
            _ = c * (a * b) := by rw [Group.assoc]
    has_inv := by
        intro a ha b
        change a⁻¹ * b = b * a⁻¹
        apply Group.left_cancel a
        have h : ∀ a b : G, a * b = b * a -> b⁻¹ * a * b = a := by
            intro a b
            apply (Group.conj_fixes_iff_commutes a b).mp
        specialize ha b
        calc
            a * (a⁻¹ * b) = (a * a⁻¹) * b := by rw [Group.assoc]
            _ = b := by rw [Group.right_inv, Group.left_id]
            _ = a⁻¹ * b * a := by
                have h1 : b * a = a * b := by simp_all
                specialize h b a h1
                rw [h]
        rw [Group.assoc, ha]
        calc
            a⁻¹ * b * a = a⁻¹ * (b * a) := by rw [Group.assoc]
            _ = a⁻¹ * a * b := by rw [<- ha, Group.assoc]
            _ = b := by rw [Group.left_inv, Group.left_id]
        rw [<- Group.assoc, Group.right_inv, Group.right_id]
    normal := by
        intro a ha x b
        have : a * b = b * a := by specialize ha b ; exact ha
        have h : a * x = x * a := by specialize ha x ; exact ha
        apply Eq.symm
        rw [<- h]
        have h1 : b * (a * x * x⁻¹) = b * a := by
            calc
                b * (a * x * x⁻¹) = b * a * (x * x⁻¹) := by repeat rw [assoc]
                _ = b * a := by rw [right_inv, right_id]
        have h2 : a * x * x⁻¹ * b = a * b := by
            calc
                 a * x * x⁻¹ * b = a * (x * x⁻¹) * b  := by rw [assoc]
                 _ = a * b := by rw [right_inv, right_id]
        rw [h1, h2, this]
/--
    2.4. The intersection of two subgroups is a subgroup.
-/
instance Intersection (G : Type u) [Group G] (H K : Subgroup G) : Subgroup G where
    carrier := fun a => a ∈ H ∧ a ∈ K
    has_one := ⟨H.has_one, K.has_one⟩
    is_closed := by
        intro a b ha hb
        split_ands
        apply H.is_closed ; apply ha.left ; apply hb.left
        apply K.is_closed ; apply ha.right ; apply hb.right
    has_inv := by
        intro a ha
        change a⁻¹ ∈ H ∧ a⁻¹ ∈ K
        split_ands
        apply H.has_inv ; apply ha.left
        apply K.has_inv ; apply ha.right
/--
    2.5. Construction of an arbitrary subgroup of an abelian group as a normal subgroup.
-/
instance AbelianNormal {A : Type*} [AbGroup A] (H : Subgroup A) : NormalSubgroup A where
    carrier := H.carrier
    has_one := H.has_one
    is_closed := H.is_closed
    has_inv := H.has_inv
    normal := by
        intro a ha x
        have : a * x = x * a := by
            apply AbGroup.mul_comm
        have : a = x * a * x⁻¹ := by
            rw [<- this, <- Group.assoc, Group.right_inv, Group.right_id]
        rw [<- this]
        exact ha
/--
    2.6. Normalizer of a subset S of a group G is a subgroup of G.
-/
def ConjSet {G : Type u} [Group G] (a : G) (S : Set G) : Set G :=
    fun y => ∃ x ∈ S, y = a * x * a⁻¹
instance Normalizer (G : Type u) [Group G] (S : Set G) : Subgroup G where
    carrier := fun a => ConjSet a S = S
    has_one := by
        change ConjSet 1 S = S
        unfold ConjSet
        ext a
        apply Iff.intro
        case h.mp =>
            intro ha
            choose x hx using ha
            rw [left_id, inv_one, right_id] at hx
            grind
        case h.mpr =>
            intro ha
            use a
            split_ands
            case h.refine_1 => exact ha
            case h.refine_2 =>
                apply Eq.symm
                calc
                    1 * a * 1⁻¹ = a * 1⁻¹ := by rw [left_id]
                    _ = a * 1 := by rw [inv_one]
                    _ = a := by rw [right_id]
    is_closed := by
        intro a b ha hb
        change ConjSet a S = S at ha
        change ConjSet b S = S at hb
        change ConjSet (a * b) S = S
        unfold ConjSet at *
        rw [<- Group.inverted_inv]
        ext n
        apply Iff.intro
        case h.mp =>
            intro ha
            choose x hx using ha
            rw [Group.assoc] at hx
            have : n = a * (b * x * b⁻¹) * a⁻¹ := by
                calc
                    n = a * b * x * b⁻¹ * a⁻¹ := by rw [hx.2]
                    _ = a * (b * x * b⁻¹) * a⁻¹ := by repeat rw [Group.assoc]
            rw [<- ha]
            change ∃ x ∈ S, n = a * x * a⁻¹
            use b * x * b⁻¹
            split_ands
            case h.refine_1 =>
                rw [<- hb]
                use x
                grind
            case h.refine_2 =>
                exact this
        case h.mpr =>
            intro hn
            change ∃ x ∈ S, n = a * b * x * (b⁻¹ * a⁻¹)
            use b⁻¹ * a⁻¹ * n * a * b
            split_ands
            case h.refine_1 =>
                rw [<- ha, <- hb] at hn
                choose y hx using hn
                choose hxy hy using hx
                choose x hx using hxy
                rw [hx.2] at hy
                rw [hy]
                have : b⁻¹ * a⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * a * b = x := by
                    calc
                        b⁻¹ * a⁻¹ * (a * (b * x * b⁻¹) * a⁻¹) * a * b =
                        b⁻¹ * (a⁻¹ * a) * (b * x * b⁻¹) * (a⁻¹ * a) * b := by
                            repeat rw [Group.assoc]
                        _ = b⁻¹ * (b * x * b⁻¹) * b := by
                            rw [Group.left_inv, Group.right_id, Group.right_id]
                        _ = (b⁻¹ * b) * x * (b⁻¹ * b) := by
                            repeat rw [Group.assoc]
                        _ = x := by
                            rw [Group.left_inv, Group.left_id, Group.right_id]
                rw [this]
                exact hx.1
            case h.refine_2 =>
                apply Eq.symm
                calc
                    a * b * (b⁻¹ * a⁻¹ * n * a * b) * (b⁻¹ * a⁻¹) =
                    a * (b * b⁻¹) * a⁻¹ * n * a * (b * b⁻¹) * a⁻¹ := by
                        repeat rw [Group.assoc]
                    _ = a * a⁻¹ * n * a * a⁻¹ := by
                        rw [Group.right_inv, Group.right_id, Group.right_id]
                    _ = n := by rw [
                        Group.right_inv,
                        Group.left_id,
                        <- Group.assoc,
                        Group.right_inv,
                        Group.right_id
                    ]
    has_inv := by
        intro a ha
        change ConjSet a S = S at ha
        change ConjSet a⁻¹ S = S
        unfold ConjSet at *
        ext z
        have h' (m : G) : a⁻¹ * (a * m * a⁻¹) * a = (a⁻¹ * a) * m * (a⁻¹ * a) := by
            repeat rw [Group.assoc]
        apply Iff.intro
        case h.mp =>
            intro hz
            change ∃ x ∈ S, z = a⁻¹ * x * (a⁻¹)⁻¹ at hz
            choose q hq using hz
            rw [<- ha]
            change ∃ x ∈ S, z = a * x * a⁻¹
            use a⁻¹ * z * a
            rw [hq.2]
            rw [Group.involuted_inv]
            split_ands
            case h.refine_1 =>
                obtain ⟨left, right⟩ := hq
                subst right
                rw [<- ha] at left
                choose n hn using left
                rw [hn.2]
                rw [<- ha] at hn
                choose k xk using hn.1
                rw [h', Group.left_inv, Group.left_id, Group.right_id] at *
                rw [xk.2]
                rw [h', Group.left_id, Group.right_id]
                exact xk.1
            case h.refine_2 =>
                apply Eq.symm
                calc
                    a * (a⁻¹ * (a⁻¹ * q * a) * a) * a⁻¹ =
                    a * a⁻¹ * a⁻¹ * q * a * (a * a⁻¹) := by
                        repeat rw [Group.assoc]
                    _ = a⁻¹ * q * a := by
                        rw [Group.right_inv, Group.left_id, Group.right_id]
        case h.mpr =>
            intro hz
            change ∃ x ∈ S, z = a⁻¹ * x * (a⁻¹)⁻¹
            rw [Group.involuted_inv]
            rw [<- ha] at hz
            choose y hy using hz
            use a * z * a⁻¹
            have hz : a⁻¹ * z * a = y := by
                rw [Group.conj_of_conj]
                exact hy.2
            apply And.symm
            split_ands
            case h.a.refine_1 =>
                apply Eq.symm
                specialize h' z
                calc
                    a⁻¹ * (a * z * a⁻¹) * a = a⁻¹ * a * z * (a⁻¹ * a) := by rw [h']
                    _ = z := by rw [Group.left_inv, Group.left_id, Group.right_id]
            case h.a.refine_2 =>
                have hy1' : y ∈ S := by exact hy.1
                rw [<- ha] at hy
                obtain ⟨hy1, hy2⟩ := hy
                rw [<- ha]
                choose k hk using hy1
                have hky : a⁻¹ * y * a = k := by
                    rw [Group.conj_of_conj]
                    exact hk.2
                use z
                apply And.symm
                split_ands
                rfl
                rw [<- ha]
                use y
/--
    2.7. Centralizer of a subset S of a group G is a subgroup of G.
-/
instance Centralizer (G : Type u) [Group G] (S : Set G) : Subgroup G where
    carrier := fun a => ∀ x ∈ S, a * x = x * a
    has_one := by
        intro _ _
        rw [Group.left_id, Group.right_id]
    is_closed := by
        intro a b ha hb x hx
        change a * b * x = x * (a * b)
        specialize ha x hx
        specialize hb x hx
        calc
            a * b * x = a * (b * x) := by rw [Group.assoc]
            _ = a * (x * b) := by rw [hb]
            _ = (a * x) * b := by rw [Group.assoc]
            _ = (x * a) * b := by rw [ha]
            _ = x * (a * b) := by rw [Group.assoc]
    has_inv := by
        intro a ha x hx
        change a⁻¹ * x = x * a⁻¹
        apply Group.left_cancel a
        specialize ha x hx
        rw [
            Group.assoc,
            Group.assoc,
            Group.right_inv,
            Group.left_id,
            ha,
            <- Group.assoc,
            Group.right_inv,
            Group.right_id
        ]
/--
    2.8. A subgroup of a subgroup of G is a subgroup of G.
-/
instance Transitive
    (G : Type u) [Group G] (H : Subgroup G) (K : Subgroup (SubgroupType G H)) :
        Subgroup G where
            carrier := fun k => ∃ (h : k ∈ H), ⟨k, h⟩ ∈ K
            has_one := by
                use H.has_one
                apply K.has_one
            is_closed := by
                intro a b ha hb
                change ∃ (h : (a * b) ∈ H), ⟨a * b, h⟩ ∈ K
                obtain ⟨ha, hax⟩ := ha
                obtain ⟨hb, hbx⟩ := hb
                have hab : a * b ∈ H := H.is_closed ha hb
                use hab
                have hK := K.is_closed hax hbx
                convert hK
            has_inv := by
                intro a ha
                change ∃ (h : a⁻¹ ∈ H), ⟨a⁻¹, h⟩ ∈ K
                obtain ⟨ha, hax⟩ := ha
                have ha' : a⁻¹ ∈ H := H.has_inv ha
                use ha'
                have hK := K.has_inv hax
                convert hK
/--
    2.9. The subset product of a subgroup and normal subgroup of G is a subgroup of G.
-/
instance DiamondOne
    (G : Type u) [Group G] (H : Subgroup G) (K : NormalSubgroup G) :
        Subgroup G where
            carrier := fun a => ∃ h ∈ H, ∃ k ∈ K, a = h * k
            has_one := by
                use 1
                split_ands
                apply H.has_one
                use 1
                split_ands
                apply K.has_one
                rw [Group.left_id]
            is_closed := by
                intro a b ha hb
                change ∃ h ∈ H, ∃ k ∈ K, a * b = h * k
                obtain ⟨h, ⟨hh, ⟨k, ⟨hk, hka⟩⟩⟩⟩ := ha
                obtain ⟨h', ⟨hh', ⟨k', ⟨hk', hkb⟩⟩⟩⟩ := hb
                use (h * h')
                split_ands
                apply H.is_closed
                apply hh ; apply hh'
                use (h'⁻¹ * k * h') * (h'⁻¹ * (h' * k' * h'⁻¹) * h')
                split_ands
                apply K.is_closed
                have : h'⁻¹ * k * (h'⁻¹)⁻¹ ∈ K.carrier := by
                    apply K.normal ; apply hk
                rw [Group.involuted_inv] at this
                exact this
                have : h' * k' * h'⁻¹ ∈ K.carrier := by
                    apply K.normal ; exact hk'
                have : h'⁻¹ * (h' * k' * h'⁻¹) * (h'⁻¹)⁻¹ ∈ K.carrier := by
                    apply K.normal ; apply this
                rw [Group.involuted_inv] at this
                exact this
                rw [hka, hkb]
                apply Eq.symm
                calc
                    h * h' * (h'⁻¹ * k * h' * (h'⁻¹ * (h' * k' * h'⁻¹) * h')) =
                    h * (h' * h'⁻¹) * k * h' * (h'⁻¹ * h') * k' * (h'⁻¹ * h') := by
                        repeat rw [Group.assoc]
                    _ = h * k * (h' * k') := by
                        rw [
                            Group.right_inv,
                            Group.left_inv,
                            Group.right_id,
                            Group.right_id,
                            Group.right_id,
                            Group.assoc
                        ]
            has_inv := by
                intro a ha
                obtain ⟨h, ⟨hh, ⟨k, ⟨hk, hka⟩⟩⟩⟩ := ha
                change ∃ h ∈ H, ∃ k ∈ K, a⁻¹ = h * k
                rw [hka, <- Group.inverted_inv]
                use h⁻¹
                split_ands
                apply H.has_inv ; apply hh
                use (h * k⁻¹ * h⁻¹)
                split_ands
                apply K.normal
                apply K.has_inv
                apply hk
                apply Eq.symm
                calc
                    h⁻¹ * (h * k⁻¹ * h⁻¹) = (h⁻¹ * h) * k⁻¹ * h⁻¹ := by
                        repeat rw [Group.assoc]
                    _ = k⁻¹ * h⁻¹ := by
                        rw [Group.left_inv, Group.left_id]
end Subgroup
/-


    Section 3 : Group homomorphisms and isomorphisms.


-/
structure GroupHom (G H : Type*) [Group G] [Group H] where
    map : G -> H
    map_mul' : ∀ a b : G, map (a * b) = map a * map b
structure GroupIso (G H : Type*) [Group G] [Group H] extends GroupHom G H where
    inv : H -> G
    left_inv' : inv ∘ map = id
    right_inv' : map ∘ inv = id
instance (G H : Type*) [Group G] [Group H] : FunLike (GroupHom G H) G H where
    coe f := f.map
    coe_injective' f g h := by
        cases f; cases g; congr
instance (G H : Type*) [Group G] [Group H] : FunLike (GroupIso G H) G H where
    coe f := f.map
    coe_injective' f g h := by
        simp at h
        have h' : f.inv = g.inv := by
            calc
                f.inv = f.inv ∘ id := by rfl
                _ = f.inv ∘ (g.map ∘ g.inv) := by rw [GroupIso.right_inv']
                _ = (f.inv ∘ g.map) ∘ g.inv := by rfl
                _ = g.inv := by rw [<- h, GroupIso.left_inv'] ; rfl
        rcases f with ⟨⟨f_map, f_mul⟩, f_inv, f_left, f_right⟩
        rcases g with ⟨⟨g_map, g_mul⟩, g_inv, g_left, g_right⟩
        have h0 : f_map = g_map := by subst h' h ; simp_all only
        have h1 : f_inv = g_inv := by
            calc
                f_inv = f_inv ∘ id := by rfl
                _ = f_inv ∘ (g_map ∘ g_inv) := by rw [g_right]
                _ = (f_inv ∘ g_map) ∘ g_inv := by rfl
                _ = (f_inv ∘ f_map) ∘ g_inv := by rw [<- h0]
                _ = g_inv := by rw [f_left] ; rfl
        subst h' h
        simp_all only
@[ext]
theorem GroupHom.ext {G H : Type*} [Group G] [Group H] {f g : GroupHom G H}
    (h : ∀ x, f x = g x) : f = g := by
        apply DFunLike.ext
        exact h
@[ext]
theorem GroupIso.ext {G H : Type*} [Group G] [Group H] {f g : GroupIso G H}
    (h : ∀ x, f x = g x) : f = g := by
        apply DFunLike.ext
        exact h
namespace GroupHom
variable {G H K : Type*} [Group G] [Group H] [Group K]
/--
    3.1. Homomorphisms preserve multiplication.
-/
theorem map_mul (G H : Type*) [Group G] [Group H] (f : GroupHom G H) :
    ∀ a b : G, f (a * b) = f a * f b := by
        intro a b
        change f.map (a * b) = f.map a * f.map b
        rw [map_mul']
theorem iso_mul (G H : Type*) [Group G] [Group H] (f : GroupIso G H) :
    ∀ a b : G, f (a * b) = f a * f b := by
        intro a b
        change f.map (a * b) = f.map a * f.map b
        rw [map_mul']
/--
    3.2. Homomorphisms preserve identity.
-/
theorem map_one (f : GroupHom G H) : f (1 : G) = (1 : H) := by
    have h : f 1 = f 1 * f 1 := by
        calc
            f 1 = f (1 * 1) := by rw [Group.left_id]
            _ = f 1 * f 1 := by rw [map_mul]
    apply Group.unique_self_id ; apply Eq.symm
    exact h
theorem iso_one (f : GroupIso G H) : f (1 : G) = (1 : H) := by
    have h : f 1 = f 1 * f 1 := by
        calc
            f 1 = f (1 * 1) := by rw [Group.left_id]
            _ = f 1 * f 1 := by rw [iso_mul]
    apply Group.unique_self_id ; apply Eq.symm
    exact h
/--
    3.3. Homomorphisms preserve inverses.
-/
theorem map_inv (f : GroupHom G H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
    apply Group.left_cancel (f a)
    calc
        f a * f a⁻¹ = f (a * a⁻¹) := by rw [map_mul]
        _ = f 1 := by rw [Group.right_inv]
        _ = f a * (f a)⁻¹ := by rw [Group.right_inv, map_one]
theorem iso_inv (f : GroupIso G H) (a : G) : f a⁻¹ = (f a)⁻¹ := by
    apply Group.left_cancel (f a)
    calc
        f a * f a⁻¹ = f (a * a⁻¹) := by rw [iso_mul]
        _ = f 1 := by rw [Group.right_inv]
        _ = f a * (f a)⁻¹ := by rw [Group.right_inv, iso_one]
/--
    3.4. The composition of two homomorphisms is a homomorphism.
-/
def HomCompose (f : GroupHom H K) (g : GroupHom G H) : GroupHom G K where
    map := f ∘ g
    map_mul' := by intro a b ; simp ; repeat rw [<- map_mul]
/--
    3.5. The identity function is a group automorphism.
-/
def IdAuto : GroupIso G G where
    map := id
    map_mul' := by intro a b ; unfold id ; rfl
    inv := id
    left_inv' := by rfl
    right_inv' := by rfl
/--
    3.6. The inverse of a group automorphism is an automorphism.
-/
def InvAuto (f : GroupIso G G) : GroupIso G G where
    map := f.inv
    inv := f.map
    left_inv' := f.right_inv'
    right_inv' := f.left_inv'
    map_mul' := by
        intro a b
        have : f.map (a * b) = f.map a * f.map b := f.map_mul' a b
        have h (x y : G) : f.inv (f.map x * f.map y) = f.inv (f.map x) * f.inv (f.map y) := by
            calc
                f.inv (f.map x * f.map y) = f.inv (f.map (x * y)) := by rw [f.map_mul']
                _ = (f.inv ∘ f.map) (x * y) := by rfl
                _ = id (x * y) := by rw [f.left_inv']
                _ = id x * id y := by rfl
                _ = (f.inv ∘ f.map) x * (f.inv ∘ f.map) y := by rw [f.left_inv']
                _ = f.inv (f.map x) * f.inv (f.map y) := by rfl
        specialize h (f.inv a) (f.inv b)
        have h' (x : G) : f.map (f.inv x) = (f.map ∘ f.inv) x := by rfl
        rw [h', h', f.right_inv'] at h
        simp_all
instance {G : Type*} [Group G] : Inv (GroupIso G G) where
    inv := fun f => InvAuto f
/--
    3.7. The composition of two automorphisms is an automorphism.
-/
def IsoCompose (f : GroupIso G G) (g : GroupIso G G) : GroupIso G G where
    map := f ∘ g
    map_mul' := by
        intro a b ; simp ; repeat rw [<- iso_mul]
    inv := g.inv ∘ f.inv
    left_inv' := by
        change (g.inv ∘ f.inv) ∘ f.map ∘ g.map = id
        calc
            (g.inv ∘ f.inv) ∘ f.map ∘ g.map = g.inv ∘ (f.inv ∘ f.map) ∘ g.map := by rfl
            _ = g.inv ∘ id ∘ g.map := by rw [f.left_inv']
            _ = g.inv ∘ g.map := by rfl
            _ = id := by rw [g.left_inv']
    right_inv' := by
        change (f.map ∘ g.map) ∘ g.inv ∘ f.inv = id
        calc
            (f.map ∘ g.map) ∘ g.inv ∘ f.inv = f.map ∘ (g.map ∘ g.inv) ∘ f.inv := by rfl
            _ = f.map ∘ id ∘ f.inv := by rw [g.right_inv']
            _ = f.map ∘ f.inv := by rfl
            _ = id := by rw [f.right_inv']
/--
    3.8. The inclusion map of a subgroup into its parent group is a homomorphism.
-/
def CanonicalEmbedding (G : Type*) [Group G] (H : Subgroup G) :
    GroupHom (SubgroupType G H) G where
        map := fun a => a.val
        map_mul' := by intro a b ; rfl
/--
    3.9. A × B ≅ B × A
-/
instance (A B : Type u) [Group A] [Group B] : GroupIso (A × B) (B × A) where
    map := fun ⟨a, b⟩ => ⟨b, a⟩
    map_mul' := by
        intro _ _
        simp_all
        rfl
    inv := fun ⟨b, a⟩ => ⟨a, b⟩
    left_inv' := by
        simp_all
        rfl
    right_inv' := by
        simp_all
        rfl
/--
    3.10. "Associativity of the direct product" isomorphism.
-/
instance (A B C : Type u) [Group A] [Group B] [Group C] :
    GroupIso ((A × B) × C) (A × B × C) where
        map := fun ⟨⟨a, b⟩, c⟩ => ⟨a, ⟨b, c⟩⟩
        map_mul' := by intro _ _ ; simp_all ; rfl
        inv := fun ⟨a, ⟨b, c⟩⟩ => ⟨⟨a, b⟩, c⟩
        left_inv' := by simp_all ; rfl
        right_inv' := by simp_all ; rfl
/--
    3.11. Left and right product projection.
-/
instance (A B : Type u) [Group A] [Group B] : GroupHom (A × B) A where
    map := fun ⟨a, b⟩ => a
    map_mul' := by simp_all
instance (A B : Type u) [Group A] [Group B] : GroupHom (A × B) B where
    map := fun ⟨a, b⟩ => b
    map_mul' := by simp_all
/--
    3.12. The inverse map is (only) an automorphism on an abelian group.
-/
instance (A : Type u) [AbGroup A] : GroupIso A A where
    map := fun a => a⁻¹
    map_mul' := by
        intro a b
        rw [Group.inverted_inv]
        calc
            (a * b)⁻¹ = b⁻¹ * a⁻¹ := by rw [Group.inverted_inv]
            _ = a⁻¹ * b⁻¹ := by rw [<- Group.comm] -- Necessitates AbGroup instance.
            _ = (b * a)⁻¹ := by rw [Group.inverted_inv]
    inv := fun a => a⁻¹
    left_inv' := by
        ext x
        calc
            ((fun a ↦ a⁻¹) ∘ fun a ↦ a⁻¹) x = (fun a ↦ a⁻¹) x⁻¹ := by simp
            _ = (x⁻¹)⁻¹ := by simp
            _ = x := by rw [Group.involuted_inv]
    right_inv' := by
        ext x
        calc
            ((fun a ↦ a⁻¹) ∘ fun a ↦ a⁻¹) x = (fun a ↦ a⁻¹) x⁻¹ := by simp
            _ = (x⁻¹)⁻¹ := by simp
            _ = x := by rw [Group.involuted_inv]
/--
    3.13. The square map is (only) a homomorphism on an abelian group.
-/
instance (A : Type u) [AbGroup A] : GroupHom A A where
    map := fun a => a * a
    map_mul' := by
        intro a b
        calc
            a * b * (a * b) = a * (b * a) * b := by repeat rw [Group.assoc]
            _ = a * (a * b) * b := by rw [Group.comm b] -- Necessitates AbGroup instance.
            _ = a * a * (b * b) := by repeat rw [Group.assoc]
end GroupHom
/--
    3.14. Automorphisms of a group form a group under composition.
-/
instance Aut (G : Type*) [Group G] : Group (GroupIso G G) where
    mul := GroupHom.IsoCompose
    one := GroupHom.IdAuto
    one_mul := by intro a ; rfl
    inv := GroupHom.InvAuto
    mul_assoc := by intro a b c ; rfl
    inv_left := by
        intro a
        ext x
        calc
            (GroupHom.IsoCompose (GroupHom.InvAuto a) a) x =
                (GroupHom.InvAuto a).map (a.map x) := rfl
            _ = a.inv (a.map x) := rfl
            _ = (a.inv ∘ a.map) x := rfl
            _ = id x := by rw [a.left_inv']
            _ = (GroupHom.IdAuto : GroupIso G G).map x := rfl
/-
    3.15. Aut(G) ≤ Sym(G).
-/
def AutoPerm (G : Type*) [Group G] [Fintype G] (f : GroupIso G G) : Permutation G where
    map := f.map
    inv := f.inv
    left_inv := f.left_inv'
    right_inv := f.right_inv'
instance (G : Type*) [Group G] [Fintype G] : Subgroup (Permutation G) where
    carrier := fun f => ∃ g : GroupIso G G, f = AutoPerm G g
    has_one := by use 1 ; rfl
    is_closed := by
        intro a b ha hb
        choose σ hσ using ha
        choose τ hτ using hb
        use σ * τ
        subst hτ hσ
        rfl
    has_inv := by
        intro a ha
        choose g hg using ha
        use g⁻¹
        subst hg
        rfl
/--
    3.16. Conjugation by a fixed element is a group ("inner") automorphism.
-/
def Conj (G : Type u) [Group G] (x : G) : GroupIso G G where
    map := fun a => x * a * x⁻¹
    map_mul' := by
        intro a b
        have : x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by
            calc
                x * a * x⁻¹ * (x * b * x⁻¹) = x * a * (x⁻¹ * x) * b * x⁻¹ := by
                    repeat rw [Group.assoc]
                _ = x * a * 1 * b * x⁻¹ := by rw [Group.left_inv]
                _ = x * (a * b) * x⁻¹ := by rw [Group.right_id, Group.assoc]
        apply Eq.symm
        exact this
    inv := fun a => x⁻¹ * a * x
    left_inv':= by
        ext a
        simp_all only [Function.comp_apply, id_eq]
        calc
            x⁻¹ * (x * a * x⁻¹) * x = (x⁻¹ * x) * a * (x⁻¹ * x) := by repeat rw [Group.assoc]
            _ = 1 * a * 1 := by rw [Group.left_inv]
            _ = a := by rw [Group.left_id, Group.right_id]
    right_inv' := by
        ext a
        simp_all only [Function.comp_apply, id_eq]
        calc
             x * (x⁻¹ * a * x) * x⁻¹ =  (x * x⁻¹) * a * (x * x⁻¹) := by
                repeat rw [Group.assoc]
            _ = 1 * a * 1 := by rw [Group.right_inv]
            _ = a := by rw [Group.left_id, Group.right_id]
/--
    3.17. Inn(G), the set of inner automorphisms of G, is a normal subgroup of Aut(G).
-/
instance Inn (G : Type u) [Group G] : NormalSubgroup (GroupIso G G) where
    carrier := fun k => ∃ x : G, Conj G x = k
    has_one := by
        use 1
        apply DFunLike.ext
        unfold Conj
        intro x
        change (fun a => 1 * a * 1⁻¹) x = (1 : GroupIso G G) x
        simp_all only
        rw [Group.left_id, Group.inv_one, Group.right_id]
        rfl
    is_closed := by
        intro a b ha hb
        choose x hx using ha
        choose y hy using hb
        use x * y
        apply DFunLike.ext
        unfold Conj
        intro g
        change (fun a ↦ x * y * a * (x * y)⁻¹) g = (a * b) g
        have : GroupHom.IsoCompose (Conj G x) (Conj G y) = GroupHom.IsoCompose a b := by
            subst hy hx
            simp_all only
        subst hy hx
        simp_all only
        change x * y * g * (x * y)⁻¹ = ((fun a => x * a * x⁻¹) ∘ (fun a => y * a * y⁻¹)) g
        simp_all
        rw [<- Group.inverted_inv]
        repeat rw [Group.assoc]
    has_inv := by
        intro a ha
        choose x hx using ha
        use x⁻¹
        subst hx
        ext n
        unfold Conj
        change (fun a => x⁻¹ * a * (x⁻¹)⁻¹) n = (fun a => x⁻¹ * a * x) n
        simp_all
        rw [Group.involuted_inv]
    normal := by
        intro a ha b
        choose x hx using ha
        use b x
        apply DFunLike.ext
        intro y
        unfold Conj
        change (fun c ↦ b x * c * (b x)⁻¹) y = (b * a * b⁻¹) y
        have : a = (fun c => x * c * x⁻¹) := by subst hx ; rfl
        subst hx
        change (fun c ↦ b x * c * (b x)⁻¹) y = (b ∘ (fun c => x * c * x⁻¹) ∘ b.inv) y
        simp [Function.comp]
        rw [GroupHom.iso_mul, GroupHom.iso_mul]
        have h : b (b.inv y) = y := by
            change (b.map ∘ b.inv) y = y
            rw [GroupIso.right_inv']
            rfl
        rw [h, <- GroupHom.iso_inv]
/-


    Section 4. Quotient groups.


-/
def induce (G : Type u) [Group G] (K : NormalSubgroup G) : G → G → Prop :=
    fun x y => x⁻¹ * y ∈ K.carrier
instance inducement (G : Type u) [Group G] (K : NormalSubgroup G) :
    Equivalence (induce G K) where
        refl := by
            intro x
            unfold induce
            rw [left_inv]
            exact Subgroup.has_one _
        symm := by
            intro x y
            unfold induce
            intro h
            have h1 : (x⁻¹ * y)⁻¹ ∈ K.carrier := by
                apply K.has_inv ; exact h
            have : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by
                calc
                    (x⁻¹ * y)⁻¹ = y⁻¹ * (x⁻¹)⁻¹ := by rw [Group.inverted_inv]
                    _ = y⁻¹ * x := by rw [Group.involuted_inv]
            rw [this] at h1
            exact h1
        trans := by
            intro x y z fxy fyz
            unfold induce at *
            have h : (x⁻¹ * y) * (y⁻¹ * z) ∈ K.carrier := by
                apply Subgroup.is_closed ; apply fxy ; apply fyz
            have : (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * z := by
                calc
                    (x⁻¹ * y) * (y⁻¹ * z) = x⁻¹ * (y * y⁻¹) * z := by repeat rw [Group.assoc]
                    _ = x⁻¹ * 1 * z := by rw [Group.right_inv]
                    _ = x⁻¹ * z := by rw [Group.right_id]
            rw [this] at h
            exact h
def induced_setoid (G : Type u) [Group G] (K : NormalSubgroup G) : Setoid G where
    r := induce G K
    iseqv := inducement G K
def NormalQuotient (G : Type u) [Group G] (K : NormalSubgroup G) : Type u :=
        Quotient (induced_setoid G K)
instance (G : Type u) [Group G] : HasQuotient G (NormalSubgroup G) where
    quotient' := fun K => NormalQuotient G K
/--
    4.1. The image of a homomorphism is a subgroup of its codomain.
-/
def HomImage (G H : Type*) [Group G] [Group H] (f : GroupHom G H) : Subgroup H where
    carrier := Set.image f Set.univ
    has_one := by
        have : f 1 = 1 := by rw [GroupHom.map_one]
        simp_all only [Set.image_univ, Set.mem_range]
        apply Exists.intro
        exact this
    is_closed := by
        intro f_a f_b _ _
        change f_a * f_b ∈ ⇑f '' Set.univ
        have ha : ∃ a : G, f a = f_a := by simp_all only [Set.image_univ, Set.mem_range]
        have hb : ∃ b : G, f b = f_b := by simp_all only [Set.image_univ, Set.mem_range]
        choose a hxa using ha
        choose b hxb using hb
        have : f (a * b) = f a * f b := by rw [GroupHom.map_mul]
        subst hxa hxb
        simp_all only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]
        apply Exists.intro
        exact this
    has_inv := by
        intro f_a hfa
        have ha : ∃ a : G, f a = f_a := by simp_all only [Set.image_univ, Set.mem_range]
        choose a hxa using ha
        have : (f a)⁻¹ ∈ ⇑f '' Set.univ := by
            subst hxa
            simp_all only [Set.image_univ, Set.mem_range, exists_apply_eq_apply]
            use a⁻¹
            rw [GroupHom.map_inv]
        choose y hfy using this
        simp_all
        use y
        rw [hfy]
        rfl
/--
    4.2. The kernel of a group homomorphism is a normal subgroup of its domain.
-/
def HomKernel (G H : Type*) [Group G] [Group H] (f : GroupHom G H) : NormalSubgroup G where
    carrier := fun x : G => f x = 1
    has_one := by
        have : f 1 = 1 := by rw [GroupHom.map_one]
        exact this
    is_closed := by
        intro a b ha hb
        have h (x y : G) : f x = 1 -> f y = 1 -> f x * f y = 1 := by
            intro hfx hfy
            rw [hfx, hfy, Group.left_id]
        have hxa : f a = 1 := by simp_all only ; exact ha
        have hxb : f b = 1 := by simp_all only ; exact hb
        specialize h a b hxa hxb
        rw [<- GroupHom.map_mul] at h
        exact h
    has_inv := by
        intro a ha
        have hxa : f a = 1 := by rw [ha]
        have : f a⁻¹ = 1 := by
            calc
                f a⁻¹ = 1 * f a⁻¹ := by rw [Group.left_id]
                _ = f a * f a⁻¹ := by rw [hxa]
                _ = f (a * a⁻¹) := by rw [GroupHom.map_mul]
                _ = f 1 := by rw [Group.right_inv]
                _ = 1 := by rw [GroupHom.map_one]
        exact this
    normal := by
        intro a ha x
        have h : f (x * a * x⁻¹) = 1 := by
            calc
                f (x * a * x⁻¹) = f x * f a * f x⁻¹ := by repeat rw [GroupHom.map_mul]
                _ = f x * 1 * f x⁻¹ := by rw [ha]
                _ = f x * f x⁻¹ := by rw [Group.right_id]
                _ = f (x * x⁻¹) := by rw [GroupHom.map_mul]
                _ = f 1 := by rw [Group.right_inv]
                _ = 1 := by rw [GroupHom.map_one]
        exact h
/--
    4.3. Multiplication operation of a generic group "lifted" to the quotient type.
-/
def coset_mul (G : Type u) [Group G] (K : NormalSubgroup G) : G ⧸ K -> G ⧸ K -> G ⧸ K :=
    Quotient.lift₂ (fun a b : G => ⟦a * b⟧)
        (by
            intro a1 b1 a2 b2 ha hb
            apply Quotient.sound
            change (a1 * b1)⁻¹ * (a2 * b2) ∈ K
            change a1⁻¹ * a2 ∈ K at ha
            change b1⁻¹ * b2 ∈ K at hb
            have h' : (a1 * b1)⁻¹ * (a2 * b2) = (b1⁻¹ * a1⁻¹) * (a2 * b2) := by
                rw [Group.inverted_inv]
            rw [h']
            have hac : b1⁻¹ * (a1⁻¹ * a2) * (b1⁻¹)⁻¹ ∈ K := by
                apply NormalSubgroup.normal
                exact ha
            rw [Group.involuted_inv] at hac
            have hab : (b1⁻¹ * (a1⁻¹ * a2) * b1) * (b1⁻¹ * b2) ∈ K := by
                apply Subgroup.is_closed
                apply hac ; apply hb
            have hab' :
                b1⁻¹ * (a1⁻¹ * a2) * b1 * (b1⁻¹ * b2) = b1⁻¹ * a1⁻¹ * a2 * b2 := by
                    have : b1 * (b1⁻¹ * b2) = (b1 * b1⁻¹) * b2 := by
                        rw [Group.assoc]
                    rw [<- Group.assoc, this, Group.right_inv, Group.left_id, Group.assoc]
            rw [Group.assoc]
            rw [hab'] at hab
            exact hab)
/--
    4.4. Inverse map of a group lifted to the quotient type.
-/
instance (G : Type u) [Group G] (K : NormalSubgroup G) : Inv (G ⧸ K) where
    inv := Quotient.lift (fun a : G => ⟦a⁻¹⟧)
        (by
            intro a b hab
            apply Quotient.sound
            change a⁻¹ * b ∈ K at hab
            change (a⁻¹)⁻¹ * b⁻¹ ∈ K
            rw [Group.involuted_inv]
            have hba : b⁻¹ * a ∈ K := by
                have : (a⁻¹ * b)⁻¹ ∈ K := by
                    apply Subgroup.has_inv
                    exact hab
                rw [<- Group.inverted_inv, Group.involuted_inv] at this
                exact this
            have : b * (b⁻¹ * a) * b⁻¹ ∈ K := by apply NormalSubgroup.normal ; apply hba
            rw [Group.assoc, Group.right_inv, Group.left_id] at this
            exact this)
/--
    4.5. The quotient of a group by a normal subgroup is a group.
-/
instance (G : Type u) [Group G] (K : NormalSubgroup G) : Group (G ⧸ K) where
    mul := coset_mul G K
    one := ⟦1⟧
    inv := fun aK => aK⁻¹
    mul_assoc := by
        intro aK bK cK
        refine Quotient.inductionOn₃ aK bK cK ?_
        intro a b c
        apply Quotient.sound
        change (a * (b * c))⁻¹ * (a * b * c) ∈ K
        have h1 : (a * (b * c))⁻¹ * (a * b * c) = 1 := by
            calc
                (a * (b * c))⁻¹ * (a * b * c) = (b * c)⁻¹ * a⁻¹ * (a * b * c) := by
                    rw [Group.inverted_inv]
                _ = c⁻¹ * b⁻¹ * a⁻¹ * (a * b * c) := by
                    rw [<- Group.inverted_inv]
                _ = c⁻¹ * (b⁻¹ * (a⁻¹ * a) * b) * c := by repeat rw [Group.assoc]
                _ = c⁻¹ * (b⁻¹ * b) * c := by rw [Group.left_inv, Group.right_id]
                _ = c⁻¹ * c := by rw [Group.left_inv, Group.right_id]
                _ = 1 := by rw [Group.left_inv]
        rw [h1]
        apply Subgroup.has_one
    one_mul := by
        intro aK
        refine Quotient.inductionOn aK ?_
        intro a
        apply Quotient.sound
        change (1 * a)⁻¹ * a ∈ K
        rw [Group.left_id, Group.left_inv]
        apply Subgroup.has_one
    inv_left := by
        intro aK
        refine Quotient.inductionOn aK ?_
        intro a
        apply Quotient.sound
        change (a⁻¹ * a)⁻¹ * 1 ∈ K
        rw [Group.right_id, <- Group.inverted_inv, Group.involuted_inv, Group.left_inv]
        apply Subgroup.has_one
/--
    4.6. The canonical surjection π : G -> G/K is a group homomorphism.
-/
def QuotientHom (G : Type u) [Group G] (K : NormalSubgroup G) : GroupHom G (G ⧸ K) where
    map := fun a => ⟦a⟧
    map_mul' := by
        intro a b
        apply Quotient.sound
        change (a * b)⁻¹ * (a * b) ∈ K
        rw [<- Group.inverted_inv]
        have : b⁻¹ * a⁻¹ * (a * b) = 1 := by
            calc
                b⁻¹ * a⁻¹ * (a * b) = b⁻¹ * (a⁻¹ * a) * b := by repeat rw [Group.assoc]
                _ = b⁻¹ * b := by rw [Group.left_inv, Group.right_id]
                _ = 1 := by rw [Group.left_inv]
        rw [this]
        apply Subgroup.has_one
/--
    4.7. The titular isomorphism of the First Isomorphism Theorem.
-/
noncomputable def InducedHom (G H : Type u) [Group G] [Group H] (f : GroupHom G H) :
    GroupIso (G ⧸ (HomKernel G H f)) (SubgroupType H (HomImage G H f)) where
        map := fun xK => xK.liftOn (fun x : G => ⟨f x, ⟨x, (by simp)⟩⟩) (by
            intro a b hab
            change a⁻¹ * b ∈ HomKernel G H f at hab
            have : f (a⁻¹ * b) = (1 : H) := by
                rw [hab]
            have h : f a⁻¹ * f b = f a⁻¹ * f a := by --f (a⁻¹ * b) = = f (a⁻¹ * a) := by
                calc
                    f a⁻¹ * f b = f (a⁻¹ * b) := by rw [GroupHom.map_mul]
                    f (a⁻¹ * b) = f 1 := by rw [this, GroupHom.map_one]
                    _ = f (a⁻¹ * a) := by rw [Group.left_inv]
                    _ = f a⁻¹ * f a := by rw [GroupHom.map_mul]
            rw [GroupHom.map_inv] at h
            have : f b = f a := by
                apply Group.left_cancel (f a)⁻¹ (f b) (f a) at h
                exact h
            simp_all)
        map_mul' := by
            intro aK bK
            refine Quotient.inductionOn₂ aK bK ?_
            intro a b
            simp_all only [Quotient.lift_mk]
            apply Subtype.ext
            apply GroupHom.map_mul
        inv := fun y => ⟦Classical.choose y.2⟧
        left_inv' := by
            ext xK
            refine Quotient.inductionOn xK ?_
            intro x
            have h : f x ∈ (HomImage G H f).carrier := by
                simp [HomImage, Set.image_univ, Set.mem_range]
            let chosen := Classical.choose h
            have chosen_spec : f chosen = f x := (Classical.choose_spec h).2
            apply Quotient.sound
            change (chosen)⁻¹ * x ∈ (HomKernel G H f).toSubgroup.carrier
            calc
                f ((Classical.choose h)⁻¹ * x) = f ((Classical.choose h)⁻¹) * f x := by
                    rw [GroupHom.map_mul]
                _ = (f (Classical.choose h))⁻¹ * f x := by
                    rw [GroupHom.map_inv]
                _ = (f x)⁻¹ * f x := by
                    rw [chosen_spec]
                _ = 1 := by
                    rw [Group.left_inv]
        right_inv' := by
            ext ⟨y, x, ⟨xin, fxy⟩⟩
            have h_choose_spec := Classical.choose_spec (by
                change y ∈ Set.image f Set.univ
                exact ⟨x, by simp, fxy⟩)
            simp at h_choose_spec
            subst fxy
            simp_all only [
                Set.mem_univ,
                true_and,
                Function.comp_apply,
                Quotient.lift_mk,
                id_eq
            ]
/--
    4.8. Outer automorphism group definition.
-/
def Out (G : Type u) [Group G] : Type u := GroupIso G G ⧸ Inn G
/-


    Section 5 : Cyclic groups.


-/
/--
    5.1. Natural number powers of a group element.
-/
@[simp]
def npow {G : Type*} [Group G] : G → ℕ → G :=
    fun a n =>
        match n with
            | 0 => 1
            | k + 1 => a * (npow a k)
theorem npow_one (G : Type u) [Group G] (x : G) : x = npow x 1 := by
    simp ; rw [Group.right_id]
theorem npow_succ (G : Type u) [Group G] (x : G) (n : ℕ) :
    x * (npow x n) = npow x (n + 1) := by
        simp_all only [npow]
@[simp]
theorem npow_nat_exp (G : Type*) [Group G] (x : G) (n m : ℕ) :
    (npow x n) * (npow x m) = npow x (n + m) := by
        induction n generalizing m
        case zero =>
            cases m
            simp_all
            case zero => rw [Group.right_id]
            case succ k =>
                simp_all
                rw [Group.left_id]
        case succ k ih =>
            simp_all
            specialize ih m
            calc
                x * npow x k * npow x m = x * (npow x k * npow x m) := by rw [Group.assoc]
                _ = x * (npow x (k + m)) := by rw [ih]
                _ = npow x (k + m + 1) := by rw [npow_succ]
                _ = npow x (k + 1 + m) := by
                    rw [Nat.add_comm, <- Nat.add_assoc, Nat.add_comm k]
@[simp]
theorem npow_comm (G : Type*) [Group G] (x : G) (n m : ℕ) :
    (npow x n) * (npow x m) = (npow x m) * (npow x n) := by
        rw [npow_nat_exp, npow_nat_exp, Nat.add_comm]
theorem npow_comm_succ (G : Type*) [Group G] (x : G) (n : ℕ) :
    x * (npow x n) = (npow x n) * x := by
        calc
            x * npow x n = npow x 1 * npow x n := by rw [<- npow_one]
            _ = npow x n * npow x 1 := by rw [npow_comm]
            _ = npow x n * x := by rw [<- npow_one]
@[simp]
theorem npow_inv_exp (G : Type*) [Group G] (x : G) (n m : ℕ) :
    (npow x n)⁻¹ * (npow x m)⁻¹ = (npow x (n + m))⁻¹ := by
        induction n generalizing m
        case zero =>
            simp_all
            rw [Group.inv_one, Group.left_id]
        case succ k ih =>
            simp_all only [npow]
            specialize ih m
            calc
                (x * npow x k)⁻¹ * (npow x m)⁻¹ =
                (npow x 1 * npow x k)⁻¹ * (npow x m)⁻¹ := by
                    rw [<- npow_one]
                _ = (npow x k * npow x 1)⁻¹ * (npow x m)⁻¹ := by
                    rw [npow_comm]
                _ = (npow x 1)⁻¹ * ((npow x k)⁻¹ * (npow x m)⁻¹) := by
                    rw [<- Group.inverted_inv, Group.assoc]
                _ = (npow x 1)⁻¹ * (npow x (k + m))⁻¹ := by
                    rw [ih] -- ⊢ (npow x (k + 1 + m))⁻¹
                _ = (npow x (k + m) * npow x 1)⁻¹ := by
                    rw [Group.inverted_inv]
                _ = (npow x (k + m + 1))⁻¹ := by rw [npow_nat_exp]
                _ = (npow x (k + 1 + m))⁻¹ := by grind
@[simp]
theorem npow_right_inv_ge (G : Type*) [Group G] (x : G) (n m : ℕ) (h : n ≥ m) :
   (npow x n) * (npow x m)⁻¹ = npow x (n - m) := by
        induction n generalizing m
        case zero =>
            simp_all
            rw [Group.left_id, Group.inv_one]
        case succ a ih =>
            cases m
            case zero =>
                simp_all
                rw [Group.inv_one, Group.right_id]
            case succ b =>
                have h : a ≥ b := by simp_all only [ge_iff_le, Nat.add_le_add_iff_right]
                specialize ih b h
                simp_all only [ge_iff_le, Nat.add_le_add_iff_right, npow, Nat.reduceSubDiff]
                have : npow x 1 * npow x b = npow x b * npow x 1 := by
                    rw [npow_comm]
                calc
                    x * npow x a * (x * npow x b)⁻¹ =
                    npow x 1 * npow x a * (npow x 1 * npow x b)⁻¹ := by
                        rw [<- npow_one]
                    _ = npow x a * npow x 1 * (npow x b * npow x 1)⁻¹ := by
                        rw [npow_comm, this]
                    _ = npow x a * x * (npow x b * x)⁻¹ := by
                        rw [<- npow_one]
                    _ = npow x a * x * x⁻¹ * (npow x b)⁻¹ := by
                        rw [<- Group.inverted_inv, Group.assoc]
                    _ = npow x a * (x * x⁻¹) * (npow x b)⁻¹ := by
                        rw [Group.assoc]
                    _ = npow x a * (npow x b)⁻¹ := by
                        rw [Group.right_inv, Group.right_id]
                    _ = npow x (a - b) := by
                        exact ih
@[simp]
theorem npow_right_inv_lt (G : Type*) [Group G] (x : G) (n m : ℕ) (h : n < m) :
    (npow x n) * (npow x m)⁻¹ = (npow x (m - n))⁻¹ := by
        induction m generalizing n
        case zero =>
            simp_all
        case succ a ih =>
            cases n
            case zero =>
                simp_all
                rw [Group.left_id]
            case succ b =>
                simp_all
                have (k : ℕ) : x * npow x k = npow x k * x := by
                    calc
                        x * npow x k = npow x 1 * npow x k := by rw [<- npow_one]
                        _ = npow x k * npow x 1 := by rw [npow_comm]
                        _ = npow x k * x := by rw [<- npow_one]
                rw [this]
                calc
                    npow x b * x * (x * npow x a)⁻¹ = npow x b * x * (npow x a * x)⁻¹ := by
                        rw [this]
                    _ = npow x b * x * (x⁻¹ * (npow x a)⁻¹) := by
                        rw [Group.inverted_inv]
                    _ = npow x b * (x * x⁻¹) * (npow x a)⁻¹ := by
                        repeat rw [Group.assoc]
                    _ = npow x b * (npow x a)⁻¹ := by
                        rw [Group.right_inv, Group.right_id]
                    _ = (npow x (a - b))⁻¹ := by
                        apply ih
                        exact h
@[simp]
theorem npow_left_inv_ge (G : Type*) [Group G] (x : G) (n m : ℕ) (h : n ≥ m) :
    (npow x n)⁻¹ * (npow x m) = (npow x (n - m))⁻¹ := by
        induction n generalizing m
        case zero =>
            simp_all
            rw [Group.right_id]
        case succ a ih =>
            cases m
            case zero =>
                simp_all
                rw [Group.right_id]
            case succ b =>
                have hab : a ≥ b := by omega
                specialize ih b hab
                rw [
                    <- npow_succ,
                    <- npow_succ,
                    <- Group.inverted_inv,
                    Nat.add_comm b,
                ]
                have : a + 1 - (1 + b) = a - b := by omega
                rw [this]
                calc
                    (npow x a)⁻¹ * x⁻¹ * (x * npow x b) = (npow x a)⁻¹ * (x⁻¹ * x) * npow x b := by
                        repeat rw [Group.assoc]
                    _ = (npow x a)⁻¹ * npow x b := by
                        rw [Group.left_inv, Group.right_id]
                    _ = (npow x (a - b))⁻¹ := by exact ih
@[simp]
theorem npow_left_inv_lt (G : Type*) [Group G] (x : G) (n m : ℕ) (h : n < m) :
    (npow x n)⁻¹ * (npow x m) = (npow x (m - n)) := by
        induction n generalizing m
        case zero =>
            simp_all
            rw [<- Group.inv_one]
            rw [Group.involuted_inv, Group.left_id]
        case succ a ih =>
            cases m
            case zero => simp_all
            case succ b =>
                have : 1 + b - (a + 1) = b - a := by omega
                have hab : a < b := by omega
                specialize ih b hab
                rw [
                    <- npow_succ,
                    <- npow_succ,
                    <- Group.inverted_inv,
                    Nat.add_comm b,
                    this
                ]
                calc
                    (npow x a)⁻¹ * x⁻¹ * (x * npow x b) = (npow x a)⁻¹ * (x⁻¹ * x) * npow x b := by
                        repeat rw [Group.assoc]
                    _ = (npow x a)⁻¹ * npow x b := by
                        rw [Group.left_inv, Group.right_id]
                    _ = (npow x (b - a)) := by exact ih
/--
    5.2. Integer powers of a group element.
-/
@[simp]
def zpow {G : Type*} [Group G] : G → ℤ → G :=
    fun a n =>
        match n with
            | Int.ofNat k => npow a k
            | Int.negSucc k => (npow a (k + 1 : ℕ))⁻¹
instance {G : Type*} [Group G] : Pow G ℤ := ⟨zpow⟩
@[simp]
theorem zpow_zero {G : Type*} [Group G] (a : G) : a ^ (0 : ℤ) = 1 :=
    rfl
@[simp]
theorem zpow_one {G : Type*} [Group G] (a : G) : a ^ (1 : ℤ) = a := by
    change zpow a 1 = a
    unfold zpow
    simp_all
    rw [Group.right_id]
@[simp]
theorem zpow_ofNat {G : Type*} [Group G] (a : G) (n : ℕ) : a ^ (n : ℤ) = npow a n :=
    rfl
@[simp]
theorem zpow_ns {G : Type*} [Group G] (a : G) (n : ℕ) :
    a ^ (Int.negSucc n) = (npow a (n + 1 : ℕ))⁻¹ :=
        rfl
@[simp]
theorem zpow_int_exp (G : Type*) [Group G] (x : G) (n m : ℤ) :
    (x ^ n) * (x ^ m) = x ^ (n + m) := by
        induction n generalizing m
        case ofNat G a =>
            cases m
            case ofNat G b =>
                simp_all
                change npow x (a + b) = zpow x (↑a + ↑b)
                simp_all only [zpow, npow]
                rfl
            case negSucc b =>
                simp_all only [Int.ofNat_eq_coe, zpow_ofNat, zpow_ns, npow]
                change npow x a * (x * npow x b)⁻¹ = zpow x (↑a + Int.negSucc b)
                unfold zpow
                simp_all only [npow]
                split
                next n k heq =>
                    rw [npow_succ, npow_right_inv_ge]
                    have h : ((a - (b + 1)) : ℤ) = (k : ℤ) := by
                        simp_all only [Int.ofNat_eq_coe]
                        exact heq
                    have h_nat : a - (b + 1) = k := by
                        apply Int.ofNat_inj.mp
                        rw [Int.ofNat_sub (by omega)]
                        exact h
                    rw [h_nat]
                    grind
                next n k heq =>
                    rw [npow_succ]
                    have : a < (b + 1) := by omega
                    calc
                        npow x a * (npow x (b + 1))⁻¹ = (npow x ((b + 1) - a))⁻¹ := by
                            rw [npow_right_inv_lt]
                            exact this
                        _ = (npow x (k + 1))⁻¹ := by grind
        case negSucc a =>
            cases m
            case ofNat G b =>
                simp_all only [Int.ofNat_eq_coe, zpow_ofNat]
                unfold npow
                simp_all
                split
                next n =>
                    simp_all only [Int.cast_ofNat_Int, Int.add_zero, zpow_ns, npow]
                    rw [Group.right_id]
                next n k =>
                    simp_all only [Nat.succ_eq_add_one, Int.natCast_add, Int.cast_ofNat_Int]
                    have : (Int.negSucc a + ((k : ℤ) + 1)) = k - a := by
                        grind
                    rw [this, <- Group.inverted_inv]
                    have : (npow x a)⁻¹ * x⁻¹ * (x * npow x k) = (npow x a)⁻¹ * npow x k := by
                        calc
                            (npow x a)⁻¹ * x⁻¹ * (x * npow x k) =
                            (npow x a)⁻¹ * (x⁻¹ * x) * npow x k := by
                                repeat rw [Group.assoc]
                            _ = (npow x a)⁻¹ * npow x k := by
                                rw [Group.left_inv, Group.right_id]
                    rw [this]
                    by_cases a < k
                    case pos h' =>
                        simp_all only [npow_left_inv_lt]
                        have : k - a > 0 := by omega
                        change npow x (k - a) = zpow x ((k : ℤ) - ↑a)
                        unfold zpow
                        simp_all only [gt_iff_lt, npow]
                        split
                        next n_1 k_1 heq =>
                            simp_all only [Int.ofNat_eq_coe]
                            have : k - a = k_1 := by grind
                            rw [this]
                        next n_1 k_1 heq =>
                            simp_all only
                            grind
                    case neg h' hx' =>
                        have : a ≥ k := by omega
                        simp_all only [not_lt, ge_iff_le, npow_left_inv_ge]
                        by_cases k < a
                        case pos h1 =>
                            have h2 : ∃ m : ℕ, (k : ℤ) - (a : ℤ) = Int.negSucc m := by
                                use (a : ℕ) - (k + 1)
                                omega
                            choose m hm using h2
                            rw [hm, zpow_ns]
                            grind
                        case neg h1 =>
                            have : k = a := by omega
                            subst this
                            simp_all only [
                                Int.sub_self,
                                Nat.sub_self,
                                npow,
                                le_refl,
                                lt_self_iff_false,
                                not_false_eq_true,
                                zpow_zero
                            ]
                            rw [Group.inv_one]
            case negSucc b =>
                have : Int.negSucc a + Int.negSucc b = Int.negSucc (a + b + 1) := by omega
                rw [this]
                simp_all only [zpow_ns, npow]
                have : (x * (x * npow x (a + b)))⁻¹ = (npow x (a + b + 2))⁻¹ := by
                    calc
                        (x * (x * npow x (a + b)))⁻¹ = (x * (npow x (a + b + 1)))⁻¹ := by
                            rw [npow_succ]
                        _ = (npow x (a + b + 1 + 1))⁻¹ := by rw [npow_succ]
                        _ = (npow x (a + b + 2))⁻¹ := by grind
                rw [this]
                calc
                    (x * npow x a)⁻¹ * (x * npow x b)⁻¹ =
                    (npow x (a + 1))⁻¹ * (npow x (b + 1))⁻¹ := by
                        rw [npow_succ, npow_succ]
                    _ = (npow x (a + 1 + b + 1))⁻¹ := by
                        rw [npow_inv_exp]
                        grind
                    _ = (npow x (a + b + 2))⁻¹ := by grind
@[simp]
theorem zpow_inv (G : Type*) [Group G] (x : G) (n : ℤ) :
    x ^ (-n) = (x ^ n)⁻¹ := by
        apply Group.left_cancel (x ^ n)
        rw [Group.right_inv, zpow_int_exp]
        have : n + (-n) = 0 := by omega
        rw [this, zpow_zero]
/--
    5.3. Cyclic group class extension.
-/
class CyclicGroup (G : Type*) extends AbGroup G where
    mono : ∃ x : G, ∀ a : G, ∃ n : ℤ, a = x ^ n
/--
    5.4. The cyclic property implies commutativity.
-/
theorem if_cyclic_then_abelian (G : Type u) [Group G] :
    (∃ x : G, ∀ a : G, ∃ n : ℤ, a = x ^ n) -> ∀ (a b : G), a * b = b * a := by
        intro hc a b
        choose x hx using hc
        have ha : ∃ n : ℤ, a = x ^ n := by specialize hx a ; exact hx
        have hb : ∃ m : ℤ, b = x ^ m := by specialize hx b ; exact hx
        choose n hn using ha ; choose m hm using hb
        rw [hn, hm]
        rw [zpow_int_exp, zpow_int_exp, Int.add_comm]
/--
    5.5. The group generated by the powers of an element.
-/
instance CyclicSubgroup (G : Type u) [Group G] (x : G) : Subgroup G where
    carrier := fun a => ∃ n : ℤ, a = x ^ n
    has_one := by use 0 ; simp_all
    is_closed := by
        intro a b ha hb
        choose n hn using ha
        choose m hm using hb
        use n + m
        rw [hn, hm]
        change (x ^ n) * (x ^ m) = x ^ (n + m)
        apply zpow_int_exp
    has_inv := by
        intro a ha
        choose n hn using ha
        use -n
        rw [hn]
        change (x ^ n)⁻¹ = x ^ (-n)
        apply Eq.symm
        apply zpow_inv
/-


    Section 6 : Group actions.


-/
structure LeftAction (G X : Type u) [Group G] where
    act : G × X -> X
    has_one : ∀ x : X, act ⟨1, x⟩  = x
    compatible : ∀ a b : G, ∀ x : X, act ⟨a, act ⟨b, x⟩⟩  = act ⟨a * b, x⟩
instance {G X : Type u} [Group G] : FunLike (LeftAction G X) (G × X) X where
    coe f := f.act
    coe_injective' f g h := by
        cases f; cases g; congr
/--
    6.1. Left multiplication as an action of a group on itself.
-/
instance MulAct (G : Type u) [Group G] : LeftAction G G where
    act := fun ⟨a, b⟩ => a * b
    has_one := by
        intro b
        simp_all
        rw [Group.left_id]
    compatible := by
        intro a b x
        simp_all
        rw [Group.assoc]
/--
    6.2. Conjugation as an action of a group on itself.
-/
instance ConjAct (G : Type u) [Group G] : LeftAction G G where
    act := fun ⟨a, b⟩ => a * b * a⁻¹
    has_one := by
        intro x
        simp_all
        rw [left_id, inv_one, Group.right_id]
    compatible := by
        intro a b x
        simp_all
        rw [<- Group.inverted_inv]
        repeat rw [Group.assoc]
/--
    6.3. Propositions defining faithful, free, and transitive actions.
-/
def FaithfulAct (G X : Type u) [Group G] (f : LeftAction G X) :=
    ∀ a : G, (∀ x : X, f (a, x) = x) -> a = 1
def FreeAct (G X : Type u) [Group G] (f : LeftAction G X) :=
    ∀ a : G, (∃ x : X, f (a, x) = x) -> a = 1
def TransitiveAct (G X : Type u) [Group G] (f : LeftAction G X) :=
    ∀ x y : X, ∃ a : G, f (a, x) = y
/--
    6.4. Orbit and stabilizer of an element of a G-set.
-/
def Orbit (G X : Type u) [Group G] (x : X) (f : LeftAction G X) : Set X :=
    fun y : X => ∃ a : G, y = f ⟨a, x⟩
instance Stabilizer (G X : Type u) [Group G] (x : X) (f : LeftAction G X) : Subgroup G where
    carrier := fun a => f ⟨a, x⟩ = x
    has_one := by
        change f (1, x) = x
        exact f.has_one x
    is_closed := by
        intro a b ha hb
        change f.act (a * b, x) = x
        change f.act (a, x) = x at ha
        change f.act (b, x) = x at hb
        calc
            f.act (a * b, x) = f.act (a, f.act (b, x)) := by rw [<- f.compatible]
            _ = f.act (a, x) := by rw [hb]
            _ = x := by rw [ha]
    has_inv := by
        intro a ha
        change f.act (a⁻¹, x) = x
        change f.act (a, x) = x at ha
        rw [<- ha]
        calc
             f.act (a⁻¹, f.act (a, x)) = f.act (a⁻¹ * a, x) := by rw [<- f.compatible]
             _ = f.act (1, x) := by rw [Group.left_inv]
             _ = x := by rw [f.has_one]
             _ = f.act (a, x) := by rw [ha]
/--
    6.5. The kernel of a group action is a subgroup of the acting group.
-/
instance ActKernel (G X : Type u) [Group G] (f : LeftAction G X) : Subgroup G where
    carrier := fun a => ∀ x : X, f ⟨a, x⟩ = x
    has_one := by
        intro x
        apply f.has_one x
    is_closed := by
        intro a b ha hb
        change ∀ x : X, f.act (a, x) = x at ha
        change ∀ x : X, f.act (b, x) = x at hb
        change ∀ x : X, f.act ⟨a * b, x⟩ = x
        intro x
        specialize ha x
        specialize hb x
        calc
            f.act (a * b, x) = f.act (a, f.act (b, x)) := by
                rw [<- LeftAction.compatible]
            _ = f.act (a, x) := by rw [hb]
            _ = x := by rw [ha]
    has_inv := by
        intro a ha x
        change ∀ x : X, f.act (a, x) = x at ha
        specialize ha x
        change f (a⁻¹, x) = x
        calc
            f.act (a⁻¹, x) = f.act (a⁻¹, f.act (a, x)) := by
                simp_all only
            _ = f.act (a⁻¹ * a, x) := by
                rw [<- LeftAction.compatible]
            _ = x := by
                rw [Group.left_inv, LeftAction.has_one]
/--
    6.6. Left multiplication as a permutation.
-/
instance MulPerm (G : Type u) [Group G] (a : G) : Permutation G where
    map := fun x => a * x
    inv := fun x => a⁻¹ * x
    left_inv := by
        ext x
        simp_all
        rw [Group.assoc, Group.left_inv, Group.left_id]
    right_inv := by
        ext x
        simp_all
        rw [Group.assoc, Group.right_inv, Group.left_id]
/--

    6.7. Homomorphism from a group into the symmetric group on its underlying set.

    While not directly using the group action structure, the idea of a
    permutation representation of a group is closely related. We
    have in this section used the definition of a group action as a function from
    a product type to the G-set, i.e. as "α : G × X -> X."

    Of course, because of the right associativity of type signatures,
    we could also easily write an action as a function α : G -> X -> X, i.e.
    G -> (X -> X).

    Because of the group action properties, then, we have the view of a
    group action as a function (homomorphism, even) α : G -> Sym(X).

-/
instance PermRep (G : Type u) [Group G] : GroupHom G (Permutation G) where
    map := fun a => MulPerm G a
    map_mul' := by
        intro x y
        apply DFunLike.ext
        intro b
        change (MulPerm G (x * y)).map b = ((MulPerm G x).map ∘ (MulPerm G y).map) b
        unfold MulPerm
        simp_all
        rw [Group.assoc]
/--
    6.8. Cayley's theorem.

    Often stated as "every group G is isomorphic to a subgroup of the
    symmetric group on the underlying set of G."

    This immediately follows from the result that f : G -> Sym(G) is an
    injective homomorphism:

    Since f is a homomorphism, im(f) ≤ Sym(G). Since f is injective,
    ker(f) = {1}. Observing that G/{1} ≅ G, the first isomorphism
    theorem then tells us that G ≅ im(f).
-/
theorem cayley (G : Type u) [Group G] : Function.Injective (PermRep G) := by
    intro a b hab
    change (PermRep G).map a = (PermRep G).map b at hab
    unfold PermRep at hab
    simp_all
    unfold MulPerm at hab
    simp_all only [Permutation.mk.injEq]
    obtain ⟨left, right⟩ := hab
    have h := congrFun left 1
    rw [right_id, right_id] at h
    exact h

end Group
