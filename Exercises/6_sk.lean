import Mathlib.Tactic
import Mathlib.Logic.Relation
set_option linter.style.docString false
/-

    A semi-naive implementation of the
    untyped SK combinator calculus in Lean. The
    SK-calculus can be considered a "dialect" of
    λ-calculus with equivalent expressive power
    but whose implementation does not have to
    concern itself with the intricacies of
    variable substitution.

    Every term in SK-calculus is built out of the
    two primitive combinators and the application
    rules which govern how terms "reduce." The rules
    for "single-step reduction" are as follows:

    Where x, y, and z are terms:

    S x y z -> x z (y z)
    K x y -> x

    These combinators can be realized in the language of
    λ-calculus as follows:

    S := λx.λy.λz.x z (y z)
    K := λx.λy.x

    Application is left-associative: a term in the form
    "w x y z" is to be interpreted as "(((w x) y) z)."

-/
inductive Term where
    | K : Term
    | S : Term
    | App : Term -> Term -> Term
deriving Repr, DecidableEq
namespace Term
def size : Term -> ℕ
    | K => 1
    | S => 1
    | App x y => size x + size y
lemma zero_lt_size {t : Term} : 0 < size t := by
    induction t with
        | K => bound
        | S => bound
        | App x y ihx ihy => change 0 < size x + size y ; bound
lemma size_ne_zero (t : Term) : size t ≠ 0 := by
    intro hn
    have : 0 < size t := zero_lt_size
    omega
/-
    ⊗ was chosen for being the first symbol
    I found which didn't conflict with
    symbols in Mathlib.
-/
infixl:100 " ⊗ " => App
/--
    Single-step reduction of a term.
-/
inductive Reduces' : Term -> Term -> Prop where
    | K : ∀ x y, Reduces' (K ⊗ x ⊗ y) x
    | S : ∀ x y z, Reduces' (S ⊗ x ⊗ y ⊗ z) (x ⊗ z ⊗ (y ⊗ z))
    | appL : ∀ {f f' x}, Reduces' f f' -> Reduces' (f ⊗ x) (f' ⊗ x)
    | appR : ∀ {f x x'}, Reduces' x x' -> Reduces' (f ⊗ x) (f ⊗ x')
infix:50 " →¹ " => Reduces'
theorem single_step_irrefl {t s : Term} (h : t →¹ s) : t ≠ s := by
    induction h with
        | K x y =>
            intro heq
            have := congrArg size heq
            simp [size] at this
            omega
        | S x y z =>
            intro heq
            injection heq with _ h2
            have := congrArg size h2
            simp [size] at this
            have h1 : 0 < y.size := zero_lt_size
            omega
        | appL hra iha => grind
        | appR hra iha => grind
/--
    In λ-calculus terminology, this relation, which we
    can call "multi-step reduction" is the
    "reflexive transitive closure" of →¹, in that it is the
    least extension of single-step reduction which is reflexive
    and transitive. As such, "multi-step reduction" also covers
    the case of "zero-step reduction," i.e. if t is a term, then
    t →• t.

    Multi-step reduction is the "main" notion of reduction for our purposes,
    and so we will use simply "reduction" to denote multi-step reduction.
-/
inductive Reduces : Term -> Term -> Prop where
    | refl : ∀ x, Reduces x x
    | step : ∀ x y z, x →¹ y -> Reduces y z -> Reduces x z
infix:50 " →• " => Reduces
theorem Reduces.trans {x y z : Term} (h1 : x →• y) (h2 : y →• z) :
    x →• z := by
        induction h1 with
            | refl _ => exact h2
            | step _ _ _ s rest ih => exact Reduces.step _ _ _ s (ih h2)
theorem liftReduces {a b : Term} (h : a →¹ b) : a →• b :=
    Reduces.step a b _ h (Reduces.refl b)
theorem combineRight {a b c : Term} (hrx : a →• b) :
    (a ⊗ c) →• (b ⊗ c) := by
        induction hrx with
            | refl x => exact Reduces.refl (x ⊗ c)
            | step x y z hxy hyz ih =>
                exact Reduces.trans
                    (Reduces.step (x ⊗ c) (y ⊗ c) _
                        (Reduces'.appL hxy)
                        (Reduces.refl (y ⊗ c)))
                    ih
theorem combineLeft {a b c : Term} (hrx : a →• b) :
    (c ⊗ a) →• (c ⊗ b) := by
        induction hrx with
            | refl x => exact Reduces.refl (c ⊗ x)
            | step x y z hxy hyz ih =>
                exact Reduces.trans
                    (Reduces.step (c ⊗ x) (c ⊗ y) _
                        (Reduces'.appR hxy)
                        (Reduces.refl (c ⊗ y)))
                    ih
theorem fuse {x y a b : Term} (hxy : x →• y) (hab : a →• b) :
    x ⊗ a →• y ⊗ b :=
        Reduces.trans
            (combineRight hxy)
            (combineLeft hab)
theorem applyK (x y : Term) : (K ⊗ x ⊗ y) →• x :=
    Reduces.step _ _ _ (Reduces'.K x y) (Reduces.refl x)
theorem applyS (x y z : Term) : (S ⊗ x ⊗ y ⊗ z) →• (x ⊗ z ⊗ (y ⊗ z)) :=
    Reduces.step _ _ _ (Reduces'.S x y z) (Reduces.refl (x ⊗ z ⊗ (y ⊗ z)))
example : S ⊗ K ⊗ S ⊗ K →• K :=
    Reduces.trans
        (applyS K S K)
        (applyK K (S ⊗ K))
/-

    2. Imprimitive combinators.

    Due to convention, the names of many combinators
    are associated with the names of birds.

-/
/--
    The I-combinator. "I" is for "identity."
-/
def I : Term := S ⊗ K ⊗ K
theorem applyI (x : Term) : I ⊗ x →• x :=
    show S ⊗ K ⊗ K ⊗ x →• x from
        Reduces.trans
            (applyS K K x)
            (applyK x (K ⊗ x))
/--
    The B-combinator. "B" is for "bluebird."
    The B-combinator models function composition.
-/
def B : Term := S ⊗ (K ⊗ S) ⊗ K
theorem applyB (f g x : Term) : B ⊗ f ⊗ g ⊗ x →• f ⊗ (g ⊗ x) :=
    show S ⊗ (K ⊗ S) ⊗ K ⊗ f ⊗ g ⊗ x →• f ⊗ (g ⊗ x) from
        Reduces.trans
            (combineRight
                (combineRight
                    (Reduces.trans
                        (applyS (K ⊗ S) K f)
                        (combineRight (applyK S f)))))
            (Reduces.trans
                (applyS (K ⊗ f) g x)
                (combineRight (applyK f x)))
/--
    The W-combinator. The "W" stands for "warbler."
-/
def W : Term := S ⊗ S ⊗ (S ⊗ K)
theorem applyW (f x : Term) : W ⊗ f ⊗ x →• f ⊗ x ⊗ x :=
    show S ⊗ S ⊗ (S ⊗ K) ⊗ f ⊗ x →• f ⊗ x ⊗ x from
        Reduces.trans
            (Reduces.trans
                (combineRight (applyS S (S ⊗ K) f))
                (applyS f ((S ⊗ K) ⊗ f) x))
            (combineLeft
                (Reduces.trans
                    (applyS K f x)
                    (applyK x (f ⊗ x))))
/--
    The T-combinator. "T" stands for "thrush."
-/
def T : Term := S ⊗ (K ⊗ (S ⊗ I)) ⊗ K
theorem applyT (x f : Term) : T ⊗ x ⊗ f →• f ⊗ x :=
    show S ⊗ (K ⊗ (S ⊗ I)) ⊗ K ⊗ x ⊗ f →• f ⊗ x from
        Reduces.trans
            (Reduces.trans
                (Reduces.trans
                    (Reduces.trans
                        (combineRight (applyS (K ⊗ (S ⊗ I)) K x))
                        (combineRight (combineRight (applyK (S ⊗ I) x))))
                    (applyS I (K ⊗ x) f))
                (combineRight (applyI f)))
            (combineLeft (applyK x f))
/--
    The C-combinator. "C" stands for "cardinal."
    That is, the bird as opposed to the kind of number.
-/
def C : Term := S ⊗ (B ⊗ B ⊗ S) ⊗ (K ⊗ K)
theorem applyC (f x y : Term) : (C ⊗ f ⊗ x ⊗ y).Reduces (f ⊗ y ⊗ x) :=
    show (S ⊗ (B ⊗ B ⊗ S) ⊗ (K ⊗ K) ⊗ f ⊗ x ⊗ y).Reduces (f ⊗ y ⊗ x) from
        Reduces.trans
            (Reduces.trans
                (Reduces.trans
                    (Reduces.trans
                        (combineRight (combineRight (applyS (B ⊗ B ⊗ S) (K ⊗ K) f)))
                        (combineRight (combineRight (combineRight (applyB B S f)))))
                    (combineRight (applyB (S ⊗ f) ((K ⊗ K) ⊗ f) x)))
                (applyS f (((K ⊗ K) ⊗ f) ⊗ x) y))
            (combineLeft
                (Reduces.trans
                    (combineRight (combineRight (applyK K f)))
                    (applyK x y)))
/--
    The M-combinator. "M" stands for "mockingbird."
-/
def M : Term := S ⊗ I ⊗ I
theorem applyM (x : Term) : M ⊗ x →• x ⊗ x :=
    show S ⊗ I ⊗ I ⊗ x →• x ⊗ x from
        Reduces.trans
            (Reduces.trans
                (applyS I I x)
                (combineRight (applyI x)))
            (combineLeft (applyI x))
/-
    The F-combinator. F is for "false." In the realization of
    the boolean "type" in the untyped SK-calculus, K acts as "true"
    while K I acts as "false," in what is called the *Church encoding*
    for booleans. In particular, "true" is abstracted to "choosing
    the first of two" and "false" is abstracted to "choosing the second
    of two."
-/
def F : Term := (K ⊗ I)
theorem applyF (x y : Term) : F ⊗ x ⊗ y →• y :=
    show (K ⊗ I) ⊗ x ⊗ y →• y from
    Reduces.trans
        (combineRight (applyK I x))
        (applyI y)
/--
    The Ω-combinator. Ω has no normal form.
-/
def Ω : Term := M ⊗ M
theorem Ω_diverges : ∃ t : Term, Ω ≠ t ∧ Ω →• t ∧ t →• Ω := by
    unfold Ω
    unfold M
    use (I ⊗ (S ⊗ I ⊗ I) ⊗ (I ⊗ (S ⊗ I ⊗ I)))
    split_ands
    · grind
    · exact (applyS I I (S ⊗ I ⊗ I))
    · exact
        Reduces.trans
            (combineRight (applyI (S ⊗ I ⊗ I)))
            (combineLeft (applyI (S ⊗ I ⊗ I)))
/--
    The Θ-combinator, or Turing fixed-point combinator.
-/
def Θ : Term := M ⊗ (B ⊗ (S ⊗ I) ⊗ M)
theorem applyΘ (f : Term) : Θ ⊗ f →• f ⊗ (Θ ⊗ f) :=
    show M ⊗ (B ⊗ (S ⊗ I) ⊗ M) ⊗ f →• f ⊗ (M ⊗ (B ⊗ (S ⊗ I) ⊗ M) ⊗ f) from
        Reduces.trans
            (Reduces.trans
                (combineRight (applyM (B ⊗ (S ⊗ I) ⊗ M)))
                (combineRight (applyB (S ⊗ I) M (B ⊗ (S ⊗ I) ⊗ M))))
            (Reduces.trans
                (applyS I (M ⊗ (B ⊗ (S ⊗ I) ⊗ M)) f)
                (combineRight (applyI f)))
theorem fixed_point_Θ (f : Term) : ∃ x : Term, x →• f ⊗ x :=
    Exists.intro
        (Θ ⊗ f)
        (applyΘ f)
/--
    See p.24 of Barendregt (1984).
-/
example (f : Term) : ∃ x : Term, x →• f ⊗ x :=
    Exists.intro
        ((B ⊗ f ⊗ M) ⊗ (B ⊗ f ⊗ M))
        (Reduces.trans
            (applyB f M (B ⊗ f ⊗ M))
            (combineLeft (applyM (B ⊗ f ⊗ M))))
/-

    3. Parallel reduction and Church-Rosser.

    The parallel reduction approach originates from the proof
    of the Church-Rosser theorem for β-reduction by
    William W. Tait and Per Martin-Löf, by way of Masako Takahashi's
    1995 paper, "Parallel Reduction in λ-Calculus."

-/
inductive ParallelReduces : Term -> Term -> Prop where
    | K_refl : ParallelReduces K K
    | S_refl : ParallelReduces S S
    | app : ∀ {f f' x x'},
        ParallelReduces f f' -> ParallelReduces x x' -> ParallelReduces (f ⊗ x) (f' ⊗ x')
    | K_red : ∀ {x x' y y'},
        ParallelReduces x x' -> ParallelReduces y y' -> ParallelReduces (K ⊗ x ⊗ y) x'
    | S_red : ∀ {x x' y y' z z'},
        ParallelReduces x x' -> ParallelReduces y y' -> ParallelReduces z z' ->
        ParallelReduces (S ⊗ x ⊗ y ⊗ z) (x' ⊗ z' ⊗ (y' ⊗ z'))
infix:50 " ⇒• " => ParallelReduces
def cdev : Term -> Term
    | K => K
    | S => S
    | K ⊗ x ⊗ _ => cdev x
    | S ⊗ x ⊗ y ⊗ z => (cdev x) ⊗ (cdev z) ⊗ ((cdev y) ⊗ (cdev z))
    | f ⊗ x => (cdev f) ⊗ (cdev x)
theorem par_refl (t : Term) : t ⇒• t := by
    induction t with
        | K => exact ParallelReduces.K_refl
        | S => exact ParallelReduces.S_refl
        | App f x ihf ihx => exact ParallelReduces.app ihf ihx
theorem step_to_par {t s : Term} (h : t →¹ s) : t ⇒• s := by
    induction h with
        | K x y =>
            exact ParallelReduces.K_red (par_refl x) (par_refl y)
        | S x y z =>
            exact ParallelReduces.S_red (par_refl x) (par_refl y) (par_refl z)
        | appL h ih =>
            exact ParallelReduces.app ih (par_refl _)
        | appR h ih =>
            exact ParallelReduces.app (par_refl _) ih
theorem par_to_multi {t s : Term} (h : t ⇒• s) : t →• s := by
    induction h with
        | K_refl => exact Reduces.refl K
        | S_refl => exact Reduces.refl S
        | app _ _ ihf ihx =>
            exact Reduces.trans
                (combineRight ihf)
                (combineLeft ihx)
        | K_red _ _ ihx ihy =>
            rename_i x _ y _ _ _
            exact Reduces.trans (applyK x y) ihx
        | S_red _ _ _ ihuv ihwx ihyz =>
            rename_i u v w x y z _ _ _
            exact Reduces.trans
                (applyS u w y)
                (fuse (fuse ihuv ihyz) (fuse ihwx ihyz))
theorem par_to_cdev : ∀ (t : Term), t ⇒• cdev t
    | K => ParallelReduces.K_refl
    | S => ParallelReduces.S_refl
    | App (App K x) y =>
        ParallelReduces.K_red (par_to_cdev x) (par_to_cdev y)
    | App (App (App S x) y) z =>
        ParallelReduces.S_red (par_to_cdev x) (par_to_cdev y) (par_to_cdev z)
    | App K x =>
        ParallelReduces.app ParallelReduces.K_refl (par_to_cdev x)
    | App S x =>
        ParallelReduces.app ParallelReduces.S_refl (par_to_cdev x)
    | App (App S x) y =>
        ParallelReduces.app (par_to_cdev (S ⊗ x)) (par_to_cdev y)
    | App (App (App K x) y) z =>
        ParallelReduces.app (par_to_cdev (K ⊗ x ⊗ y)) (par_to_cdev z)
    | App (App (App (App f x) y) z) w =>
        ParallelReduces.app (par_to_cdev (f ⊗ x ⊗ y ⊗ z)) (par_to_cdev w)
theorem triangle_property {t s : Term} (h : t ⇒• s) : s ⇒• cdev t := by
    induction h with
        | K_refl => exact ParallelReduces.K_refl
        | S_refl => exact ParallelReduces.S_refl
        | K_red _ _ ihx _ => exact ihx
        | S_red _ _ _ ihx ihy ihz =>
            exact ParallelReduces.app
                (ParallelReduces.app ihx ihz)
                (ParallelReduces.app ihy ihz)
        | app hf hx ihf ihx =>
            rename_i f f' x x'
            match f, hf, ihf with
                | K, hf, ihf => exact ParallelReduces.app ihf ihx
                | S, hf, ihf => exact ParallelReduces.app ihf ihx
                | App S a, hf, ihf => exact ParallelReduces.app ihf ihx
                | App (App K a) b, hf, ihf => exact ParallelReduces.app ihf ihx
                | App (App (App f a) b) c, hf, ihf => exact ParallelReduces.app ihf ihx
                | App K a,
                    ParallelReduces.app ParallelReduces.K_refl ha,
                    ParallelReduces.app ParallelReduces.K_refl iha =>
                        exact ParallelReduces.K_red iha ihx
                | App (App S a) b,
                    ParallelReduces.app
                        (ParallelReduces.app ParallelReduces.S_refl ha) hb,
                    ParallelReduces.app
                        (ParallelReduces.app ParallelReduces.S_refl iha) ihb =>
                            exact ParallelReduces.S_red iha ihb ihx
theorem diamond_parallel {a b c : Term} (hab : a ⇒• b) (hac : a ⇒• c) :
    ∃ d, b ⇒• d ∧ c ⇒• d :=
        ⟨cdev a, triangle_property hab, triangle_property hac⟩
theorem strip {a b c : Term}
    (hab : a ⇒• b) (hac : a →• c) : ∃ d, b →• d ∧ c ⇒• d := by
        induction hac generalizing b with
            | refl _ => exact ⟨b, Reduces.refl b, hab⟩
            | step _ _ _ hxy hyz ih =>
                obtain ⟨d', hbd', hyd'⟩ := diamond_parallel hab (step_to_par hxy)
                obtain ⟨d, hd'd, hzd⟩ := ih hyd'
                exact ⟨d, Reduces.trans (par_to_multi hbd') hd'd, hzd⟩
/--
    The Church-Rosser property.
-/
theorem confluence {a b c : Term} (hab : a →• b) (hac : a →• c) :
    ∃ d : Term, b →• d ∧ c →• d := by
        induction hab generalizing c with
            | refl x => exact ⟨c, hac, Reduces.refl c⟩
            | step x y z hxy hyz ih =>
                obtain ⟨d', hyd', hcd'⟩ := strip (step_to_par hxy) hac
                obtain ⟨d, hzd, hd'd⟩ := ih hyd'
                exact ⟨d, hzd, Reduces.trans (par_to_multi hcd') hd'd⟩

end Term
