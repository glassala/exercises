import Mathlib.Tactic
set_option linter.style.docString false
set_option linter.style.openClassical false
/-

    Exercises from chapters 3-5 of Theorem Proving in Lean.

    Variants with and without tactics.

-/
section Propositions
variable (P Q R : Prop)

/--
    1. Commutativity of the ∧ operator.

    For goals in the "if and only if" form A ↔ B,
    use "apply Iff.intro" to split the goal into
    a "case mp => ⊢ A → B" and a "case mpr => ⊢ B → A."

    Note that "And.intro ha hb" is equivalent to "⟨ha, hb⟩."
-/
example : P ∧ Q ↔ Q ∧ P := Iff.intro
    (
        fun a : P ∧ Q =>
            ⟨And.right a, And.left a⟩
    ) (
        fun a : Q ∧ P =>
            ⟨And.right a, And.left a⟩
    )
example : P ∧ Q ↔ Q ∧ P := by -- exact And.comm
    apply Iff.intro
    case mp =>
        intro (a : P ∧ Q)
        exact ⟨And.right a, And.left a⟩
    case mpr =>
        intro (b : Q ∧ P)
        exact ⟨And.right b, And.left b⟩
/--
    2. Commutativity of the ∨ operator.
-/
example : P ∨ Q ↔ Q ∨ P := Iff.intro
    (
        fun u : P ∨ Q =>
            match u with
                | Or.inl (p : P) =>
                    Or.inr p
                | Or.inr (q : Q) =>
                    Or.inl q
    ) (
        fun u : Q ∨ P =>
            match u with
                | Or.inl (q : Q) =>
                    Or.inr q
                | Or.inr (p : P) =>
                    Or.inl p
    )
example : P ∨ Q ↔ Q ∨ P := by -- apply Or.comm
    apply Iff.intro
    case mp =>
        intro (u : P ∨ Q)
        have v : Q ∨ P :=
            match u with
                | Or.inl (p : P) =>
                    Or.inr p
                | Or.inr (q : Q) =>
                    Or.inl q
        exact v
    case mpr =>
        intro (u : Q ∨ P)
        have v : P ∨ Q :=
            match u with
                | Or.inl (q : Q) =>
                    Or.inr q
                | Or.inr (p : P) =>
                    Or.inl p
        exact v
/--
    3. Associativity of the ∧ operator.
-/
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := Iff.intro
    (
        fun a : (P ∧ Q) ∧ R =>
            ⟨
                And.left (And.left a),
                ⟨And.right (And.left a), And.right a⟩
            ⟩
    ) (
        fun a : P ∧ (Q ∧ R) =>
            ⟨
                ⟨And.left a, And.left (And.right a)⟩,
                And.right (And.right a)
            ⟩
    )
example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
    apply Iff.intro
    case mp =>
        intro (h : (P ∧ Q) ∧ R)
        have a : P ∧ Q :=
            And.left h
        exact ⟨And.left a, ⟨And.right a, And.right h⟩⟩
    case mpr =>
        intro (h : P ∧ Q ∧ R)
        have a : Q ∧ R :=
            And.right h
        exact ⟨⟨And.left h, And.left a⟩, And.right a⟩
/--
    4. Associativity of ∨.
-/
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := Iff.intro
    (
        fun u : (P ∨ Q) ∨ R =>
            match u with
                | Or.inl (u' : P ∨ Q) =>
                    match u' with
                        | Or.inl (p : P) =>
                            Or.inl p
                        | Or.inr (q : Q) =>
                            Or.inr (Or.inl q)
                | Or.inr (r : R) =>
                    Or.inr (Or.inr r)
    ) (
        fun u : P ∨ (Q ∨ R) =>
            match u with
                | Or.inl (p : P) =>
                    Or.inl (Or.inl p)
                | Or.inr (u' : Q ∨ R) =>
                    match u' with
                        | Or.inl q =>
                            Or.inl (Or.inr q)
                        | Or.inr r =>
                            Or.inr r

    )
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
    apply Iff.intro
    case mp =>
        intro (h : (P ∨ Q) ∨ R)
        have u : P ∨ (Q ∨ R) :=
            match h with
                | Or.inl (v : P ∨ Q) =>
                    match v with
                        | Or.inl (p : P) =>
                            Or.inl p
                        | Or.inr (q : Q) =>
                            Or.inr (Or.inl q)
                | Or.inr (r : R) =>
                    Or.inr (Or.inr r)
        exact u
    case mpr =>
        intro (h : P ∨ Q ∨ R)
        have u : (P ∨ Q) ∨ R :=
            match h with
                | Or.inl (p : P) =>
                    Or.inl (Or.inl p)
                | Or.inr (v : Q ∨ R) =>
                    match v with
                        | Or.inl (q : Q) =>
                            Or.inl (Or.inr q)
                        | Or.inr (r : R) =>
                            Or.inr r
        exact u
/--
    5. Distributivity of ∧ over ∨.
-/
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := Iff.intro
    (
        fun a : P ∧ (Q ∨ R) =>
            match a.right with
                | Or.inl (q : Q) =>
                    Or.inl ⟨a.left, q⟩
                | Or.inr (r : R) =>
                    Or.inr ⟨a.left, r⟩
    ) (
        fun u : P ∧ Q ∨ P ∧ R =>
            match u with
                | Or.inl (a : P ∧ Q) =>
                    ⟨a.left, Or.inl a.right⟩
                | Or.inr (b : P ∧ R) =>
                    ⟨b.left, Or.inr b.right⟩
    )
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
    apply Iff.intro
    case mp =>
        intro (h : P ∧ (Q ∨ R))
        have p : P := And.left h
        have u : P ∧ Q ∨ P ∧ R :=
            match And.right h with
                | Or.inl (q : Q) =>
                    Or.inl ⟨p, q⟩
                | Or.inr (r : R) =>
                    Or.inr ⟨p, r⟩
        exact u
    case mpr =>
        intro (h : P ∧ Q ∨ P ∧ R)
        match h with
            | Or.inl (a : P ∧ Q) =>
                exact ⟨And.left a, Or.inl (And.right a)⟩
            | Or.inr (a : P ∧ R) =>
                exact ⟨And.left a, Or.inr (And.right a)⟩
/--
    6. Distributivity of ∨ over ∧.
-/
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := Iff.intro
    (
        fun u : P ∨ Q ∧ R =>
            match u with
                | Or.inl (p : P) =>
                    ⟨Or.inl p, Or.inl p⟩
                | Or.inr (a : Q ∧ R) =>
                    ⟨Or.inr a.left, Or.inr a.right⟩
    ) (
        fun a : (P ∨ Q) ∧ (P ∨ R) =>
            match a.left with
                | Or.inl (p : P) =>
                    Or.inl p
                | Or.inr (q : Q) =>
                    match a.right with
                        | Or.inl (p : P) =>
                            Or.inl p
                        | Or.inr (r : R) =>
                            Or.inr ⟨q, r⟩
    )
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
    apply Iff.intro
    case mp =>
        intro (h : P ∨ Q ∧ R)
        match h with
            | Or.inl (p : P) =>
                exact ⟨Or.inl p, Or.inl p⟩
            | Or.inr (a : Q ∧ R) =>
                exact ⟨Or.inr (And.left a), Or.inr (And.right a)⟩
    case mpr =>
        intro (h : (P ∨ Q) ∧ (P ∨ R))
        match And.left h with
            | Or.inl (p : P) =>
                apply Or.inl p
            | Or.inr (q : Q) =>
                match And.right h with
                    | Or.inl (p : P) =>
                        apply Or.inl p
                    | Or.inr (r : R) =>
                        apply Or.inr ⟨q, r⟩
/--
    7.
-/
example : (P → Q → R) ↔ P ∧ Q → R := Iff.intro
    (
        fun f : P → Q → R =>
            fun a : P ∧ Q =>
                f a.left a.right
    ) (
        fun a : P ∧ Q → R =>
            fun p : P =>
                fun q : Q =>
                    a ⟨p, q⟩
    )
example : (P → Q → R) ↔ P ∧ Q → R := by
    simp only [and_imp] -- a ∧ b → c ↔ a → b → c
/--
    8.
-/
example : (P ∨ Q) → R ↔ (P → R) ∧ (Q → R) := Iff.intro
    (
        fun f : P ∨ Q → R =>
            ⟨
                fun p : P =>
                    f (Or.inl p),
                fun q : Q =>
                    f (Or.inr q)
            ⟩
    ) (
        fun a : (P → R) ∧ (Q → R) =>
            fun u : P ∨ Q =>
                match u with
                    | Or.inl (p : P) =>
                        a.left p
                    | Or.inr (q : Q) =>
                        a.right q
    )
example : (P ∨ Q) → R ↔ (P → R) ∧ (Q → R) := by
    apply Iff.intro
    case mp =>
        intro (h : P ∨ Q → R)
        have f : P → R := by
            intro (p : P)
            apply h
            exact Or.inl p
        have g : Q → R := by
            intro (q : Q)
            apply h
            exact Or.inr q
        exact ⟨f, g⟩
    case mpr =>
        intro (h : (P → R) ∧ (Q → R)) (u : P ∨ Q)
        match u with
            | Or.inl (p : P) =>
                apply And.left h p
            | Or.inr (q : Q) =>
                apply And.right h q
/--
    9.
-/
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := Iff.intro
    (
        fun n : ¬(P ∨ Q) =>
            ⟨
                fun p : P =>
                    n (Or.inl p),
                fun q : Q =>
                    n (Or.inr q)
            ⟩
    ) (
        fun a : ¬P ∧ ¬Q =>
            fun v : P ∨ Q =>
                match v with
                    | Or.inl (p : P) =>
                        a.left p
                    | Or.inr (q : Q) =>
                        a.right q
    )
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
    simp only [not_or] -- ¬(p ∨ q) ↔ ¬p ∧ ¬q
/--
    10.
-/
example : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
    fun u : ¬P ∨ ¬Q =>
        fun a : P ∧ Q =>
            match u with
                | Or.inl (np : ¬P) =>
                    np a.left
                | Or.inr (nq : ¬Q) =>
                    nq a.right
example : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
    intro (v : ¬P ∨ ¬Q)
    match v with
        | Or.inl (np : ¬P) =>
            intro (a : P ∧ Q)
            apply np a.left
        | Or.inr (nq : ¬Q) =>
            intro (a : P ∧ Q)
            apply nq a.right
/--
    11. Not (P and not P).

    Note that "a.right a.left" works and "a.left a.right" doesn't work,
    because the mechanism of proof is to use the fact that ¬P : P → False
    and apply ¬P to P to solve ⊢ False.
-/
example : ¬(P ∧ ¬P) :=
    fun a : P ∧ ¬P =>
        a.right a.left
example : ¬(P ∧ ¬P) := by
    simp only [
        and_not_self, -- ¬(a ∧ ¬a)
        not_false_eq_true -- (¬False) = True
    ]
/--
    12.

    The methodology behind this form of proof of negation is as follows.
    You have a "contradiction" function ¬P : P → Trash which throws a
    term of type P into the trash, and your goal is to construct
    such a term of P so that you can use this function to throw the term
    into the trash.
-/
example : P ∧ ¬Q → ¬(P → Q) :=
    fun a : P ∧ ¬Q =>
        fun f : P → Q =>
            a.right (f a.left)
example : P ∧ ¬Q → ¬(P → Q) := by
    simp only [
        Classical.not_imp, -- ¬(a → b) ↔ a ∧ ¬b
        imp_self -- a → a ↔ True
    ]
/-
    13.
-/
example : ¬P → (P → Q) :=
    fun n : ¬P =>
        fun p : P =>
            absurd p n
example : ¬P → (P → Q) := by
    intro (np : ¬P) (p : P)
    simp_all only [not_true_eq_false] -- (¬True) = False
/--
    14.
-/
example : (¬P ∨ Q) → (P → Q) :=
    fun u : ¬P ∨ Q =>
        fun p : P =>
            match u with
                | Or.inl n => absurd p n
                | Or.inr q => q
example : (¬P ∨ Q) → (P → Q) := by
    intro (v : ¬P ∨ Q) (p : P)
    simp_all only [
        not_true_eq_false, -- (¬True) = False
        false_or -- (False ∨ p) = p
    ]
/--
    15.
-/
example : P ∨ False ↔ P :=
    Iff.intro (
        fun u : P ∨ False =>
            match u with
                | Or.inl (p : P) =>
                    p
                | Or.inr (b : False) =>
                    False.elim b
    ) (
        fun p : P =>
            Or.inl p
    )
example : P ∨ False ↔ P := by
    simp only [or_false] -- (p ∨ False) = p
/--
    16.
-/
example : P ∧ False ↔ False := Iff.intro
    (
        fun h : P ∧ False =>
            absurd h And.right
    )
    (
        fun b : False =>
            False.elim b
    )
example : P ∧ False ↔ False := by
    simp only [and_false] -- (p ∧ False) = False
/--
    17.
-/
example : (P → Q) → (¬Q → ¬P) :=
    fun f : P → Q =>
        fun n : ¬Q =>
            fun p : P =>
                n (f p)
example : (P → Q) → (¬Q → ¬P) := by
    intro (f : P → Q) (nq : ¬Q)
    simp_all only [
        imp_false, -- a → False ↔ ¬a
        not_false_eq_true -- (¬False) = True
    ]
/--
    18. The law of the excluded middle.

    Assumed in classical logic, but not in constructive logic.
-/
example : P ∨ ¬P := Classical.em P
/--
    19.
-/
example : (P → Q ∨ R) → ((P → Q) ∨ (P → R)) :=
    fun f : P → Q ∨ R =>
        match Classical.em P with
            | Or.inl (p : P) =>
                match (f p) with
                    | Or.inl q =>
                        Or.inl (fun _ : P => q)
                    | Or.inr r =>
                        Or.inr (fun _ : P => r)
            | Or.inr (n : ¬P) =>
                Or.inl (fun p : P => absurd p n)
example : (P → Q ∨ R) → ((P → Q) ∨ (P → R)) := by
    intro (f : P → Q ∨ R)
    match Classical.em P with
        | Or.inl (p : P) =>
            match f p with
                | Or.inl (q : Q) =>
                    apply Or.inl (fun _ => q)
                | Or.inr (r : R) =>
                    apply Or.inr (fun _ => r)
        | Or.inr (n : ¬P) =>
            simp_all only [
                IsEmpty.forall_iff, -- [IsEmpty α] : (∀ (a : α), p a) ↔ True
                or_self -- (p ∨ p) = p
            ]
/--
    20.
-/
example : ¬(P ∧ Q) → ¬P ∨ ¬Q :=
    fun f : ¬(P ∧ Q) =>
        match Classical.em P with
            | Or.inl (p : P) =>
                Or.inr (fun q : Q => f ⟨p, q⟩)
            | Or.inr (n : ¬P) =>
                Or.inl n
example : ¬(P ∧ Q) → ¬P ∨ ¬Q := by
    simp
    match Classical.em P with
        | Or.inl (p : P) =>
            intro (f : P → ¬Q)
            apply Or.inr (f p)
        | Or.inr (n : ¬P) =>
                intro (f : P → ¬Q)
                apply Or.inl n
/--
    21.
-/
example : ¬(P → Q) → P ∧ ¬Q :=
    fun f : ¬(P → Q) =>
        match Classical.em P with
            | Or.inl (p : P) =>
                ⟨p, fun q : Q => f (fun _ : P => q)⟩
            | Or.inr (np : ¬P) =>
                absurd (fun p : P => absurd p np) f
example : ¬(P → Q) → P ∧ ¬Q := by
    simp only [
        Classical.not_imp, -- ¬(a → b) ↔ a ∧ ¬b
        imp_self -- a → a ↔ True
    ]
/--
    22.
-/
example : (P → Q) → (¬P ∨ Q) :=
    fun f : P → Q =>
        match Classical.em P with
            | Or.inl (p : P) =>
                Or.inr (f p)
            | Or.inr (n : ¬P) =>
                Or.inl n
example : (P → Q) → (¬P ∨ Q) := by
    intro (f : P → Q)
    match Classical.em P with
        | Or.inl (p : P) =>
            apply Or.inr (f p)
        | Or.inr (np : ¬P) =>
            apply Or.inl np
/--
    23.
-/
example : (¬Q → ¬P) → (P → Q) :=
    fun f : ¬Q → ¬P =>
        fun p : P =>
            match Classical.em Q with
                | Or.inl (q : Q) =>
                    (fun _ : P => q) p
                | Or.inr (nq : ¬Q) =>
                    absurd p (f nq)
example : (¬Q → ¬P) → (P → Q) := by
    intro (f : ¬Q → ¬P)  (p : P)
    simp_all only [
        not_true_eq_false,
        imp_false,
        not_not
    ]
/--
    24.
-/
example : ((P → Q) → P) → P :=
    fun h =>
        match Classical.em P with
            | Or.inl (p : P) =>
                p
            | Or.inr (n : ¬P) =>
                h (fun p : P => absurd p n)
example : (((P → Q) → P) → P) := by
    intro (f : (P → Q) → P)
    match Classical.em P with
        | Or.inl (p : P) =>
            exact p
        | Or.inr (n : ¬P) =>
            simp_all only [
                IsEmpty.forall_iff,
                imp_false, not_true_eq_false
            ]
/--
    25.
-/
example : ¬(P ↔ ¬P) :=
    fun ⟨(f : P → ¬P), (n : ¬P → P)⟩ =>
        (fun p : P => f p p) (n (fun p : P => f p p))
end Propositions
section Quantifiers
variable (α : Type) (P Q : α → Prop)
variable (R : Prop)
/--
    26.
-/
example : (∃ _ : α, R) → R :=
    fun a : ∃ _, R =>
        match a with
            | ⟨_, r⟩ =>
                r
example : (∃ _ : α, R) → R := by
    simp only [
        exists_const_iff, -- (∃ x, P) ↔ Nonempty α ∧ P
        and_imp, -- a ∧ b → c ↔ a → b → c
        imp_self, -- a → a ↔ True
        implies_true -- (∀ (a : α), True) = True
    ]
/--
    27.
-/
example (a : α) : R → (∃ _ : α, R) :=
    fun r =>
        ⟨a, r⟩
example (a : α) : R → (∃ _ : α, R) := by
    intro (_ : R)
    simp_all only [
        exists_const_iff, -- (∃ x, P) ↔ Nonempty α ∧ P
        and_true -- (p ∧ True) = p
    ]
    exact Nonempty.intro a
/--
    28.
-/
example : (∃ x, P x ∧ R) ↔ (∃ x, P x) ∧ R := Iff.intro
    (
        fun a : ∃ x, P x ∧ R =>
            match a with
                | ⟨x, ⟨p, r⟩⟩ =>
                    ⟨⟨x, p⟩, r⟩

    ) (
        fun ⟨(a : ∃ x, P x), (r : R)⟩ =>
            match a with
                | ⟨x, p⟩ =>
                    ⟨x, ⟨p, r⟩⟩
    )
example : (∃ x, P x ∧ R) ↔ (∃ x, P x) ∧ R := by
    simp only [
        exists_and_right -- (∃ x, p x ∧ b) ↔ (∃ x, p x) ∧ b
    ]
/--
    29.
-/
example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := Iff.intro
    (
        fun a : ∃ x, P x ∨ Q x =>
            match a with
                | ⟨x, u⟩ =>
                    match u with
                        | Or.inl (p : P x) =>
                            Or.inl ⟨x, p⟩
                        | Or.inr (q : Q x) =>
                            Or.inr ⟨x, q⟩
    ) (
        fun h' : (∃ x, P x) ∨ ∃ x, Q x =>
            match h' with
                | Or.inl ⟨x, p⟩ =>
                    ⟨x, Or.inl p⟩
                | Or.inr ⟨x, q⟩ =>
                    ⟨x, Or.inr q⟩
    )
example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
    aesop -- Try "aesop?"
/--
    30.
-/
example : (∀ x, P x) ↔ ¬(∃ x, ¬ P x) := Iff.intro
    (
        fun f : ∀ (x : α), P x =>
            fun a : ∃ x, ¬P x =>
                match a with
                    | ⟨x, p⟩ =>
                        p (f x)
    ) (
        fun a : ¬∃ x, ¬P x =>
            fun x : α =>
                Classical.byContradiction (
                    fun n =>
                        a ⟨x, n⟩
                )
    )
example : (∀ x, P x) ↔ ¬(∃ x, ¬P x) := by
    simp only [
        not_exists, -- (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
        not_not -- ¬¬a ↔ a
    ]
/--
    31.
-/
example : (∃ x, P x) ↔ ¬(∀ x, ¬ P x) := Iff.intro
    (
        fun a : ∃ x, P x =>
            fun f : ∀ (x : α), ¬P x =>
                match a with
                    | ⟨x, p⟩ =>
                        (f x) p
    ) (
        fun f : ¬∀ (x : α), ¬P x =>
            match Classical.em (∃ x, P x) with
                | Or.inl (a : ∃ x, P x) =>
                    a
                | Or.inr (na : ¬∃ x, P x) =>
                    have h' : ∀ x, ¬P x :=
                        fun x : α =>
                            fun p : P x =>
                                na ⟨x, p⟩
                    False.elim (f h')
    )
example : (∃ x, P x) ↔ ¬(∀ x, ¬P x) := by
    simp only [
        not_forall, -- (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
        not_not -- ¬¬a ↔ a
    ]
/--
    32.
-/
example : (¬∃ x, P x) ↔ ∀ x, ¬P x := Iff.intro (
    fun a : ¬∃ x, P x =>
        fun x : α =>
            match Classical.em (P x) with
                | Or.inl p =>
                    absurd ⟨x, p⟩ a
                | Or.inr n =>
                    fun p : P x =>
                        n p
) (
    fun f : ∀ (x : α), ¬P x =>
        fun a : ∃ x, P x =>
            match a with
                | ⟨x, p⟩ =>
                    f x p
)
example : (¬∃ x, P x) ↔ (∀ x, ¬P x) := by
    simp only [
        not_exists -- (¬∃ x, p x) ↔ ∀ (x : α), ¬p x
    ]
/--
    33.
-/
example : (¬∀ x, P x) ↔ (∃ x, ¬P x) := Iff.intro
    (
        fun n =>
            Classical.byContradiction (
                fun a : ¬(∃ x, ¬P x) =>
                    have f : ∀ x, P x :=
                        fun x : α =>
                            Classical.byContradiction (
                                fun n' =>
                                    absurd (Exists.intro x n') a
                            )
                    absurd f n
            )
    ) (
        fun n : ∃ x, ¬P x =>
            fun f : ∀ (x : α), P x =>
                match n with
                    | ⟨x, n'⟩ =>
                        absurd (f x) n'
    )
example : (¬ ∀ x, P x) ↔ (∃ x, ¬P x) := by
    simp only [
        not_forall -- (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
    ]
/--
    34.
-/
example : (∀ x, P x → R) ↔ (∃ x, P x) → R := Iff.intro
    (
        fun f :  ∀ (x : α), P x → R =>
            fun a : ∃ x, P x =>
                match a with
                    | ⟨x, p⟩ =>
                        f x p
    ) (
        fun a : (∃ x, P x) → R =>
            fun x : α =>
                fun p : P x =>
                    a ⟨x, p⟩
    )
example : (∀ x, P x → R) ↔ (∃ x, P x) → R := by
    simp only [
        forall_exists_index
    ]
/--
    35.
-/
example (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := Iff.intro
    (
        fun a : ∃ x, P x → R =>
            fun f : ∀ (x : α), P x =>
                match a with
                    | ⟨x, f'⟩ => f' (f x)
    ) (
        fun f : (∀ (x : α), P x) → R =>
            match Classical.em (∀ x, P x) with
                | Or.inl (r : ∀ (x : α), P x) =>
                    ⟨a, fun _ => f r⟩
                | Or.inr (np : ¬∀ (x : α), P x) =>
                    match Classical.not_forall.mp np with
                        | ⟨x, n⟩ =>
                            ⟨x, fun p => absurd p n⟩
    )
example (a : α) : (∃ x, P x → R) ↔ (∀ x, P x) → R := by
    apply Iff.intro
    case mp =>
        intro (f : ∃ x, P x → R) (g : ∀ (x : α), P x)
        simp_all only [
            forall_const, -- (∀ (a : α), b) ↔ b
            exists_const_iff -- (∃ x, P) ↔ Nonempty α ∧ P
        ]
    case mpr =>
        intro (f : (∀ (x : α), P x) → R)
        match Classical.em (∀ (x : α), P x) with
            | Or.inl (p : ∀ (x : α), P x) =>
                simp_all only [
                    implies_true, -- (∀ (a : α), True) = True
                    forall_const, -- (∀ (a : α), b) ↔ b
                    exists_const_iff, -- (∃ x, P) ↔ Nonempty α ∧ P
                    and_true -- (p ∧ True) = p
                ]
                apply Nonempty.intro a
            | Or.inr (np : ¬∀ (x : α), P x) =>
                simp_all only [
                    IsEmpty.forall_iff, -- [IsEmpty α] : (∀ (a : α), p a) ↔ True
                    not_forall -- (¬∀ (x : α), p x) ↔ ∃ x, ¬p x
                ]
                obtain ⟨w, h⟩ := np
                exact ⟨w, fun p : P w => absurd p h⟩
/--
    36.
-/
example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := Iff.intro
    (
        fun a : ∃ x, R → P x =>
            fun r : R =>
                match a with
                    | ⟨x, f⟩ =>
                        ⟨x, f r⟩
    ) (
        fun f => match Classical.em R with
            | Or.inl (r : R) =>
                match (f r) with
                    | ⟨x, p⟩ =>
                        ⟨x, fun _ : R => p⟩
            | Or.inr (nr : ¬R) =>
                ⟨a, fun r : R => absurd r nr⟩
    )
example (a : α) : (∃ x, R → P x) ↔ (R → ∃ x, P x) := by
    apply Iff.intro
    case mp =>
        intro (f : ∃ x, R → P x) (r : R)
        simp_all only [forall_const] -- (∀ (a : α), b) ↔ b
    case mpr =>
        intro (f : R → ∃ x, P x)
        match Classical.em R with
            | Or.inl (r : R) =>
                match f r with
                    | ⟨x, p⟩ =>
                        exact ⟨x, fun _ => p⟩
            | Or.inr (nr : ¬R) =>
                simp_all only [
                    IsEmpty.forall_iff, -- [IsEmpty α] : (∀ (a : α), p a) ↔ True
                    exists_const_iff, -- (∃ x, P) ↔ Nonempty α ∧ P)
                    and_true -- (p ∧ True) = p
                ]
                exact Nonempty.intro a
/--
    37.
-/
example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := Iff.intro (
    fun f : ∀ x, P x ∧ Q x =>
        ⟨
            fun x : α =>
                (f x).left,
            fun x : α =>
                (f x).right
        ⟩
) (
    fun f : (∀ x, P x) ∧ (∀ x, Q x) =>
        fun x : α =>
            ⟨f.left x, f.right x⟩
)
example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
    apply Iff.intro
    case mp =>
        intro (f : ∀ (x : α), P x ∧ Q x)
        simp_all only [
            implies_true,
            and_self
        ]
    case mpr =>
        intro (f : (∀ (x : α), P x) ∧ ∀ (x : α), Q x) (x : α)
        simp_all only [and_self] -- (p ∧ p) = p
/--
    38.
-/
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
    fun h : ∀ x, P x → Q x =>
        fun f : ∀ x, P x =>
            fun x : α =>
                (h x) (f x)
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
    intro (_ : ∀ (x : α), P x → Q x) (_ : ∀ (x : α), P x) (_ : α)
    simp_all only [forall_const] -- (∀ (a : α), b) ↔ b
/--
    39.
-/
example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
    fun f : (∀ x, P x) ∨ (∀ x, Q x) =>
        match f with
            | Or.inl (p : ∀ (x : α), P x) =>
                fun x : α =>
                    Or.inl (p x)
            | Or.inr (q : ∀ (x : α), Q x) =>
                fun x : α =>
                    Or.inr (q x)
example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
    intro (a : (∀ (x : α), P x) ∨ ∀ (x : α), Q x) (_ : α)
    cases a with
        | inl _ =>
            simp_all only [true_or]
        | inr _ =>
            simp_all only [or_true]
/--
    40.
-/
example : α → ((∀ _ : α, R) ↔ R) :=
    fun x : α => Iff.intro
        (
            fun f : ∀ (_ : α), R =>
                f x
        ) (
            fun r : R =>
                fun _ : α =>
                    r
        )
example : α → ((∀ _ : α, R) ↔ R) := by
    intro a
    apply Iff.intro
    case mp =>
        intro (f : ∀ (x : α), R)
        apply f
        exact a
    case mpr =>
        intro (_ : R) (_ : α)
        simp_all only
/--
    41.
-/
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := Iff.intro
    (
        fun f => match Classical.em R with
            | Or.inl (r : R) => Or.inr r
            | Or.inr (nr : ¬R) =>
                Or.inl (
                    fun x : α =>
                        match f x with
                            | Or.inl (p : P x) => p
                            | Or.inr (r : R) => absurd r nr
                )
    ) (
        fun a : (∀ (x : α), P x) ∨ R =>
            match a with
                | Or.inl (f : ∀ (x : α), P x) =>
                    fun x : α =>
                        Or.inl (f x)
                | Or.inr (r : R) =>
                    fun _ : α =>
                        Or.inr r
    )
example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R := by
    apply Iff.intro
    case mp =>
        intro (a : ∀ (x : α), P x ∨ R)
        match Classical.em R with
            | Or.inl (r : R) =>
                exact Or.inr r
            | Or.inr (nr : ¬R) =>
                simp_all only [
                    or_false, -- (p : Prop) : (p ∨ False) = p
                    implies_true -- {u} (α : Sort u) : (∀ (a : α), True) = True
                ]
    case mpr =>
        intro (v : (∀ (x : α), P x) ∨ R) (x : α)
        cases v with
            | inl =>
                simp_all only [
                    true_or -- (p : Prop) : (True ∨ p) = True
                ]
            | inr =>
                simp_all only [
                    or_true -- (p : Prop) : (p ∨ True) = True
                ]
/--
    42.
-/
example : (∀ x, R → P x) ↔ (R → ∀ x, P x) := Iff.intro
    (
        fun f : ∀ (x : α), R → P x =>
            fun r : R =>
                fun x : α =>
                    f x r
    ) (
        fun f : R → ∀ (x : α), P x =>
            fun x : α =>
                fun r : R =>
                    f r x
    )
example : (∀ x, R → P x) ↔ (R → ∀ x, P x) := by
    apply Iff.intro
    case mp =>
        intro (_ : ∀ (x : α), R → P x) (_ : R) (_ : α)
        simp_all only [forall_const] -- (∀ (a : α), b) ↔ b
    case mpr =>
        intro (_ : R → ∀ (x : α), P x) (_ : α) (_ : R)
        simp_all only [forall_const] -- (∀ (a : α), b) ↔ b
/--
    43.
-/
example (μ : Type) (β : μ) (α : μ → μ → Prop) (h : ∀ x : μ, α β x ↔ ¬α x x) : False :=
    (fun a : (α β β) => ((h β).mp a) a) ((h β).mpr
    (fun a : (α β β) => ((h β).mp a) a))
example (μ : Type) (β : μ) (α : μ → μ → Prop) (h : ∀ x : μ, α β x ↔ ¬α x x) : False := by
    have f := h β
    by_contra!
    have f' : ¬α β β := by
        intro a
        exact (f.mp a) a
    exact f' (f.mpr f')
end Quantifiers
