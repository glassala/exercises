import Mathlib.Tactic
set_option linter.style.docString false
/-

    Miniature replica of the natural numbers. Dated to around
    July-August 2025; conceived as a response to an exercise in
    *Theorem Proving in Lean 4* which was taken to the extreme.

    Eccentric and amateur in retrospect, perhaps, but left mostly as-is.

    -- Will Sweet

-/
section NaturalNumbers

inductive N where
    | zero : N
    | s : N -> N
deriving DecidableEq

namespace N

instance (n : ℕ) : OfNat N n where
    ofNat :=
        let rec fromLit : ℕ -> N
            | 0 => zero
            | n + 1 => s (fromLit n)
        fromLit n

def toLit : N -> ℕ
    | zero => 0
    | s n => (toLit n) + 1

instance : Repr N where
    reprPrec n _ := repr (n.toLit)

@[simp]
def add : N -> N -> N :=
    fun n m =>
        match n with
            | zero => m
            | s n => s (add n m)
instance : Add N where
    add := add

@[simp]
theorem s_add (n m : N) : n.s + m = (n + m).s := by
    rfl

@[simp]
theorem zero_add (n : N) : zero + n = n := by
    rfl

@[simp]
theorem add_zero (n : N) : n + zero = n := by
    induction n
    case zero =>
        rfl
    case s k ih =>
        rw [s_add, ih]

@[simp]
theorem s_plus_left (a b : N) : a.s + b = a + b.s := by
    simp_all only [s_add]
    induction a
    case zero =>
        simp only [zero_add]
    case s k ih =>
        simp_all only [s_add]

theorem s_plus_right (a b : N) : b + a.s = a.s + b := by
    induction b
    case zero =>
        rw [add_zero, zero_add]
    case s k ih =>
        simp_all only [s_add, s.injEq]
        rw [← s_add, s_plus_left]

@[simp]
theorem add_comm (a b : N) : a + b = b + a := by
    induction b
    case zero =>
        rw [zero_add, add_zero]
    case s k ih =>
        rw [s_plus_right]

@[simp]
theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
    induction a
    case zero =>
        simp only [add_comm, add_zero, zero_add]
    case s k ih =>
        rw [← add_comm, ← add_comm, s_add, s_add, ← s_plus_right]
        simp_all only [add_comm]
        rw [← s_add, add_comm]

@[simp]
theorem add_cancel (a b c : N) (h : a + c = b + c) : a = b := by
    induction c with
    | zero =>
        simp at h ⊢
        exact h
    | s c ih =>
        have hs : s (a + c) = s (b + c) := by
            rw [← s_add, ← s_add, s_plus_left, s_plus_left, h]
        simp at hs
        exact ih hs

theorem add_one (n : N) : n.s = n + zero.s := by
    induction n
    case zero =>
        apply zero_add
    case s k ih =>
        simp_all only [add_comm, s_add, zero_add]

@[simp]
def nsmul : ℕ -> N -> N :=
    fun k : ℕ =>
        fun n : N =>
            match k with
                | 0 => zero
                | k' + 1 => n + (nsmul k' n)

theorem nsmul_zero : ∀ (x : N), nsmul 0 x = 0 := by
    intro x
    simp_all only [nsmul]
    rfl

theorem nsmul_s : ∀ (n : ℕ) (x : N), nsmul (n + 1) x = nsmul n x + x := by
    intro n x
    simp_all only [nsmul, add_comm]

instance : AddMonoid N where
    add_assoc := add_assoc
    zero := zero
    zero_add := zero_add
    add_zero := add_zero
    nsmul := nsmul
    nsmul_zero := nsmul_zero
    nsmul_succ := nsmul_s

@[simp]
def mul : N -> N -> N :=
    fun a b =>
        match a with
            | zero => zero
            | s a => b + (mul a b)

@[simp]
instance : Mul N where
    mul := mul

@[simp]
theorem zero_mul (n : N) : zero * n = zero := by
    rfl

@[simp]
theorem mul_zero (n : N) : n * zero = zero := by
    induction n
    case zero =>
        rfl
    case s k ih =>
        exact ih

@[simp]
theorem one_mul (n : N) : (s zero) * n = n := by
    induction n
    case zero =>
        simp only [instMul, mul_zero]
    case s a ih =>
        have : ((zero.s) * a).s = a.s := by rw [ih]
        exact this

@[simp]
theorem mul_one (n : N) : n * (s zero) = n := by
    induction n
    case zero =>
        simp only [instMul, zero_mul]
    case s k ih =>
        have : (k * zero.s).s = k.s := by rw [ih]
        exact this

@[simp]
theorem s_mul (a b : N) : a.s * b = a * b + b := by
    simp_all only [instMul, add_comm]
    rfl

@[simp]
theorem mul_s (a b : N) : a * b.s = a * b + a := by
    induction a
    case zero => rfl
    case s a ih =>
        simp_all only [instMul, s_mul, add_assoc]
        rw [add_comm, add_comm, s_plus_right, s_plus_left]

@[simp]
theorem mul_comm (a b : N) : a * b = b * a := by
    induction a
    case zero =>
        simp only [instMul, zero_mul, mul_zero]
    case s a ih =>
        calc
            a.s * b = a * b + b := by
                rw [s_mul]
            _ = b * a + b := by
                rw [ih]
            _ = b * a.s := by
                simp_all
@[simp]
theorem mul_dist_add (a b c : N) : a * (b + c) = a * b + a * c := by
    induction a
    case zero => rfl
    case s a ih =>
        calc
            a.s * (b + c) = (a * (b + c)) + (b + c) := by simp
            _ = a * b + a * c + b + c := by
                simp_all only [add_assoc]
            _ = a * b + b + a * c + c := by
                simp only [instMul, mul_comm, add_comm, add_assoc]
            _ = a.s * b + a.s * c := by
                simp_all only [s_mul a, add_assoc]

@[simp]
theorem mul_assoc (a b c : N) : a * b * c = a * (b * c) := by
    induction a
    case zero => rfl
    case s a ih =>
        simp_all

instance : Monoid N where
    one := s zero
    one_mul := one_mul
    mul_one := mul_one
    mul_assoc := mul_assoc

def pow : N -> N -> N :=
    fun a b =>
        match b with
            | zero => zero.s
            | s b => a * (pow a b)
instance : Pow N N where
    pow := pow

@[simp]
theorem pow_zero (n : N) : n ^ zero = zero.s := by
    rfl

@[simp]
theorem zero_pow_zero : zero ^ zero = zero.s := by
    rfl

@[simp]
theorem zero_pow (n : N) : zero ^ n.s = zero := by
    induction n
    case zero => rfl
    case s k ih => rfl

@[simp]
theorem next_pow (a b : N) : a ^ (s b) = (a ^ b) * a := by
    simp_all only [instMul, mul_comm]
    rfl

@[simp]
theorem one_pow (n : N) : zero.s ^ n = zero.s := by
    induction n
    case zero =>
        simp only [pow_zero]
    case s n ih =>
        rw [next_pow, ih, one_mul]

@[simp]
theorem pow_one (n : N) : n ^ zero.s = n := by
    simp only [next_pow, instMul, pow_zero, mul_comm,
        mul_s, mul_zero, add_comm, add_zero]

theorem map_pow (n a b : N) : (n ^ a) * (n ^ b) = n ^ (a + b) := by
    induction a
    case zero =>
        rw [pow_zero, one_mul, zero_add]
    case s k ih =>
        have h' (x : N) : x * (n ^ k * n) = x * n ^ k * n := by
            rw [mul_assoc]
        rw [mul_comm] at ih
        rw [next_pow, mul_comm, h', ih, s_add, next_pow]

@[simp, reducible]
def compare : N -> N -> Ordering
    | zero, zero => .eq
    | zero, s _ => .lt
    | s _, zero => .gt
    | s a, s b => compare a b

instance : Ord N where
    compare := compare

instance : LT N where
    lt := fun a b => compare a b = .lt

instance : LE N where
    le := fun a b => (compare a b = .lt) ∨ (compare a b = .eq)

@[simp]
theorem not_lt_zero (a : N) : ¬ a < zero := by
    intro h
    reduce at h
    induction a
    case zero =>
        have : zero.compare zero = Ordering.eq := by rfl
        contradiction
    case s k ih =>
        simp_all only [imp_false, compare, reduceCtorEq]

@[simp]
theorem lt_s (n : N) : n < n.s := by
    induction n
    case zero =>
        reduce
        rfl
    case s k ih =>
        change compare (s k) (s (s k)) = Ordering.lt
        rw [compare]
        exact ih

@[simp]
theorem lt_irrefl (a : N) : ¬ a < a := by
    induction a
    case zero =>
        apply not_lt_zero
    case s a ih =>
        exact ih

@[simp]
theorem lt_implies_lt_s (a b : N) (h : a < b) : a.s < b.s := by
    exact h

@[simp]
theorem lt_s_implies_lt (a b : N) (h : a.s < b.s) : a < b := by
    exact h

@[simp]
theorem zero_lt (n : N) : zero < n.s := by
    induction n
    case zero =>
        exact lt_s zero
    case s k ih =>
        exact ih

@[simp]
theorem lt_trans (a b c : N) (g : a < b) (f : b < c) : a < c := by
    induction c generalizing a b
    case zero =>
        exfalso
        exact not_lt_zero b f
    case s c ih =>
        cases b
        case zero =>
            exfalso
            exact not_lt_zero a g
        case s b =>
            cases a
            case zero =>
                simp
            case s a =>
                exact ih a b g f

@[simp]
theorem lt_s_lt (a b : N) (h : a.s < b) : a < b := by
    have h' : a < s a := by simp
    induction b generalizing a
    case zero =>
        exfalso
        simp_all only [not_lt_zero]
    case s b ih =>
        cases a
        case zero =>
            apply zero_lt
        case s a =>
            simp_all only [lt_s, lt_s_implies_lt, gt_iff_lt, forall_const]
            apply ih
            simp_all only [lt_s_implies_lt]

@[simp]
theorem lt_asymm (a b : N) (h : a < b) : ¬ b < a := by
    induction a generalizing b
    case zero =>
        intro h'
        exact not_lt_zero b h'
    case s k ih =>
        cases b
        case zero =>
            exfalso
            exact not_lt_zero (s k) h
        case s b =>
            intro h'
            exact ih b h h'
/--
    41.
-/
@[simp]
theorem lt_trichotomous (a b : N) : a < b ∨ a = b ∨ b < a := by
    induction a generalizing b
    case zero =>
        simp
        cases b
        case zero =>
            apply Or.inr
            rfl
        case s b =>
            apply Or.inl
            exact zero_lt zero
    case s a ih =>
        cases b
        case zero =>
            simp only [not_lt_zero, reduceCtorEq, zero_lt, lt_implies_lt_s,
                lt_s_implies_lt, or_true]
        case s b =>
            simp_all only [s.injEq]
            exact ih b

@[simp]
instance : IsStrictTotalOrder N LT.lt where
    irrefl := lt_irrefl
    trans := lt_trans
    trichotomous := lt_trichotomous

@[simp]
theorem compare_eq (a b : N) (h : a.compare b = Ordering.eq) : a = b := by
    induction a generalizing b
    case zero =>
        cases b
        case zero => rfl
        case s _ => contradiction
    case s k ih =>
        cases b
        case zero => contradiction
        case s b =>
            simp_all only [compare, s.injEq]
            apply ih
            simp_all

@[simp]
theorem eq_symm (a b : N) (h : a = b) : b = a := by
    subst h
    simp_all only

@[simp]
theorem eq_trans (a b c : N) (g : a = b) (f : b = c) : a = c := by
    subst f g
    rfl

@[simp]
theorem zero_le (n : N) : zero ≤ n := by
    induction n
    case zero =>
        reduce
        apply Or.inr
        rfl
    case s k ih =>
        reduce
        apply Or.inl
        rfl

@[simp]
theorem le_implies_le_s (a b : N) (h : a ≤ b) : a.s ≤ b.s := by
    exact h

@[simp]
theorem not_le_zero (n : N) : ¬ n.s ≤ zero := by
    intro h
    induction n
    case zero =>
        have h' : zero.s ≠ zero := by
            intro hn
            contradiction
        have hn : ¬ zero.s < zero := by simp
        cases h with
            | inl hl => apply hn hl
            | inr _ => contradiction
    case s k ih => contradiction

@[simp]
theorem le_zero_eq_zero (a : N) (h : a ≤ zero) : a = zero := by
    induction a
    case zero =>
        rfl
    case s a ih =>
        exfalso
        apply not_le_zero a
        exact h

@[simp]
theorem le_refl (a : N) : a ≤ a := by
    induction a
    case zero =>
        reduce
        apply Or.inr
        rfl
    case s k ih =>
        apply le_implies_le_s k k ih

@[simp]
theorem le_antisymm (a b : N) (h : a ≤ b) (h' : b ≤ a) : a = b := by
    cases h with
        | inl lt =>
            change a < b at lt
            have n : ¬ b < a := by
                apply lt_asymm
                exact lt
            cases h' with
                | inl lt' =>
                    change b < a at lt'
                    exfalso
                    apply n lt'
                | inr eq =>
                    have eq' : b = a := by
                        apply compare_eq ; exact eq
                    apply eq_symm
                    exact eq'
        | inr eq =>
            cases h' with
                | inl lt =>
                    apply compare_eq
                    exact eq
                | inr eq' =>
                    apply compare_eq
                    exact eq

@[simp]
theorem le_trans (a b c : N) (g : a ≤ b) (f : b ≤ c) : a ≤ c := by
    induction c generalizing b a
    case zero =>
        cases b
        case zero => exact g
        case s b =>
            cases a
            case zero =>
                exact le_refl zero
            case s a =>
                have h' : ¬b.s ≤ zero := by
                    exact not_le_zero zero
                exfalso
                apply h' f
    case s c ih =>
        cases b
        case zero =>
            have h : a = zero := by
                apply le_zero_eq_zero
                exact g
            rw [h]
            exact f
        case s b =>
            cases a
            case zero =>
                exact zero_le c.s
            case s a =>
                exact ih a b g f

@[simp]
theorem le_total (a b : N) : a ≤ b ∨ b ≤ a := by
    induction a generalizing b
    case zero =>
        apply Or.inl
        exact zero_le b
    case s a ih =>
        cases b
        case zero =>
            apply Or.inr
            exact zero_le a.s
        case s b =>
            exact ih b

@[simp]
theorem if_lt_le (a b : N) (h : a < b) : a ≤ b := by
    induction a generalizing b
    case zero =>
        exact zero_le b
    case s a ih =>
        cases b
        case zero =>
            exfalso
            apply not_lt_zero a.s
            exact h
        case s b =>
            apply ih
            apply lt_s_implies_lt
            exact h

@[simp]
theorem if_lt_not_eq (a b : N) (h : a < b) : a ≠ b := by
    simp_all only [ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro eq
    subst eq
    simp_all only [lt_irrefl]

@[simp]
theorem if_lt_not_ge (a b : N) (h : a < b) : ¬ b ≤ a := by
    have h' : a ≤ b := by
        apply if_lt_le
        exact h
    intro n
    have eq : a = b := by
        apply le_antisymm
        exact h' ; exact n
    have neq : a ≠ b := by
        apply if_lt_not_eq
        exact h
    contradiction

@[simp]
theorem if_neq_zero_gt_zero (a : N) (h : a ≠ zero) : zero < a := by
    induction a
    case zero =>
        contradiction
    case s a ih =>
        apply zero_lt

@[simp]
theorem if_le_and_not_ge_lt (a b : N) (h : a ≤ b) (h' : ¬ b ≤ a) : a < b := by
    induction a generalizing b
    case zero =>
        simp_all only [zero_le]
        have f : b ≠ zero := by
            simp_all only [ne_eq]
            apply Aesop.BuiltinRules.not_intro
            intro c
            subst c
            simp_all only [le_refl, not_true_eq_false]
        apply if_neq_zero_gt_zero
        exact f
    case s a ih =>
        cases b
        case zero =>
            exfalso
            apply not_le_zero a
            exact h
        case s b =>
            apply ih b
            · exact h
            exact h'

@[simp]
theorem compare_eq_compare : ∀ (a b : N), Ord.compare a b = compareOfLessAndEq a b := by
    intro a b
    induction a generalizing b
    case zero =>
        cases b
        case zero =>
            rfl
        case s b =>
            rfl
    case s a ih =>
        cases b
        case zero =>
            rfl
        case s b =>
            rw [compareOfLessAndEq]
            simp [Ord.compare, compare]
            exact ih b

instance : DecidableLE N :=
    fun a b =>
        match h : compare a b with
            | Ordering.lt =>
                isTrue (Or.inl h)
            | Ordering.eq =>
                isTrue (Or.inr h)
            | Ordering.gt =>
                isFalse (by
                    intro hle
                    cases hle with
                    | inl hlt =>
                        have : compare a b = Ordering.lt := hlt
                        rw [h] at this
                        simp at this
                    | inr heq =>
                        have : compare a b = Ordering.eq := heq
                        rw [h] at this
                        simp at this
                )

@[simp]
theorem le_sum (a b : N) : a ≤ a + b := by
    induction a
    case zero =>
        rw [zero_add]
        simp only [zero_le]
    case s k ih =>
        exact ih

theorem le_times_nonzero (a b : N) : a ≤ a * b.s := by
    induction a generalizing b
    case zero =>
        rw [zero_mul]
        apply zero_le
    case s a ih =>
        cases b
        case zero =>
            rw [mul_one]
            simp [le_refl]
        case s b =>
            simp_all only [
                instMul,
                mul_s,
                add_comm,
                eq_symm,
                le_sum,
                implies_true,
                mul_comm,
                add_assoc,
                s_add,
                le_implies_le_s
            ]

instance : LinearOrder N where
    le_refl := le_refl
    le_antisymm := le_antisymm
    le_trans := le_trans
    le_total := le_total
    lt_iff_le_not_ge := fun a b => by
        apply Iff.intro
        case mp =>
            intro le
            exact ⟨if_lt_le a b le, if_lt_not_ge a b le⟩
        case mpr =>
            exact And.rec (if_le_and_not_ge_lt a b)
    compare_eq_compareOfLessAndEq := compare_eq_compare
    toDecidableLE := inferInstance

def pre (n : N) :=
    match n with
        | zero => zero
        | s k => k

@[simp]
def sub (a b : N) :=
    match a with
        | zero => zero
        | s a' =>
            match b with
                | zero => a
                | s b' => sub a' b'
instance : Sub N where
    sub := sub

@[simp]
theorem sub_zero (n : N) : n - zero = n := by
    induction n
    case zero =>
        rfl
    case s n ih =>
        rfl

@[simp]
theorem zero_sub (n : N) : zero - n = zero := by
    rfl

@[simp]
theorem sub_self (n : N) : n - n = zero := by
    induction n
    case zero =>
        rw [sub_zero]
    case s n ih =>
        exact ih

theorem s_sub_one (n : N) : n.s - zero.s = n := by
    induction n with
    | zero =>
        rw [sub_self]
    | s n ih =>
        rw [show zero.s = s zero from rfl]
        rfl

@[simp]
theorem sub_eq_sub_s (a b c : N) (h : a - b = c) : a.s - b.s = c := by
    induction b generalizing a
    case zero =>
        rw [s_sub_one]
        subst c
        rw [show a - zero = a from sub_zero a]
    case s b ih =>
        cases a
        case zero =>
            simp [zero_sub] at h ⊢
            exact h
        case s a =>
            exact ih a h

@[simp]
theorem sub_le (a b : N) : a - b ≤ a := by
    induction b generalizing a
    case zero =>
        rw [sub_zero]
    case s b ih =>
        cases a
        case zero =>
            rw [zero_sub]
        case s a =>
            have h : a - b = a.s - b.s := by
                rw [sub_eq_sub_s]
                rfl
            have h' : a ≤ a.s := by
                simp
            rw [← h]
            exact le_trans (a - b) a a.s (ih a) h'

@[simp]
theorem sub_le_s_sub (a b : N) : a - b ≤ a.s - b := by
    induction b generalizing a
    case zero =>
        repeat rw [sub_zero]
        simp only [lt_s, lt_s_implies_lt, if_lt_le]
    case s b ih =>
        cases a
        case zero =>
            rw [zero_sub]
            simp [zero_le]
        case s a =>
            have h : a - b = a.s - b.s := by
                rw [sub_eq_sub_s]
                rfl
            have h' : a.s - b = s (a.s) - b.s := by
                rw [sub_eq_sub_s]
                rfl
            rw [← h, ← h']
            exact ih a

@[simp]
theorem sub_s_le_sub (a b : N) : a - b.s ≤ a - b := by
    induction a
    case zero =>
        rfl
    case s a ih =>
        have h : a - b = a.s - b.s := by
            rw [sub_eq_sub_s]
            rfl
        rw [← h]
        exact sub_le_s_sub a b

@[simp]
theorem sub_s_lt (a b c : N) (h : a.s - b < c) : a.s - b.s < c := by
    induction b
    case zero =>
        rw [s_sub_one]
        rw [sub_zero] at h
        have : a < a.s := by
            simp only [lt_s, lt_s_implies_lt]
        exact lt_trans a a.s c this h
    case s b ih =>
        have : a - b.s = a.s - b.s.s := by
            rw [sub_eq_sub_s] ; rfl
        rw [← this]
        have h' : a - b = a.s - b.s := by
            rw [sub_eq_sub_s] ; rfl
        have h1 : a - b < c := by
            rw [h'] ; exact h
        have h2 : a - b.s ≤ a - b := by
            exact sub_s_le_sub a b
        rcases le_iff_eq_or_lt.mp h2
        case inl heq =>
            rw [heq] ; exact h1
        case inr hlt =>
            exact lt_trans (a - b.s) (a - b) c hlt h1

@[simp]
theorem sub_lt (a b : N) (ha : a ≠ zero) (hb : b ≠ zero) : a - b < a := by
    induction b generalizing a
    case zero =>
        contradiction
    case s b ih =>
        cases a
        case zero =>
            contradiction
        case s a =>
            by_cases hb_zero : b = zero
            case pos =>
                rw [hb_zero]
                rw [s_sub_one]
                simp only [lt_s, lt_s_implies_lt]
            case neg =>
                rw [← ne_eq] at hb_zero
                have ih' : a.s - b < a.s := by
                    exact ih a.s ha hb_zero
                exact sub_s_lt a b a.s ih'

@[simp]
theorem sub_twice_lt (a b : N) (hb : b ≠ 0) (hc : a - b ≠ 0) : a - b - b < a - b := by
    induction a generalizing b
    case zero =>
        contradiction
    case s a ih =>
        cases b
        case zero =>
            contradiction
        case s b =>
            have h : a - b = a.s - b.s := by
                rw [sub_eq_sub_s] ; rfl
            rw [← h]
            apply sub_lt
            case ha =>
                exact hc
            case hb =>
                exact hb

def dvd (a b : N) := ∃ (c : N), b = a * c

theorem one_dvd (n : N) : dvd zero.s n := by
    induction n
    case zero =>
        unfold dvd
        apply Exists.intro zero
        rw [mul_zero]
    case s k ih =>
        unfold dvd
        apply Exists.intro k.s
        rw [one_mul]

theorem dvd_zero (n : N) : dvd n zero := by
    induction n
    case zero =>
        unfold dvd
        apply Exists.intro zero
        rw [zero_mul]
    case s n ih =>
        unfold dvd
        apply Exists.intro zero
        rw [mul_zero]

theorem zero_not_dvd (n : N) : ¬ dvd zero n.s := by
    unfold dvd
    have h (k : N) : zero = zero * k := by
        rw [zero_mul]
    induction n
    case zero =>
        intro h'
        obtain ⟨c, pc⟩ := h'
        contradiction
    case s n ih =>
        intro h'
        obtain ⟨c, pc⟩ := h'
        contradiction

theorem dvd_le (a b : N) (h : dvd a b) (nb : b ≠ zero) : a ≤ b := by
    unfold dvd at h
    obtain ⟨c, hc⟩ := h
    cases c
    case zero =>
        exfalso
        apply nb
        rw [hc]
        rw [mul_zero]
    case s c =>
        have : a * c.s = a + a * c := by
            rw [mul_s]
            simp
        rw [this] at hc
        have : a ≤ a + a * c := le_sum a (a * c)
        rw [← hc] at this
        exact this

theorem dvd_refl (a : N) : dvd a a := by
    unfold dvd
    apply Exists.intro zero.s
    rw [mul_one]

theorem dvd_antisymm (a b : N) (h : dvd a b) (h' : dvd b a) : a = b := by
    induction a generalizing b
    case zero =>
        cases b
        case zero =>
            rfl
        case s b =>
            have : ¬ dvd zero b.s := by
                apply zero_not_dvd
            contradiction
    case s a ih =>
        cases b
        case zero =>
            have : ¬ dvd zero a.s := by
                apply zero_not_dvd
            contradiction
        case s b =>
            have f : a.s ≠ zero := by
                simp
            have g : b.s ≠ zero := by
                simp
            have ha : a.s ≤ b.s := by
                apply dvd_le
                case h =>
                    exact h
                case nb =>
                    exact g
            have hb : b.s ≤ a.s := by
                apply dvd_le
                case h =>
                    exact h'
                case nb =>
                    exact f
            exact le_antisymm a.s b.s ha hb

theorem dvd_trans (a b c : N) (h : dvd a b) (h' : dvd b c) : dvd a c := by
    unfold dvd at *
    obtain ⟨c, pc⟩ := h
    obtain ⟨d, pd⟩ := h'
    rw [pc] at pd
    simp only [pd]
    let c' := c * d
    apply Exists.intro c'
    unfold c'
    rw [mul_assoc]

end N
end NaturalNumbers
