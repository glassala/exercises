import Mathlib.Tactic
set_option linter.style.docString false
section Lists
/-
    Notation in the form [a, b, c] is fairly tightly
    connected to Lean's native List type, so we will use
    {a, b, c} and suspend our disbelief at this notation
    signifying an *ordered* collection.
-/
variable {α β γ : Type*}
universe u
inductive L (α : Type*) where
    | nil : L α
    | cons : α -> L α -> L α
deriving Repr, BEq
namespace L
instance : EmptyCollection (L α) :=
    ⟨nil⟩
instance : Singleton α (L α) :=
    ⟨
        fun x : α =>
            cons x nil
    ⟩
instance : Insert α (L α) :=
    ⟨
        fun x : α =>
            fun xs : L α =>
                cons x xs
    ⟩
/-

    (++)

-/
/--
    1.
-/
@[simp]
def append : L α -> L α -> L α
    | nil, ys => ys
    | cons x xs, ys => cons x (append xs ys)
instance : Append (L α) where
    append := append
/--
    2.
-/
@[simp]
theorem nil_append (as : L α) : append nil as = as := by
    rfl
/--
    3.
-/
@[simp]
theorem append_nil (as : L α) : append as nil = as := by
    induction as
    case nil =>
        apply nil_append
    case cons a as ih =>
        rw [append, ih]
/--
    4.
-/
@[simp]
theorem cons_append (a : α) (as bs : L α) : append (cons a as) bs = cons a (append as bs) := by
    rfl
/--
    5.
-/
@[simp]
theorem append_assoc (as bs cs : L α) :
    append (append as bs) cs = append as (append bs cs) := by
        induction as
        case nil =>
            apply nil_append
        case cons a as ih =>
            simp_all only [append]
/--
    6.
-/
def nsmul : ℕ -> L α -> L α :=
    fun n xs =>
        match n with
            | 0 =>
                nil
            | k + 1 =>
                xs ++ nsmul k xs
/--
    7.
-/
theorem nsmul_zero (x : L α) : nsmul 0 x = nil := by
    rfl
/--
    8.
-/
theorem nsmul_one (xs : L α) : nsmul 1 xs = xs := by
    unfold nsmul
    change append xs (nsmul 0 xs) = xs
    rw [nsmul_zero, append_nil]
/--
    9.
-/
theorem nsmul_succ (n : ℕ) (xs : L α) : nsmul (n + 1) xs = nsmul n xs ++ xs := by
    induction n
    case zero =>
        simp_all only [zero_add, nsmul_zero]
        change nsmul 1 xs = append nil xs
        rw [nil_append, nsmul_one]
    case succ k ih =>
        unfold nsmul
        rw [ih]
        change append xs (append (nsmul k xs) xs) = append (append xs (nsmul k xs)) xs
        simp [append_assoc]
/--
    10.
-/
instance : AddMonoid (L α) where
    add := append
    add_assoc := append_assoc
    zero := nil
    zero_add := nil_append
    add_zero := append_nil
    nsmul := nsmul
    nsmul_zero := nsmul_zero
    nsmul_succ := nsmul_succ
/--
    11.
-/
@[simp]
def length : L α -> ℕ :=
    fun xs =>
        match xs with
            | nil =>
                0
            | cons _ xs =>
                1 + length xs
/--
    12.
-/
@[simp]
theorem nil_length : length (nil : L α) = 0 := by
    rfl
/--
    13.
-/
@[simp]
theorem singleton_length (x : α) : length (cons x nil) = 1 := by
    rfl
/--
    14.
-/
@[simp]
theorem cons_length (x : α) (xs : L α) : length (cons x xs) = length xs + 1 := by
    simp_all [length, add_comm]
/--
    15.
-/
theorem append_length_sum (as bs : L α) : length (as ++ bs) = length as + length bs := by
    induction as
    case nil =>
        change (append nil bs).length = nil.length + bs.length
        rw [nil_append]
        simp
    case cons a as ih =>
        have h1 : (cons a as) ++ bs = cons a (as ++ bs) := by rfl
        calc
            length ((cons a as) ++ bs) = length (cons a (as ++ bs)) := by rw [h1]
            _ = length (as ++ bs) + 1 := by simp_all only [length, add_comm]
            _ = (length as + length bs) + 1 := by rw [ih]
            _ = length as + (length bs + 1) := by rw [add_assoc]
            _ = length as + (1 + length bs) := by rw [add_comm (length bs) 1]
            _ = (length as + 1) + length bs := by rw [add_assoc]
            _ = length (cons a as) + length bs := by simp_all only [length, add_comm]
/--
    16.
-/
@[simp]
def reverse : L α -> L α :=
    fun xs =>
        match xs with
            | nil =>
                nil
            | cons x xs => reverse xs ++ {x}
/--
    17.
-/
@[simp]
theorem reverse_cons (x : α) (xs : L α) : reverse (xs ++ {x}) = cons x (reverse xs) := by
    induction xs
    case nil =>
        rfl
    case cons a as ih =>
        calc
            reverse ((cons a as) ++ {x}) = reverse (cons a (as ++ {x})) := by rfl
            _ = reverse (as ++ {x}) ++ {a} := by rfl
            _ = (cons x (reverse as)) ++ {a} := by rw [ih]
            _ = cons x (reverse as ++ {a}) := by rfl
            _ = cons x (reverse (cons a as)) := by rfl
/--
    18.
-/
@[simp]
theorem reverse_reverse (xs : L α) : reverse (reverse xs) = xs := by
    induction xs
    case nil =>
        rfl
    case cons x xs ih =>
        simp_all only [reverse, reverse_cons]
/--
    19.
-/
theorem reverse_length (xs : L α) : length (reverse xs) = length xs := by
    induction xs
    case nil =>
        rfl
    case cons a as ih =>
        simp_all only [reverse, length]
        rw [append_length_sum]
        simp [ih, add_comm]
/-

    (<$>)

-/
/--
    20.
-/
@[simp]
def map : (α -> β) -> L α -> L β :=
    fun f xs =>
        match xs with
            | nil =>
                nil
            | cons x xs => cons (f x) (map f xs)
/--
    21.
-/
instance : Functor L where
    map := map
/--
    22.
-/
@[simp]
theorem id_map (xs : L α) : id <$> xs = xs := by
    induction xs
    case nil =>
        rfl
    case cons a as ih =>
        unfold id
        simp_all [Functor.map]
        exact ih
/--
    23.
-/
@[simp]
theorem comp_map {α β γ : Type u} (g : α -> β) (h : β -> γ) (xs : L α) :
    (h ∘ g) <$> xs = h <$> g <$> xs := by
        induction xs with
            | nil =>
                rfl
            | cons x xs ih =>
                simp [Functor.map]
                exact ih
/--
    24.
-/
instance : LawfulFunctor L where
    id_map := id_map
    comp_map := comp_map
    map_const := by
        intro α β
        funext x xs
        simp [Functor.mapConst, Function.comp]
        rfl
/--
    25.
-/
def filter : (α -> Bool) -> L α -> L α :=
    fun P xs =>
        match xs with
            | nil =>
                nil
            | cons x xs =>
                match P x with
                    | true => cons x (filter P xs)
                    | _ => filter P xs
/--
    26.

    Filter 2, now featuring dependent types.
-/
def subtypeFilter (P : α -> Prop) [DecidablePred P] : L α -> L {x // P x}
    | nil =>
        nil
    | cons x xs =>
        if h : P x then
            cons ⟨x, h⟩ (subtypeFilter P xs)
        else
            subtypeFilter P xs
end L
end Lists
/-
    Dependent Vec type. Acts as a list bundled with its length.
-/
section Vector
universe u
variable {α : Type u}
/--
    27.
-/
inductive Vec (α : Type u) : ℕ -> Type u
    | nil  : Vec α 0
    | cons (n : ℕ) (_ : α) (_ : Vec α n) : Vec α (n + 1)
deriving Repr, BEq
namespace Vec
instance : EmptyCollection (Vec α 0) :=
    ⟨nil⟩
instance : Singleton α (Vec α 1) := ⟨
    fun x : α =>
        cons _ x nil
⟩
/--
    28.
-/
def head {n : ℕ} : Vec α (n + 1) -> α
    | cons _ x _ => x
/--
    29.
-/
def tail {n : ℕ} : Vec α (n + 1) -> Vec α n
    | cons _ _ xs => xs
/--
    30.
-/
def insert {n : ℕ} : α -> Vec α n -> Vec α (n + 1) :=
    fun x : α =>
        fun xs : Vec α n =>
            cons n x xs
/--
    31.
-/
def append {n m : ℕ} : Vec α n -> Vec α m -> Vec α (n + m) :=
    fun xs : Vec α n =>
        fun ys : Vec α m =>
            match xs with
                | nil =>
                    show Vec α (0 + m) by
                        simp [zero_add]
                        exact ys
                | cons k a as  =>
                    show Vec α (k + 1 + m) by
                        rw [add_assoc, add_comm 1]
                        apply cons (k + m) a (append as ys)
end Vec
end Vector
