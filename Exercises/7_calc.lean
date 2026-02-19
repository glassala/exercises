import Mathlib.Tactic
set_option linter.style.docString false
/-

    A symbolic differentiator for elementary functions
    of a single real variable.

-/
inductive Expr where
    | const : ℚ -> Expr
    | x : Expr
    | plus : Expr -> Expr -> Expr
    | minus : Expr -> Expr -> Expr
    | times : Expr -> Expr -> Expr
    | div : Expr -> Expr -> Expr
    | pow : Expr -> ℕ -> Expr
    | sin : Expr -> Expr
    | cos : Expr -> Expr
    | exp : Expr -> Expr
deriving DecidableEq, Repr
namespace Expr

def diff (f : Expr) : Expr :=
    match f with
        | const _ => const 0
        | x => const 1
        | plus a b => plus (diff a) (diff b)
        | minus a b => minus (diff a) (diff b)
        | times a b => plus (times (diff a) b) (times a (diff b))
        | div a b => div (minus (times (diff a) b) (times (diff b) a)) (pow b 2)
        | pow fx n => match n with
            | 0 => const 0
            | 1 => diff fx
            | k + 1 => times (times (const (k + 1 : ℚ)) (pow fx k)) (diff fx)
        | sin fx => times (cos fx) (diff fx)
        | cos fx => times (times (const (-1)) (sin fx)) (diff fx)
        | exp fx => times (exp fx) (diff fx)

def size : Expr → ℕ
    | const _  => 1
    | x        => 1
    | plus a b | minus a b | times a b | div a b => size a + size b + 1
    | pow a _ | sin a | cos a | exp a => size a + 1

def reduce' (f : Expr) : Expr :=
    match f with
        | plus (const a) (const b) => const (a + b)
        | plus (const 0) a | plus a (const 0) => reduce' a
        | minus (const a) (const b) => const (a - b)
        | minus a (const 0) => reduce' a
        | times (const a) (const b) => const (a * b)
        | times (const 0) _ | times _ (const 0) => const 0
        | times (const 1) a | times a (const 1) => reduce' a
        | plus a b => plus (reduce' a) (reduce' b)
        | minus a b => minus (reduce' a) (reduce' b)
        | times a b => times (reduce' a) (reduce' b)
        | div a b => div (reduce' a) (reduce' b)
        | _ => f

theorem size_reduce'_le (f : Expr) : size (reduce' f) ≤ size f := by
    induction f with
        | plus a b iha ihb =>
            unfold reduce'; split <;> simp_all [size] <;> omega
        | minus a b iha ihb =>
            unfold reduce'; split <;> simp_all [size] <;> omega
        | times a b iha ihb =>
            unfold reduce'; split <;> simp_all [size] <;> omega
        | div a b iha ihb =>
            unfold reduce'; simp_all [size] ; omega
        | _ => simp [reduce', size]

theorem size_reduce'_lt (f : Expr) (hf : f ≠ reduce' f) :
    size (reduce' f) < size f := by
        unfold reduce'
        split <;> simp_all <;>



def reduce (f : Expr) : Expr :=
    let g := reduce' f
    match f == g with
        | true => g
        | false => reduce g



def parse (f : Expr) : String :=
    match f with
        | const a => toString a
        | x => "x"
        | plus a b => parse a ++ " + " ++ parse b
        | minus a b => parse a ++ " - " ++ parse b
        | times a b => match a with
            | const 1 => parse b
            | _ => match b with
                | const 1 => parse a
                | _ => parse a ++ " * (" ++ parse b ++ ")"
        | div a b => parse a ++ " / " ++ parse b
        | pow fx n => "(" ++ parse fx ++ ")^" ++ toString n
        | sin fx => "sin(" ++ parse fx ++ ")"
        | cos fx => "cos(" ++ parse fx ++ ")"
        | exp fx => "exp(" ++ parse fx ++ ")"

--#eval parse (diff (sin (cos x)))
--#eval parse (diff (minus (plus (pow x 5) (pow x 3)) (sin (cos x))))
#eval parse (reduce' (diff (exp (times (const 5) x))))

end Expr
/-
/--
    221.
-/
inductive Expression where
    | num : ℕ -> Expression
    | var : ℕ -> Expression
    | plus : Expression -> Expression -> Expression
    | times : Expression -> Expression -> Expression
namespace Expression
/--
    222.
-/
def eval (e : Expression) (f : ℕ -> ℕ) : ℕ :=
    match e with
        | Expression.num n => n
        | Expression.var i => f i
        | Expression.plus s t => eval s f + eval t f
        | Expression.times s t => eval s f * eval t f
/--
    223.
-/
def simplify : Expression → Expression
    | plus (num n₁) (num n₂)  => num (n₁ + n₂)
    | times (num n₁) (num n₂) => num (n₁ * n₂)
    | e => e
/--
    224.
-/
def fuse : Expression -> Expression
    | num n => num n
    | var i => var i
    | plus a b =>
        match a, b with
            | (num a), (num b) => simplify (plus (num a) (num b))
            | (num a), b => simplify (plus (num a) b)
            | a, (num b) => simplify (plus a (num b))
            | a, b => simplify (plus (fuse a) (fuse b))
    | times a b =>
        match a, b with
            | (num a), (num b) => simplify (times (num a) (num b))
            | (num a), b => simplify (times (num a) b)
            | a, (num b) => simplify (times a (num b))
            | a, b => simplify (times (fuse a) (fuse b))
/--
    225.
-/
theorem simplify_eq (v : ℕ → ℕ) (e : Expression) : eval (simplify e) v = eval e v := by
    induction e
    case num n =>
        rfl
    case var i =>
        rfl
    case plus a b iha ihb =>
        simp [simplify, eval]
        cases a <;> cases b <;> simp [eval, *]
    case times a b iha ihb =>
        simp [simplify, eval]
        cases a <;> cases b <;> simp [eval, *]
/--
    226.
-/
theorem fuse_eq (v : ℕ → ℕ) (e : Expression) : eval (fuse e) v = eval e v := by
    induction e
    case num n =>
        rfl
    case var i =>
        rfl
    case plus a b iha ihb =>
        simp [eval]
        cases a <;> cases b <;> simp [fuse, eval, simplify_eq, iha, ihb]
    case times a b iha ihb =>
        simp [eval]
        cases a <;> cases b <;> simp [fuse, eval, simplify_eq, iha, ihb]
#eval fuse (times (plus (num 3) (num 3)) (plus (num 1) (num 2)))
-/
