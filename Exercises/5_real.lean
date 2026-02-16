import Mathlib.Tactic
set_option linter.style.multiGoal false
set_option linter.style.docString false
set_option linter.style.cases false
/-

    Exercises from the first 7 worlds of Alex Kontorovich's
    Real Analysis: The Game. From around November 2025.

    In the game, "rw" and "exact" must be foregone
    in favor of "rewrite" and "apply" respectively.

    It must be said, however, that rw is much shorter, and
    closing a goal with "exact h" when h exactly matches
    said goal "really hits the spot."

    These examples otherwise remain faithful to the
    progressively-less-restrictive tactical toolbox which is
    characteristic of a well-designed Lean game.

    -- Will Sweet

-/
/--
    1.
-/
example (f : ℝ → ℝ)
    (h_existential : ∃ (a : ℝ), f (a) = 3)
    (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9) :
    ∃ (b : ℝ), ∀ y > 0, f (y + 1) ^ 2 = (f (y) + (f b) ^ 2) ^ 2 := by
        choose a ha using h_existential
        use a
        rw [ha]
        intro x hx
        rw [h_universal]
        ring_nf
        exact hx
/--
    2.
-/
example (f : ℝ → ℝ) (h : ∀ u, f (u) = 2 * u + 1) : ∃ a, f (3) = a := by
    specialize h 3
    use 7
    ring_nf at h
    apply h
/--
    3.
-/
example : ∃ c, ∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y = 1 → (x + y) ^ 2 = c := by
    use 4
    intro _ _ f g
    have huv (u v : ℝ) : (u + v) ^ 2 = (u ^ 2) + (v ^ 2) + (2 * (u * v)) := by
        ring_nf
    rw [huv, f, g]
    ring_nf
/--
    4.
-/
example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (1) = 8 := by
    specialize h1 0
    rw [h2] at h1
    ring_nf at h1
    exact h1
/--
    5.
-/
example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (2) = 11 := by
    have h3 : g (0 + 1) = g (0) + 3 := by
        apply h1 0
    rw [h2] at h3
    ring_nf at h3
    specialize h1 1
    rewrite [h3] at h1
    ring_nf at h1
    exact h1
/--
    6.
-/
example (p : ℝ → ℝ) (x : ℝ) (h1 : ∀ t, p (t) = t ^ 2 + 2 * t) (h2 : p (x) = 15) :
    ∃ b, x ^ 2 + 2 * x = b := by
        have h : p x = x^2 + 2*x := by
            apply h1
        rw [h] at h2
        use 15
/--
    7.
-/
def binom : ℚ -> ℕ -> ℚ :=
    fun n k =>
        (prod' n k)/(Nat.factorial k) where
             prod' : ℚ -> ℕ -> ℚ :=
                fun n k => match k with
                    | 0 => 1
                    | k' + 1 => (n - k') * prod' n k'
#eval binom (1/2) 5
example : ∃ c, ∀ (x : ℝ),
    (1 + x / 2 - x^2 / 8 + x^3 / 16 - 5 * x^4 / 128 + c * x^5) ^ 2 - (1 + x) =
    x^6 * (21 / 512 - 3 * x / 256 + 81 * x^2 / 16384 - 35 * x^3 / 16384 + 49 * x^4 / 65536) := by
        use (7/256)
        intro x
        ring_nf
#eval binom (3/2) <$> [2, 3, 4]
/--
    8.
-/
example : ∃ c d e, ∀ (x : ℝ),
    (1 + 3 * x / 2 + c * x ^ 2 + d * x ^ 3 + e * x ^ 4) ^ 2 - (1 + x) ^ 3 =
    x ^ 5 * ( 3/128 + (11 * x)/512 - (3 * x^2)/1024 + (9 * x^3)/16384 ) := by
        use (3/8), (-1/16), (3/128)
        intro x
        ring_nf
/--
    9.

    Limit of a sequence. The underpinning of the idea of convergence of a series.
    An infinite series converges to a real number L if the sequence of its successive
    partial sums has a limit L.

-/
def SeqLim (a : ℕ -> ℝ) (L : ℝ) := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
/--
    10.

    If a sequence is constant, *obviously* it converges to that constant.
-/
theorem ConstLim (a : ℕ → ℝ) (L : ℝ) (a_const : ∀ n, a n = L) : SeqLim a L := by
    change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
    intro _ hx
    use 0
    intro n _
    rw [a_const n]
    ring_nf
    norm_num
    exact hx
/--
    11.
-/
theorem ArchProp {ε : ℝ} (_ : 0 < ε) : ∃ (N : ℕ), 1 / ε < N := by
    use ⌈1 / ε⌉₊ + 1
    push_cast
    have h : 1 / ε ≤ ⌈1 / ε⌉₊ := by
        bound
    have h' (a b : ℝ) : (a ≤ b) -> (a < b + 1) := by
        intro f ; bound
    specialize h' (1 / ε) (↑⌈1 / ε⌉₊) h
    apply h'
/--
    12.

    The limit of f(x) = 1/x as x approaches ∞ is 0.
-/
theorem OneOverNLimZero (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : SeqLim a 0 := by
    change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - 0| < ε
    have if_lt_inv_gt (a b : ℝ) (h : a > 0) : (a < b) -> (1/b < 1/a) := by
        bound
    have if_le_inv_ge (a b : ℝ) (h : a > 0) : (a ≤ b) -> (1/b ≤ 1/a) := by
        bound
    ring_nf
    intro ε hep
    have hap : ∃ (N : ℕ), 1 / ε < ↑N := by
        apply ArchProp
        apply hep
    choose N hn' using hap
    use N
    intro n hn
    specialize ha n
    rw [ha]
    have hpos : 1/ε > 0 := by
        bound
    specialize if_lt_inv_gt (1/ε) N hpos hn'
    field_simp at if_lt_inv_gt
    have hnpos : (N : ℝ) > 0 := by
        linarith [hn', hpos]
    have le_cast : (N : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
    specialize if_le_inv_ge N n hnpos le_cast
    rw [show |1 / (n : ℝ)| = 1 / (n : ℝ) by norm_num]
    bound
/--
    13.

    The full archimedean property.
-/
example (x y : ℝ) (x_pos : 0 < x) (y_pos : 0 < y) : ∃ (N : ℕ), y < x * N := by
    have h1 : y / x ≤ ↑(⌈y / x⌉₊) := by bound
    have h2 (a b : ℝ) (_ : 0 < a) (_ : 0 < b) : (a ≤ b) -> (x * a ≤ x * b) := by bound
    have h3 : (0 < y / x) := by bound
    have h4 (a b : ℝ) (h : 0 < a) (h' : a ≤ b) : 0 < b := by bound
    have h5 : (0 < (⌈y / x⌉₊ : ℝ)) := by specialize h4 (y / x) ↑(⌈y / x⌉₊) h3 h1 ; apply h4
    have h6 : x * (y / x) ≤ x * (⌈y / x⌉₊ : ℝ) := by
        specialize h2 (y / x) ↑(⌈y / x⌉₊) h3 h5 h1
        apply h2
    have h7 (a b c : ℝ) (h : 0 < c): (a ≤ c * b) -> (a < c * (b + 1)) := by intro f ; bound
    use (⌈y / x⌉₊ + 1)
    field_simp at h6
    push_cast
    specialize h7 y ↑(⌈y / x⌉₊) x x_pos h6
    apply h7
/--
    14.

    The limit of f(x) = (x + 1)/x as x approaches ∞ is 1.

    I am left with the suspicion that the actual problem was easier than this
    barely readable monstrosity indicates. However, having spent the better part
    of two days cobbling it together, I am more inclined to look fondly at the
    pair of checkmarks next to it and then bury my suspicions behind the garden
    so I can move on to the next problem.

    If you look at something made into an explicit "have" statement and think
    "surely Lean could automatically infer this decidedly elementary step,"
    there is a decent chance that I had thought so too.
-/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) : ∃ L, SeqLim a L := by
    have trans (a b c : ℝ) (h : a ≥ b) (h' : b ≥ c) : a ≥ c := by bound
    have up_cast (x y : ℕ) : (x ≥ y) -> (x : ℝ) ≥ (y : ℝ) := by intro h ; exact_mod_cast h
    use 1 ; change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - 1| < ε
    intro ε ε_pos ; use ⌈1/ε⌉₊ + 1 ; intro n hn ; specialize ha n
    have f1 : (x : ℝ) -> ((x + 1) / x) = (x / x) + (1 / x) := by intro _ ; field_simp
    have f2 : (x : ℝ) -> (x > 0) -> x / x = 1 := by intro _ _ ; field_simp
    have f3 : (x : ℝ) -> 1 + x - 1 = x := by intro _ ; ring_nf
    have f4 : (n : ℝ) > 0 := by bound
    have f5 (x : ℝ) : ⌈x⌉₊ + 1 ≥ x + 1 := by bound
    rewrite [ha, f1, f2, f3] ; norm_num
    have h0 : 1/ε > 0 := by bound
    have h1 (x : ℕ) (y : ℝ) (f : x ≥ ⌈y⌉₊ + 1) : ((x : ℝ) ≥ y + 1) := by
        have h1a : (x : ℝ) ≥ ↑⌈y⌉₊ + 1 := by
            specialize up_cast x (⌈y⌉₊ + ↑1) f ; push_cast at up_cast ; apply up_cast
        specialize f5 y ; specialize trans x (⌈y⌉₊ + 1) (y + 1) h1a f5 ; apply trans
    have h2 : n ≥ (1 / ε) + 1 := by specialize h1 n (1/ε) hn ; apply h1
    have h3 : (n : ℝ) > 1 := by bound
    have h4 (x y : ℝ) (h : x > 1) : (x ≥ y + 1) -> (x > y) := by bound
    have h5 (x y : ℝ) (hx : x > 0) (hy : y > 0) : (x > (1/y)) -> (x * y > 1) := by
        have inv : y⁻¹ * y = 1 := by field_simp
        intro f ; ring_nf at f ; rewrite [<- inv] ; bound
    specialize h4 (↑n) (1/ε) h3 h2 ; specialize h5 ↑n ε f4 ε_pos h4
    have h6 (x y z : ℝ) : (x * y > z) -> (y * x > z) := by bound
    have h7 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x * z > y * z) -> (x > y) := by
        intro _
        have h' : (x * z) / z > (y * z) / z := by bound
        field_simp at h' ; apply h'
    have h8 (x y : ℝ) (hx : x > 0) (hy : y > 0) : (x * y > 1) -> (y > 1/x) := by
        have hip : x⁻¹ > 0 := by bound
        have inv_eq : x⁻¹ * x = 1 := by field_simp
        intro f ; specialize h6 x y 1 f ; rewrite [<- inv_eq] at h6 ; ring_nf
        specialize h7 y x⁻¹ x hy hip hx h6 ; apply h7
    specialize h8 ↑n ε f4 ε_pos h5 ; ring_nf at h8 ; bound ; bound
/--
    15.
-/
example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n ^ 2) : ∃ L, SeqLim a L := by
    use 0 ; change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - 0| < ε
    intro ε hε
    have hap : ∃ (N : ℕ), 1 / ε < ↑N := by apply ArchProp ; apply hε
    choose N hN using hap ; use N
    intro n hn ; ring_nf ; specialize ha n ; rewrite [ha]
    have h1 : 1/ε > 0 := by bound
    have h2 : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
    have h3 : (n : ℝ) > 1/ε := by linarith
    have h4 : (n : ℝ) > 0 := by linarith
    have h5 : n > 0 := by exact_mod_cast h4
    have f0 (h : n > 0) : ((1 : ℝ)/(n : ℝ)) ≥ (1/(n : ℝ)^2) := by bound
    have f1 (a b : ℝ) (h : a > 0) : (a < b) -> (1/b < 1/a) := by bound
    have f2 (a b : ℝ) (h : a > 0) : (a ≤ b) -> (1/b ≤ 1/a) := by bound
    specialize f1 (1/ε) n h1 h3 ; field_simp at f1
    specialize f0 h5
    have trans (a b c : ℝ) : (a ≥ b) -> (a < c) -> (b < c) := by bound
    specialize trans (1 / (n : ℝ)) (1 / ((n : ℝ)^ 2)) ε f0 f1 ; norm_num at *
    exact_mod_cast trans
/--
    16.

    Nowhere in the analysis handbook does it say the bounds for N must be tight.

    Considering the tactical constraints of a Lean game, I have given up all
    worry about "elegance."
-/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + 8) / (2 * n + 5)) : ∃ L, SeqLim a L := by
    have trans' (a b c : ℝ) : (a > b) -> (b > c) -> (a > c) := by bound
    use 3/2 ; change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - (3/2)| < ε
    intro ε hε ; use ⌈1/ε⌉₊ + 1 ; intro n hn ; specialize ha n ; rewrite [ha]
    have hnr : (n : ℝ) ≥ ⌈1 / ε⌉₊ + 1 := by exact_mod_cast hn
    have h1 : (⌈1 / ε⌉₊ : ℝ) ≥ 1/ε := by bound
    have h2 : n > 1/ε := by bound
    have h3 : (n : ℝ) > 0 := by specialize trans' n (1/ε) 0 h2 (by bound) ; apply trans'
    have h4 : (2 * (n : ℝ) + 5) > 0 := by bound
    have h5 (x : ℝ) (f : x > 0) : 3/2 = (3 * x)/(2 * x) := by field_simp
    have h6 : 3 * ((n : ℝ) + 5) = 3 * (n : ℝ) + 15 := by ring_nf
    have h7 : 2 * ((n : ℝ) + 5) = 2 * (n : ℝ) + 10 := by ring_nf
    have h8 : (n : ℝ) + 5 > 0 := by bound
    have h9 (x : ℝ) : (x > 0) -> (3*x+8)/(2*x+5) = ((6*x^2)+(46*x)+80)/((4*x^2)+(30*x)+50) := by
        intro h ; field_simp ; ring_nf
    have h10 (x : ℝ) : (x > 0) -> (3*x+15)/(2*x+10) = ((6*x^2)+(45*x)+75)/((4*x^2)+(30*x)+50) := by
        intro h ; field_simp ; ring_nf
    have h11 (x : ℝ) :
        ((6*x^2)+(46*x)+80)/((4*x^2)+(30*x)+50) - ((6*x^2)+(45*x)+75)/((4*x^2)+(30*x)+50) =
        (x+5)/((4*x^2)+(30*x)+50) := by
            ring_nf
    have h12 (x : ℝ) : (4*x^2)+(30*x)+50 = (x+5)*(4*x+10) := by ring_nf
    have h13 (x y : ℝ) (hx : x > 0) (hy : y > 0) : x/(x * y) = 1/y := by field_simp
    have h14 (x : ℝ) : (x > 0)  -> 1 / (4 * x + 10) > 0 := by intro _ ; bound
    have h15 (x : ℝ) : (x > 0) -> (1 / (4 * x + 10)) < (1/x) := by intro _ ; bound
    specialize h5 ((n : ℝ) + 5) h8 ; rewrite [h6, h7] at h5
    specialize h9 ↑n h3 ; specialize h10 ↑n h3 ; specialize h11 ↑n
    specialize h12 ↑n ; specialize h13 (↑n + 5) (4*↑n+10) (by bound) (by bound)
    rewrite [h5, h9, h10, h11, h12, h13]
    specialize h14 ↑n (by bound) ; rewrite [abs_of_nonneg]
    specialize h15 ↑n (by bound)
    have h16 (a b : ℝ) (h : a > 0) : (a < b) -> (1/b < 1/a) := by bound
    specialize h16 (1/ε) ↑n (by bound) (by bound)
    bound ; bound
/--
    17.

    Convergence of a sequence.
-/
def SeqConv (a : ℕ → ℝ) : Prop := ∃ L, SeqLim a L
/--
    18.

    Proof 1:

    The sequence aₙ = (-1)ⁿ does not converge.

    Suppose it were to converge.

    Then, there would exist a real limit L, such that for all real ε > 0,
    there would exist a natural number N, such that for all natural numbers
    n ≥ N, |(-1)ⁿ - L| < ε.

    Then, let ε = 1/2. Observe that, for any n, either (-1)ⁿ = 1
    or (-1)ⁿ = -1. So, any choice of L would have to satisfy both
    |(-1) - L| < 1/2 and |1 - L| < 1/2.

    We can then consider the possible intervals for L to lie in.

    If L ≥ 3/2 or L ≤ -3/2, then it is apparent that both cases fail.
    If -1/2 ≤ L ≤ 1/2, then it is apparent that both cases fail.
    If 1/2 < L < 3/2 or -3/2 < L < -1/2, then one case will pass while
    the other fails.

    Since all real numbers fail as candidates for L,
    we can conclude that no limit exists for aₙ = (-1)ⁿ.

    (...)

    I used hidden techniques of the lambda taken from
    Theorem Proving in Lean in order to sequence break and
    give myself early access to the "induction" and "cases" tactics.

    (...)

    Proof 2:

    (See above)

    (...) So, any choice of L would have to satisfy both
    |1 - L| < 1/2 and |(-1) - L| < 1/2. Therefore, L would have to satisfy
    |1 - L| + |(-1) - L| < 1.

    Consider that 2 = |1 - -1| = |1 - L + (L - (-1))|, and so, by the
    triangle inequality, 2 ≤ |1 - L| + |L - (-1)|.

    Since |L - (-1)| = |(-((-1) - L))| = |(-1) - L|,
    2 ≤ |1 - L| + |L - (-1)|.

    However, this necessitates that 2 ≤ |1 - L| + |L - (-1)| < 1,
    which is a contradiction. So, this limit doesn't exist.

-/
example (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ¬ SeqConv a := by
    change ¬ ∃ L, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
    intro h
    choose L hL using h
    specialize hL (1/2) (by bound)
    choose N hN using hL
    have h0 : |(1 : ℝ) - (-1)| = 2 := by ring_nf ; apply abs_of_nonneg ; bound
    have h1 : |1 - (-1)| = |(1 - L) + (L - (-1))| := by ring_nf
    have h2 : |(1 - L) + (L - (-1))| ≤ |1 - L| + |L - (-1)| := by apply abs_add_le
    have h3 : |L - (-1)| = |-((-1) - L)| := by ring_nf
    have h4 : |1 - L| + |L - (-1)| = |1 - L| + |-((-1) - L)| := by rewrite [<- h3] ; rfl
    rewrite [<- h1, h0, h4, abs_neg] at h2
    have h_base : (-1) ^ 0 = 1 := by ring_nf
    have h_split (n : ℕ) : ((-1) ^ n = 1) -> ((-1) ^ (n + 1) = -1) := by
        intro f ; ring_nf ; rewrite [f] ; rfl
    have h_split' (n : ℕ) : ((-1) ^ n = -1) -> ((-1) ^ (n + 1) = 1) := by
        intro f ; ring_nf ; rewrite [f] ; rfl
    have hm (n : ℕ) : ((-1) ^ n = 1) ∨ ((-1) ^ n = -1) :=
        Nat.rec
            (motive := fun n => ((-1) ^ n = 1) ∨ ((-1) ^ n = -1)) (Or.inl rfl)
            (fun k ih => Or.by_cases ih
                (fun hl => Or.inr (h_split k hl))
                (fun hr => Or.inl (h_split' k hr)))
        n
    specialize hm N
    have hq (x y z : ℝ) : (x < z) -> (y < z) -> (x + y < 2 * z) := by
        intro xz yz ; bound
    apply Or.by_cases hm
        (fun h_left => by
            specialize h_split N h_left
            have xp1 : |1 - L| < 1 / 2 := by
                specialize hN N (by rfl)
                specialize ha N
                have h_left_cast : (-1 : ℝ) ^ N = 1 := by exact_mod_cast h_left
                rewrite [ha, h_left_cast] at hN
                apply hN
            have xp2 : |-1 - L| < 1 / 2 := by
                specialize hN (N + 1) (by bound)
                specialize ha (N + 1)
                have h_left_cast : (-1 : ℝ) ^ (N + 1) = -1 := by
                    exact_mod_cast h_split
                rewrite [ha, h_left_cast] at hN
                apply hN
            specialize hq (|1 - L|) (|-1 - L|) (1/2) xp1 xp2
            ring_nf at hq
            linarith)
        (fun h_right => by
            specialize h_split' N h_right
            have xp1 : |-1 - L| < 1 / 2 := by
                specialize hN N (by rfl)
                specialize ha N
                have h_right_cast : (-1 : ℝ) ^ N = -1 := by exact_mod_cast h_right
                rewrite [ha, h_right_cast] at hN
                apply hN
            have xp2 : |1 - L| < 1 / 2 := by
                specialize hN (N + 1) (by bound)
                specialize ha (N + 1)
                have h_right_cast : (-1 : ℝ) ^ (N + 1) = 1 := by
                    exact_mod_cast h_split'
                rewrite [ha, h_right_cast] at hN
                apply hN
            specialize hq (|1 - L|) (|-1 - L|) (1/2) xp2 xp1
            linarith)
/--
    19.

    This one took me altogether too long.

-/
example (a : ℕ → ℝ)
    (ha2n : ∀ n, a (2 * n) = 3 - 1 / n)
    (ha2np1 : ∀ n, a (2 * n + 1) = 1 + 1 / n) : ¬ SeqConv a := by
        have f (x y z : ℝ) : (x < z) -> (y < z) -> (x + y < 2 * z) := by
          intro _ _ ; bound
        have f0 (x y z w : ℝ) : (x ≤ z) -> (y ≤ w) -> (x + y ≤ z + w) := by
          intro _ _ ; bound
        have f1 (x y z : ℝ) : (|x| + |y| < z) -> (|x + y| < z) := by
            intro _
            have h' : |x + y| ≤ |x| + |y| := by apply abs_add_le
            bound
        have f2 (x y z : ℝ) : |x| + |z| + (|y| + |z|) = |x| + |y| + |2*z| := by
            have f2' (w : ℝ) : (w ≥ 0) -> |z| * |w| = |z| * w := by
                intro hw
                rewrite [abs_of_nonneg hw] ; rfl
            rewrite [abs_mul] ; ring_nf
            specialize f2' 2 (by bound)
            rewrite [f2'] ; rfl
        change ¬ ∃ L, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
        intro h
        choose L hL using h
        specialize hL (1/2) (by bound)
        choose N hN using hL
        have n3 : ∃ n : ℕ, n ≥ N ∧ n ≥ 3 := ⟨max N 3, by norm_num⟩
        choose n hn using n3
        have even_bound : |a (2 * n) - L| < 1/2 := hN (2 * n) (by linarith)
        have odd_bound : |a (2 * n + 1) - L| < 1/2 := hN (2 * n + 1) (by linarith)
        have sum_bound : |a (2 * n) - L| + |a (2 * n + 1) - L| < 1 := by bound
        have h3L : |3 - L| = |a (2*n) - L + 1/n| := by
          rewrite [ha2n] ; ring_nf
        have h1L : |1 - L| = |a (2*n+1) - L - 1/n| := by
          rewrite [ha2np1] ; ring_nf
        have h_tri : |3 - L| + |1 - L| ≤ |a (2*n) - L| + |a (2*n+1) - L| + 2/n := by
            rewrite [h3L, h1L]
            have h1 : |(a (2 * n) - L) + (1/n)| ≤ |a (2 * n) - L| + |(1/n: ℝ)| := abs_add_le _ _
            have h2 : |(a (2*n+1) - L) + (-(1/n))| ≤ |a (2*n+1) - L| + |-(1/n: ℝ)| := abs_add_le _ _
            specialize
                f0 |(a (2 * n) - L) + (1/n)| |(a (2 * n + 1) - L) + (-(1/n))|
                (|a (2 * n) - L| + |(1/n: ℝ)|)
                (|a (2 * n + 1) - L| + |-(1/n: ℝ)|)
                h1 h2
            rewrite [abs_neg] at f0 ; field_simp at f0
            specialize f2 |a (2 * n) - L| |a (2*n+1) - L| |1 / (n : ℝ)|
            have h' :
                |a (2*n) - L| + |1 / (n : ℝ)| + (|a (2*n+1) - L| + |1 / (n : ℝ)|) =
                |a (2*n) - L| + |a (2*n+1) - L| + |2/(n : ℝ)| := by
                    have h'' : |(2:ℝ) / ↑n| = |(2:ℝ) * (↑n)⁻¹| := by ring_nf
                    norm_num at *
                    rewrite [f2, h''] ; rfl
            rewrite [h'] at f0
            have hnn : |2/(n:ℝ)| = 2/(n:ℝ) := by apply abs_of_nonneg ; bound
            rewrite [hnn] at f0
            apply f0
        have hz : |a (2*n) - L| + |a (2*n+1) - L| + 2/n < 2 := by
            have hz' : 2/(n : ℝ) < 1 := by
                have hz'' (x : ℝ) : (x ≥ 3) -> (2/x < 1) := by bound
                specialize hz'' ↑n (by exact_mod_cast hn.right)
                apply hz''
            bound
        have hy : 2 ≤ |3 - L| + |1 - L| := by
            have split_2 : |3 - 1| = |(3 - L) + (L - 1)| := by ring_nf
            have split_tri : |(3 - L) + (L - 1)| ≤ |(3 - L)| + |(L - 1)| := by
                apply abs_add_le
            have hx : |-(L - 1)| = |1 - L| := by ring_nf
            have hx' : |-(L - 1)| = |L - 1| := by apply abs_neg
            rewrite [<- hx', hx, <- split_2] at split_tri
            norm_num at split_tri ; apply split_tri
        bound
/--
    20.
-/
example (a b : ℕ → ℝ) (L : ℝ) (h : SeqLim a L)
    (b_scaled : ∀ n, b n = 2 * a n) : SeqLim b (2 * L) := by
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - (2 * L)| < ε
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at h
        intro ε hε
        have h_alf : 0 < (ε/2) := by bound
        specialize h (ε/2) h_alf
        choose N hN using h
        use N
        intro n hn
        specialize b_scaled n ; rewrite [b_scaled]
        have ham (x y : ℝ) : |x * y| = |x| * |y| := by apply abs_mul
        have h_dist : 2 * a n - 2 * L = 2 * (a n - L) := by ring_nf
        specialize ham 2 (a n - L)
        rewrite [h_dist, ham, abs_of_nonneg]
        specialize hN n hn
        have kill_shot (x y : ℝ) : (|x| < y/2) -> (2 * |x| < y) := by bound
        specialize kill_shot (a n - L) ε hN
        apply kill_shot ; bound
/--
    21.
-/
theorem SumLim (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M)
    (hc : ∀ n, c n = a n + b n) : SeqLim c (L + M) := by
        have f (x y z : ℝ) : (|x| + |y| < z) -> (|x + y| < z) := by
            intro f'
            have h' : |x + y| ≤ |x| + |y| := by apply abs_add_le
            bound
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at ha
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - M| < ε at hb
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |c n - (L + M)| < ε
        intro ε hε
        specialize ha (ε/2) (by bound) ; specialize hb (ε/2) (by bound)
        choose aN haN using ha ; choose bN hbN using hb
        use (aN + bN)
        intro n' hcN
        rewrite [hc]
        specialize haN n' (by bound) ; specialize hbN n' (by bound)
        have ha1 : |a n' - L| + |b n' - M| < ε := by bound
        have h_sum : |a n' + b n' - (L + M)| = |a n' - L + (b n' - M)| := by
            ring_nf
        rewrite [h_sum]
        specialize f (a n' - L) (b n' - M) ε ha1
        apply f
/--
    22.
-/
example (x y : ℝ) (hx : x = 2) (hy : y = 3) : x = 2 ∧ y = 3 :=
    ⟨hx, hy⟩
example (x y : ℝ) (hx : x = 2) (hy : y = 3) : x = 2 ∧ y = 3 := by
    split_ands ; apply hx ; apply hy
/--
    23.
-/
example (x y : ℝ) (_ : x = 2) (hy : y = 3) : x = 3 ∨ y = 3 :=
    Or.inr hy
example (x y : ℝ) (_ : x = 2) (hy : y = 3) : x = 3 ∨ y = 3 := by
    apply Or.inr hy
example (x y : ℝ) (_ : x = 2) (hy : y = 3) : x = 3 ∨ y = 3 := by
    right ; apply hy
/--
    24.
-/
example (x y : ℝ) (h : x = 2 ∧ y = 3) : y = 3 :=
    h.right
example (x y : ℝ) (h : x = 2 ∧ y = 3) : y = 3 := by
    apply h.2
/--
    25.

    The "cases'" tactic is discouraged in favor of "cases" or "rcases."
-/
example (x y : ℝ) (h : x = 2 ∨ y = 3) : (x - 2) * (y - 3) = 0 := by
    cases' h with h1 h2
    rewrite [h1] ; ring_nf
    rewrite [h2] ; ring_nf
example (x y : ℝ) (h : x = 2 ∨ y = 3) : (x - 2) * (y - 3) = 0 := by
    cases h
    case inl h1 =>
        rewrite [h1] ; ring_nf
    case inr h2 =>
        rewrite [h2] ; ring_nf
example (x y : ℝ) (h : x = 2 ∨ y = 3) : (x - 2) * (y - 3) = 0 := by
    rcases h
    case inl h1 =>
        rewrite [h1] ; ring_nf
    case inr h2 =>
        rewrite [h2] ; ring_nf
/--
    26.
-/
example (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) : ∃ N, ∀ n ≥ N, a n ≥ L - 1 := by
    change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at ha
    specialize ha 1 (by bound)
    choose N hN using ha
    use N
    intro n hn
    specialize hN n hn
    rewrite [abs_lt] at hN
    linarith [hN.left]
/--
    27.
-/
theorem SqueezeThm (a b c : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (cToL : SeqLim c L)
    (aLeb : ∀ n, a n ≤ b n) (bLec : ∀ n, b n ≤ c n) : SeqLim b L := by
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - L| < ε
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |c n - L| < ε at cToL
        intro ε hε
        specialize aToL ε hε ; specialize cToL ε hε
        choose aN haN using aToL ; choose cN hcN using cToL
        use (aN + cN)
        intro n hn
        specialize haN n (by bound) ; specialize hcN n (by bound)
        specialize aLeb n ; specialize bLec n
        rewrite [abs_lt] at *
        bound
/--
    28.
-/
example (x y z : ℝ) (hx : x = 2) (hy : y = 3) (hz : z = 4) : x = 2 ∧ y = 3 ∧ z = 4 := by
    split_ands
    apply hx ; apply hy ; apply hz
/--
    29.
-/
example (x y z : ℝ) (h : x = 2 ∧ y = 3 ∧ z = 4) : z = 4 := by
    apply h.2.2
/--
    30.
-/
example (a : ℕ → ℝ) (ha : SeqLim a 5) : ∃ N, ∀ n ≥ N, 0 < a n := by
    change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - 5| < ε at ha
    specialize ha 1 (by bound)
    choose N hN using ha
    use N
    intro n hn
    specialize hN n hn
    rewrite [abs_lt] at hN
    bound
/--
    31.
-/
example (a : ℕ → ℝ) (ha : ∀ N, ∃ n ≥ N, |a n| > 10) : ¬ ∃ L, |L| < 5 ∧ SeqLim a L := by
    change ¬ ∃ L, |L| < 5 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε
    intro h
    choose L hL using h
    have ⟨hLL, hLR⟩ := hL
    specialize hLR 1 (by bound)
    choose N hN using hLR
    specialize ha N
    choose n hn using ha
    specialize hN n (by bound)
    have sub_tri : |a n| - |L| ≤ |a n - L| := by
        have h' : |a n| ≤ |a n - L| + |L| := by
            have hh : |a n| = |a n - L + L| := by ring_nf
            rewrite [hh]
            apply abs_add_le
        linarith
    have h1 : |a n| - |L| > 5 := by bound
    linarith
/--
    32.
-/
example (a b c d e : ℕ → ℝ) (L : ℝ)
    (ha : SeqLim a L) (hc : SeqLim c L) (he : SeqLim e L)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) (hcd : ∀ n, c n ≤ d n)
    (hde : ∀ n, d n ≤ e n) : SeqLim b L ∧ SeqLim d L := by
        split_ands
        apply SqueezeThm a b c L ha hc hab hbc
        apply SqueezeThm c d e L hc he hcd hde
/--
    33.
-/
theorem LimUnique (a : ℕ → ℝ) (L M : ℝ)
    (aToL : SeqLim a L) (aToM : SeqLim a M) : L = M := by
        have f1 (x y z : ℝ) : x = y -> x + z = y + z := by
            intro f' ; norm_num ; apply f'
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - M| < ε at aToM
        by_contra! hn
        have d_pos : |L - M|/2 > 0 := by
            norm_num
            intro hl
            specialize f1 (L - M) 0 M hl
            norm_num at f1 hn
            apply hn f1
        specialize aToL (|L - M|/2) (by bound)
        specialize aToM (|L - M|/2) (by bound)
        choose NL hNL using aToL
        choose NM hNM using aToM
        specialize hNL (NL + NM) (by bound) ; specialize hNM (NL + NM) (by bound)
        have epsum : |L - M| / 2 + |L - M| / 2 = |L - M| := by ring_nf
        have next_sum : |a (NL + NM) - L| + |a (NL + NM) - M| < |L - M| := by bound
        have killer : |L - M| = |(a (NL + NM) - M) + (L - a (NL + NM))| := by ring_nf
        have k_tri : |(a (NL + NM) - M) + (L - a (NL + NM))| ≤
            |a (NL + NM) - M| + |L - a (NL + NM)| := by apply abs_add_le
        have k_swap : |L - a (NL + NM)| = |-(L - a (NL + NM))| := by
            rewrite [abs_neg] ; rfl
        have k_swap2 : |-(L - a (NL + NM))| = |a (NL + NM) - L| := by ring_nf
        rewrite [k_swap, k_swap2, <- killer] at k_tri
        linarith
/--
    34.
-/
theorem EventuallyGeHalfLimPos (a : ℕ → ℝ) (L : ℝ)
    (aToL : SeqLim a L) (LneZero : L ≠ 0) : ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        have h : 0 < |L| := by norm_num at * ; apply LneZero
        specialize aToL (|L|/2) (by bound)
        choose N hN using aToL
        use N
        intro n hn
        specialize hN n hn
        have f : |L| = |a n + (L - a n)| := by ring_nf
        have f_tri : |a n + (L - a n)| ≤ |a n| + |L - a n| := by apply abs_add_le
        have f1 : |L - a n| = |-(L - a n)| := by rewrite [abs_neg] ; rfl
        have f2 : |-(L - a n)| = |a n - L| := by ring_nf
        rewrite [<- f, f1, f2] at f_tri
        bound
/--
    35.
-/
theorem AbsLim (a : ℕ → ℝ) (L : ℝ)
    (aToL : SeqLim a L) (b : ℕ → ℝ) (bEqAbsa : ∀ n, b n = |a n|) : SeqLim b |L| := by
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - (|L|)| < ε
        intro ε hε
        specialize aToL ε hε
        choose N hN using aToL
        use N
        intro n hn
        specialize bEqAbsa n
        specialize hN n hn
        rewrite [bEqAbsa]
        have sub_tri : |a n| - |L| ≤ |a n - L| := by
            have h' : |a n| ≤ |a n - L| + |L| := by
                have hh : |a n| = |a n - L + L| := by ring_nf
                rewrite [hh]
                apply abs_add_le
            linarith
        have tri_next : |a n| - |L| < ε := by bound
        have abs_lip (x y : ℝ) : |(|x|) - (|y|)| ≤ |x - y| := by
            apply abs_abs_sub_abs_le_abs_sub
        specialize abs_lip (a n) L
        bound
/--
    36.
-/
theorem InvLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero : L ≠ 0) (b : ℕ → ℝ)
    (bEqInva : ∀ n, b n = 1 / a n) : SeqLim b (1 / L) := by
        have L_bound : |L|/2 > 0 := by
            have h' : |L| > 0 := by
                rewrite [<- abs_pos] at LneZero
                bound
            bound
        have f_sub_tri (x y : ℝ) : |x| - |y| ≤ |x - y| := by
            have h' : |x| ≤ |x - y| + |y| := by
                have hh : |x| = |x - y + y| := by ring_nf
                rewrite [hh]
                apply abs_add_le
            linarith
        have f (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
            (1/x) - (1/y) = (y - x)/(x * y) := by field_simp
        have aToL' : SeqLim a L := by apply aToL
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL'
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - (1/L)| < ε
        intro ε hε
        have ε_bound : |L|^2/2 * ε > 0 := by bound
        specialize aToL (|L|^2/2 * ε) ε_bound
        specialize aToL' (|L|/2) L_bound
        choose N hN using aToL ; choose N' hN' using aToL'
        use (N + N')
        intro n hn
        specialize hN n (by bound) ; specialize hN' n (by bound)
        have a_nzero : |a n| > 0 := by
            by_contra heq
            norm_num at heq
            rewrite [heq] at hN' ; norm_num at hN'
            bound
        have h2 : |L - a n| = |a n - L| := by
            rewrite [<- abs_neg]
            ring_nf
        have f1 : |L| = |a n + (L - a n)| := by ring_nf
        have f2 : |a n + (L - a n)| ≤ |a n| + |L - a n| := by apply abs_add_le
        rewrite [<- f1, h2] at f2 -- |L| ≤ |a n| + |a n - L|
        have h3 : |a n| ≥ |L|/2 := by bound
        have h4 : |a n * L| ≥ |L|/2 * |L| := by
            rewrite [abs_mul]
            bound
        rewrite [bEqInva]
        specialize f (a n) (L) (by norm_num at * ; apply a_nzero) LneZero
        rewrite [f, abs_div, h2]
        have h' : |a n * L| > 0 := by rewrite [abs_mul] ; bound
        have f3 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : x ≥ y -> ε * x ≥ ε * y := by
            bound
        have h5 : ε * (|L|^2/2) ≤ ε * |a n * L| := by bound
        have f4 : |a n - L| < (|L|^2/2) * ε -> |a n - L| < ε * |a n * L| := by bound
        specialize f4 hN
        have f5 : |a n - L| < ε * |a n * L| ->
            |a n - L| / |a n * L| < ε * |a n * L| / |a n * L| := by
                intro f'
                bound
        specialize f5 f4
        have f6 : ε * |a n * L| / |a n * L| = ε := by field_simp
        field_simp at f5
        apply f5
/--
    37.
-/
theorem EventuallyGeHalfLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) :
    ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
        have h_pos (LneZero : L ≠ 0) : ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
            apply EventuallyGeHalfLimPos ; apply aToL ; apply LneZero
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at aToL
        have thm : L = 0 -> ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
            intro hl
            specialize aToL 1 (by bound)
            choose N hN using aToL
            specialize hN N (by bound)
            use N
            intro n hn
            rewrite [hl] at ⊢ hN ; norm_num at ⊢ hN
        by_cases h' : L ≠ 0
        apply h_pos h'
        norm_num at h'
        apply thm h'
/--
    38.
-/
theorem EventuallyBdd_of_SeqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) :
    ∃ N, ∀ n ≥ N, |a n| ≤ 2 * |L| := by
        have f_sub_tri (x y : ℝ) : |x| - |y| ≤ |x - y| := by
            have h' : |x| ≤ |x - y| + |y| := by
                have hh : |x| = |x - y + y| := by ring_nf
                rewrite [hh]
                apply abs_add_le
            linarith
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at ha
        have h : |L| > 0 := by
            rewrite [<- abs_pos] at hL ; bound
        specialize ha (|L|) (by bound)
        choose N hN using ha
        use N
        intro n hn
        specialize hN n hn
        specialize f_sub_tri (a n) (L)
        have f1 : |a n| < 2 * |L| := by bound
        bound
/--
    39.
-/
example (a b : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M) (hLM : L < M) :
    ∃ N, ∀ n ≥ N, a n < b n := by
        have f_sub_tri (x y : ℝ) : |x| - |y| ≤ |x - y| := by
            have h' : |x| ≤ |x - y| + |y| := by
                have hh : |x| = |x - y + y| := by ring_nf
                rewrite [hh]
                apply abs_add_le
            linarith
        have l_neq_m : L ≠ M := by by_contra heq ; linarith
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε at ha
        change ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |b n - M| < ε at hb
        specialize ha ((M - L)/4) (by bound) ; specialize hb ((M - L)/4) (by bound)
        choose aN haN using ha ; choose bN hbN using hb
        use aN + bN
        intro n hn
        specialize haN n (by bound) ; specialize hbN n (by bound)
        rewrite [abs_lt] at haN hbN
        have ha_lower : a n > L - ((M - L)/4) := by linarith [haN]
        have hb_upper : b n < M + ((M - L)/4) := by linarith [hbN]
        have key : L - ((M - L)/4) < M + ((M - L)/4) := by bound
        linarith
/--
    Lemma storage.
-/
example : True := by
    have sub_tri (x y : ℝ) : |x| - |y| ≤ |x - y| := by
        have h' : |x| ≤ |x - y| + |y| := by
            have hh : |x| = |x - y + y| := by ring_nf
            rewrite [hh]
            apply abs_add_le
        linarith
    have inv_sub (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
            (1/x) - (1/y) = (y/(x * y)) - (x/(x * y)) := by
                field_simp
    have sum_ge_zero (L M : ℝ) (hLM : L < M) : |L| + |M| > 0 := by
            by_cases h' : L = 0
            case pos =>
                have m_neq : M ≠ 0 := by
                    by_contra hm
                    linarith
                rewrite [h'] ; norm_num at *
                apply m_neq
            case neg =>
                have hz : L ≠ 0 := by
                    norm_num ; apply h'
                have hz' : |L| > 0 := by
                    rewrite [<- abs_pos] at hz
                    bound
                have hz'' : |M| ≥ 0 := by bound
                bound
    have diff_ne_zero (L M : ℝ) (hLM : L < M) : |M - L| > 0 := by
            by_cases h' : L = 0
            case pos =>
                have m_neq : M ≠ 0 := by
                    by_contra hm
                    linarith
                rewrite [h'] ; norm_num at *
                apply m_neq
            case neg =>
                have hz : L ≠ 0 := by norm_num ; apply h'
                have hz' : |L| > 0 := by
                    rewrite [<- abs_pos] at hz
                    bound
                have hz'' : |M| ≥ 0 := by bound
                have hm : M - L ≠ 0 := by
                    linarith
                rewrite [<- abs_pos] at hm
                bound
    apply True.intro
