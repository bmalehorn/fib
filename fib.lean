import logic standard classical data.nat data.list
open decidable nat list

namespace fib

definition fib : ℕ → ℕ,
           fib 0 := 0,
           fib 1 := 1,
           fib (succ (succ n)) := fib n + fib (succ n)


/-
   fₙ ≤ fₙ₊₁
-/
private theorem nondecreasing'' : ∀ n : ℕ, fib n ≤ fib (succ n),
        nondecreasing'' 0 :=
          (calc fib 0 = 0 : rfl
                ...   ≤ 0 + 1 : le_add_right
                ...   = fib 1 : rfl),
        nondecreasing'' (succ n) :=
          (calc fib (succ n) ≤ (fib n) + (fib (succ n)) : le_add_left)

/-
   1 ≤ fₙ₊₁
-/
theorem pos : ∀ n : ℕ, 1 ≤ fib (succ n),
        -- There is certainly an easier way to do this.
        pos 0 :=
          (calc 1 = fib (succ 0) : rfl
              ... ≤ fib (succ 0) + 0 : le_add_right),
        pos (succ n) :=
          (calc 1 ≤ fib (succ n) : pos n
              ... ≤ fib (succ (succ n)) : nondecreasing'' (succ n))


/-
   n
   ∑ fᵢ = fₙ₊₂ - 1
  i=0
-/
definition sum_to : ℕ → ℕ,
           sum_to 0 := fib 0,
           sum_to (succ n) := fib (succ n) + sum_to n


theorem sum_identity : ∀ n : ℕ, sum_to n = fib (succ (succ n)) - 1,
        sum_identity 0 :=
          (calc sum_to 0 = fib (succ (succ 0)) - 1 : rfl),
        sum_identity (succ n) :=
          (calc sum_to (succ n) = fib (succ n) + sum_to n : rfl
                ...             = fib (succ n) + (fib (succ (succ n)) - 1)
                                      : sum_identity n
                ...             = (fib (succ n) + fib (succ (succ n))) - 1
                                      : add_sub_assoc (pos (succ n)))


/-
   n
   ∑ fᵢ² = fₙ * fₙ₊₁
  i=0
-/
definition sum_squared : ℕ → ℕ,
           sum_squared 0 := 0,
           sum_squared (succ n) :=
             (fib (succ n)) * (fib (succ n)) + sum_squared n


theorem sum_squared_identity
        : ∀ n : ℕ, sum_squared n = fib n * fib (succ n),
        sum_squared_identity 0 :=
          (calc sum_squared 0 = 0 * 1 : zero_mul),
        sum_squared_identity (succ n) :=
          (calc sum_squared (succ n)
               = (fib (succ n)) * (fib (succ n)) + sum_squared n : rfl
           ... = (fib (succ n)) * (fib (succ n)) + (fib n) * (fib (succ n))
                     : sum_squared_identity n
           ... = (fib (succ n) + fib n) * fib (succ n) : mul.right_distrib
           ... = (fib n + fib (succ n)) * fib (succ n) : add.comm
           ... = fib (succ n) * fib (succ (succ n))    : mul.comm)


/-   -------------------------------------------------------------------
 |           _____         _                  _             __         |
 |          |__  /___  ___| | _____ _ __   __| | ___  _ __ / _|        |
 |            / // _ \/ __| |/ / _ \ '_ \ / _` |/ _ \| '__| |_         |
 |           / /|  __/ (__|   <  __/ | | | (_| | (_) | |  |  _|        |
 |          /____\___|\___|_|\_\___|_| |_|\__,_|\___/|_|  |_|          |
 |                                                                     |
 --------------------------------------------------------------------  -/


------------------------------------------
-- definitions
------------------------------------------

/-
  Note that we start at fib 2 instead of fib 0.
     1, 2, 3, 5, ...
  This is because if we used these Fibonacci numbers:
     0, 1, 1, 2, 3, 5, ...
  Many numbers would have multiple representations, using 0 or the "other" 1.
  e.g. 11 = 8 + 3 OR 8 + 2 + 1 OR 8 + 3 + 0
 -/
definition fibsum : list ℕ → ℕ,
           fibsum nil := 0,
           fibsum (x::xs) := fib (succ (succ x)) + fibsum xs

inductive nonadjacent : list ℕ → Prop :=
  empty : nonadjacent nil,
  singleton : ∀ n : ℕ, nonadjacent (n :: nil),
  cons : ∀ (n : ℕ) (m : ℕ) (xs : list ℕ)
           (H: succ (succ m) ≤ n)
           (Hxs : nonadjacent (m :: xs)),
             nonadjacent (n :: m :: xs)


------------------------------------------
-- helpers
------------------------------------------

-- writing this is faster than trying to find it in nat.lean.
private definition eq_to_le {a b : ℕ} (H: a = b) : a ≤ b :=
           (calc a = b : H
               ... ≤ b : le.refl)

theorem straddle : ∀ n : ℕ, ∃ i : ℕ, fib (succ (succ i)) ≤ succ n
                                     ∧ succ n < fib (succ (succ (succ i))),
        straddle 0 :=
         exists.intro 0
         (and.intro
          (calc fib (succ 1) ≤ fib (succ 1) + 0 : le_add_right
                         ... = succ 0 : rfl)
          (calc succ 0 < succ (succ 0) : lt.base
                   ... = fib (succ (succ 1)) : rfl)),
        straddle (succ n) :=
          exists.elim (straddle n)
           (assume i : ℕ,
            assume H : fib (succ (succ i)) ≤ succ n
                       ∧ succ n < fib (succ (succ (succ i))),
            have Hl : fib (succ (succ i)) ≤ succ n, from and.elim_left H,
            have Hr : succ n < fib (succ (succ (succ i))),
              from and.elim_right H,
            have Ha : succ (succ n) = fib (succ (succ (succ i))) ∨
                      succ (succ n) < fib (succ (succ (succ i))),
                      from eq_or_lt_of_le (succ_le_of_lt Hr),
            or.elim Ha

              (assume Heq : succ (succ n) = fib (succ (succ (succ i))),
              exists.intro (succ i)
               (and.intro
                (eq_to_le (eq.symm Heq))
                (calc succ (succ n) = fib (succ (succ (succ i))) : Heq
                      ... < succ (fib (succ (succ (succ i))))
                        : (lt_succ_of_le (le.refl (fib (succ (succ (succ i))))))
                      ... = 1 + fib (succ (succ (succ i))) : add.comm
                      ... ≤ fib (succ (succ i)) + fib (succ (succ (succ i)))
                        : (add_le_add_right (pos (succ i))
                                            (fib (succ (succ (succ i)))))
                     ... = fib (succ (succ (succ (succ i)))) : rfl)))

              (assume Hlt : succ (succ n) < fib (succ (succ (succ i))),
              exists.intro i
               (and.intro (le_of_lt (lt_succ_of_le Hl)) Hlt)))


theorem nondecreasing' : ∀ (a : ℕ) (b : ℕ), fib a ≤ fib (a + b),

        nondecreasing' a 0 :=
        have H: fib (a+0) < fib(a+0) ∨ fib(a+0) = fib(a+0),
          from or.intro_right (fib (a+0) < fib (a+0)) rfl,
          calc fib a = fib (a+0) : rfl
                 ... ≤ fib (a+0) : le_of_lt_or_eq H,

        nondecreasing' a (succ b) :=
        calc fib a ≤ fib (a+b) : nondecreasing' a b
               ... ≤ fib (succ (a+b)) : nondecreasing'' (a+b)
               ... = fib (a+(succ b)) : rfl

theorem nondecreasing : ∀ (a : ℕ) (b : ℕ) (H : a ≤ b), fib a ≤ fib b,
        nondecreasing a b H :=
        calc fib a ≤ fib (a+(b-a)) : nondecreasing' a (b-a)
               ... = fib b : add_sub_of_le H



-- helper function, passed in closure elements of weak_zeckendorf'.
private theorem zek_helper : ∀ (xs : list ℕ) (i : ℕ) (n : ℕ)
      (Hfibsum : fibsum (i::xs) = succ n) (Htail : nonadjacent xs)
      (Hi : fib (succ (succ i)) ≤ succ n ∧ succ n < fib (succ (succ (succ i)))),
      nonadjacent (i::xs),

      zek_helper nil i n Hfibsum Htail Hi := nonadjacent.singleton i,

      zek_helper (y::ys) i n Hfibsum Htail Hi :=
        have Hhead : succ (succ y) ≤ i,
         from by_contradiction
           (assume (Hfalse : ¬ (succ (succ y)) ≤ i),
              have Hgt : i < succ (succ y), from lt_of_not_le Hfalse,
              have Hge : succ i ≤ succ (succ y), from succ_le_of_lt Hgt,
              have Hfibge : fib (succ i) ≤ fib (succ (succ y)),
                   from nondecreasing (succ i) (succ (succ y)) Hge,
              have Hlies : succ n < fibsum (i::y::ys),
              from calc succ n < fib (succ (succ (succ i))) : and.elim_right Hi
                           ... = fib (succ i) + fib (succ (succ i)) : rfl
                           ... = fib (succ (succ i)) + fib (succ i) : add.comm
                           ... ≤ fib (succ (succ i)) + fib (succ (succ y))
                                  : add_le_add_left Hfibge
                           ... ≤ (fib (succ (succ i)) + fib (succ (succ y))) +
                                 fibsum ys : le_add_right
                           ... = fib (succ (succ i)) +
                                 (fib (succ (succ y)) + fibsum ys) : add.assoc
                           ... = fibsum (i::y::ys) : rfl,
               have Huh : succ n ≠ fibsum (i::y::ys),
                from nat.ne_of_lt Hlies,
               have Huh' : ¬ (succ n = fibsum (i::y::ys)), from Huh,
               have Hfibsum' : succ n = fibsum (i::y::ys), from
                 calc succ n = succ n : rfl
                         ... = fibsum (i::y::ys) : Hfibsum,
               absurd Hfibsum' Huh'),
         nonadjacent.cons i y ys Hhead Htail


private theorem weak_zeckendorf' : ∀ (n : ℕ) (c : ℕ) (H : n ≤ c),
                          ∃ xs : list ℕ, nonadjacent xs ∧ fibsum xs = n,

        weak_zeckendorf' (succ n) 0 H :=
        absurd (calc 0 < succ n : zero_lt_succ n ... ≤ 0 : H) (lt.irrefl 0),

        weak_zeckendorf' 0 c H :=
        have Hsum : 0 = fibsum nil, from rfl,
        have Hnadj : nonadjacent nil, from nonadjacent.empty,
        exists.intro nil (and.intro Hnadj Hsum),

        weak_zeckendorf' (succ n) (succ c) H :=
        exists.elim (straddle n)
         (assume (i : ℕ)
                 (Hi : fib (succ (succ i)) ≤ succ n
                       ∧ succ n < fib (succ (succ (succ i)))),
          have Hpos : 1 ≤ fib (succ (succ i)), from pos (succ i),
          -- "smaller term" proof
          have Hless : succ n - fib (succ (succ i)) ≤ c,
          from calc succ n - fib (succ (succ i))
                        ≤ succ n - 1 : sub_le_sub_left (pos (succ i)) (succ n)
                    ... = n : rfl
                    ... ≤ c : le_of_succ_le_succ H,
          have HIH : (∃ xs : list ℕ,
                     nonadjacent xs ∧ fibsum xs = succ n - fib (succ (succ i))),
          from weak_zeckendorf' (succ n - fib (succ (succ i))) c Hless,
          exists.elim HIH
          (assume
              (xs : list ℕ)
              (Hxs : nonadjacent xs ∧ fibsum xs = succ n - fib (succ (succ i))),
           have Hfibeq : fibsum xs = succ n - fib (succ (succ i)),
                from and.elim_right Hxs,
           -- 1/2
           have Hfibsum : fibsum (i::xs) = succ n,
            from calc fibsum (i::xs)
                          = fib (succ (succ i)) + fibsum xs : rfl
                      ... = fib (succ (succ i)) + (succ n - fib (succ (succ i)))
                                                       : Hfibeq
                      ... = succ n : add_sub_of_le (and.elim_left Hi),
           -- 1/2
           have Hnonadjacent : nonadjacent (i::xs),
             from zek_helper xs i n Hfibsum (and.elim_left Hxs) Hi,

           exists.intro (i::xs) (and.intro Hnonadjacent Hfibsum)))

------------------------------------------
-- zeckendorf
------------------------------------------

theorem weak_zeckendorf : ∀ (n : ℕ),
                          ∃ xs : list ℕ, nonadjacent xs ∧ fibsum xs = n,
        weak_zeckendorf n := weak_zeckendorf' n n (le.refl n)

end fib
