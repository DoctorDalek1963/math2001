/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

-- 4.2.1
example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  -- =>
  · intro h
    calc
      a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  -- <=
  · intro h
    calc 3 * a + 1
      _ ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers

-- 4.2.2
example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  -- =>
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  -- <=
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n
      _ = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring

-- 4.2.3
theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    -- dsimp [Int.ModEq]
    -- dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]

-- 4.2.4
theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    -- dsimp [Int.ModEq]
    -- dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    addarith [hk]

-- 4.2.5
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have h1 := calc (x + 3) * (x - 2)
      _ = x ^ 2 + x - 6 := by ring
      _ = 0 := h
    have h2 : x + 3 = 0 ∨ x - 2 = 0 := zero_eq_mul.mp (id h1.symm)
    obtain hx3 | hx2 := h2
    · left
      addarith [hx3]
    · right
      addarith [hx2]
  · intro h
    obtain hx3 | hx2 := h
    · calc x ^ 2 + x - 6
        _ = (-3) ^ 2 + (-3) - 6 := by rw [hx3]
        _ = 0 := by numbers
    · calc x ^ 2 + x - 6
        _ = 2 ^ 2 + 2 - 6 := by rw [hx2]
        _ = 0 := by numbers

-- 4.2.6
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  sorry

-- 4.2.7a
example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  sorry

-- 4.2.7b
example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  sorry

-- 4.2.8
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra

-- 4.2.9
example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · sorry

/-! # Exercises -/

-- 4.2.10.1
example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  sorry

-- 4.2.10.2
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  sorry

-- 4.2.10.3
theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  sorry

-- 4.2.10.4
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  sorry

-- 4.2.10.5
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry
