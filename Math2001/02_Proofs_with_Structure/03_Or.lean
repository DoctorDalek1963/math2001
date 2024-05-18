/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.3.1
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h

  -- hx : x = 1
  calc
    x * y + x
    _ = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring

  -- hy : y = -1
  calc
    x * y + x
    _ = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

-- 2.3.2
example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn

  -- hn : n ≤ 1
  apply ne_of_lt
  calc
    n ^ 2
    _ ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers

  -- hn: 2 ≤ n
  apply ne_of_gt
  calc
    n ^ 2
    _ ≥ 2 ^ 2 := by rel [hn]
    _ > 2 := by numbers

-- 2.3.3
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers

-- 2.3.4
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 := calc
    (x - 1) * (x - 2)
    _ = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  obtain hl | hr := eq_zero_or_eq_zero_of_mul_eq_zero h1

  -- hl : x - 1 = 0
  left
  calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [hl]
    _ = 1 := by numbers

  -- hr : x - 2 = 0
  right
  calc
    x = x - 2 + 2 := by ring
    _ = 0 + 2 := by rw [hr]
    _ = 2 := by numbers

-- 2.3.5
example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0

  -- hn0 : n ≤ 0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    -- hn : -n ≤ 1
    · apply ne_of_lt
      calc
        n ^ 2
        _ = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    -- hn : 2 ≤ -n
    · apply ne_of_gt
      calc
        (2 : ℤ)
        _ < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring

  -- hn0 : 1 ≤ n
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    -- hn : n ≤ 1
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers

    -- hn : 2 ≤ n
    · apply ne_of_gt
      calc
        (2 : ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]

/-! # Exercises -/

-- 2.3.6.1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain hp | hn := h

  -- hp : x = 4
  calc
    x ^ 2 + 1
    _ = 4 ^ 2 + 1 := by rw [hp]
    _ = 17 := by numbers

  -- hn : x = -4
  calc
    x ^ 2 + 1
    _ = (-4) ^ 2 + 1 := by rw [hn]
    _ = 17 := by numbers

-- 2.3.6.2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h

  -- h1 : x = 1
  calc
    x ^ 2 - 3 * x + 2
    _ = 1 ^ 2 - 3 * 1 + 2 := by rw [h1]
    _ = 0 := by numbers

  -- h2 : x = 2
  calc
    x ^ 2 - 3 * x + 2
    _ = 2 ^ 2 - 3 * 2 + 2 := by rw [h2]
    _ = 0 := by numbers

-- 2.3.6.3
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h

  -- h1 : t = -2
  calc
    t ^ 2 - t - 6
    _ = (-2) ^ 2 - (-2) - 6 := by rw [h1]
    _ = 0 := by numbers

  -- h2 : t = 3
  calc
    t ^ 2 - t - 6
    _ = 3 ^ 2 - 3 - 6 := by rw [h2]
    _ = 0 := by numbers

-- 2.3.6.4
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h

  -- hx : x = 2
  calc
    x * y + 2 * x
    _ = 2 * y + 2 * 2 := by rw [hx]
    _ = 2 * y + 4 := by ring

  -- hy : y = -2
  calc
    x * y + 2 * x
    _ = x * -2 + 2 * x := by rw [hy]
    _ = 2 * -2 + 4 := by ring
    _ = 2 * y + 4 := by rw [hy]

-- 2.3.6.5
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith [h]

-- 2.3.6.6
example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith [h]

-- 2.3.6.7
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  have h1 : (1 : ℝ) / 2 > 0 := by norm_num
  left
  calc
    x = (y - 1) / 2 := by addarith [h]
    _ = y / 2 - 1 / 2 := by ring
    _ < y / 2 := by exact sub_lt_self (y / 2) h1

-- 2.3.6.8
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h : (x + 3) * (x - 1) = 0 := by calc
    (x + 3) * (x - 1)
    _ = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := hx
  obtain h3 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h

  -- h3 : x + 3 = 0
  left
  calc
    x = x + 3 - 3 := by ring
    _ = 0 - 3 := by rw [h3]
    _ = -3 := by numbers

  -- h1 : x - 1 = 0
  right
  calc
    x = x - 1 + 1 := by ring
    _ = 0 + 1 := by rw [h1]
    _ = 1 := by numbers

-- 2.3.6.9
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h : (a - b) * (a - 2 * b) = 0 := by calc
    (a - b) * (a - 2 * b)
    _ = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
    _ = 0 := by addarith [hab]
  obtain h1 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h

  -- h1 : a - b = 0
  left
  addarith [h1]

  -- h2 : a - 2 * b = 0
  right
  addarith [h2]

-- 2.3.6.10
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  obtain h0 | hn0 := eq_or_ne t 0

  -- h0 : t = 0
  right
  exact h0

  -- hn0 : t ≠ 0
  left
  have h : (t ^ 2) * t = (t ^ 2) * 1 := by calc
    (t ^ 2) * t
    _ = t ^ 3 := by ring
    _ = t ^ 2 := ht
    _ = (t ^ 2) * 1 := by ring
  cancel (t ^ 2) at h

-- Same as previous (2.3.6.10), but with an alternative approach
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h : t ^ 2 * (t - 1) = 0 := by calc
    t ^ 2 * (t - 1)
    _ = t ^ 3 - t ^ 2 := by ring
    _ = t ^ 2 - t ^ 2 := by rw [ht]
    _ = 0 := by ring
  obtain h0 | h1 := eq_zero_or_eq_zero_of_mul_eq_zero h

  -- h0 : t ^ 2 = 0
  right
  exact pow_eq_zero h0

  -- h1 : t - 1 = 0
  left
  addarith [h1]

-- 2.3.6.11
example {n : ℕ} : n ^ 2 ≠ 7 := by
  obtain h1 | h2 := le_or_succ_le n 2

  -- h1 : n ≤ 2
  apply ne_of_lt
  calc
    n ^ 2
    _ ≤ 2 ^ 2 := by rel [h1]
    _ < 7 := by numbers

  -- h2: 3 ≤ n
  apply ne_of_gt
  calc
    n ^ 2
    _ ≥ 3 ^ 2 := by rel [h2]
    _ > 7 := by numbers

-- 2.3.6.12
example {x : ℤ} : 2 * x ≠ 3 := by
  obtain h1 | h2 := le_or_succ_le x 1

  -- h1 : x ≤ 1
  apply ne_of_lt
  calc
    2 * x
    _ ≤ 2 * 1 := by rel [h1]
    _ < 3 := by numbers

  -- h2 : 2 ≤ x
  apply ne_of_gt
  calc
    2 * x
    _ ≥ 2 * 2 := by rel [h2]
    _ > 3 := by numbers

-- 2.3.6.13
example {t : ℤ} : 5 * t ≠ 18 := by
  obtain h1 | h2 := le_or_succ_le t 3

  -- h1 : t ≤ 3
  apply ne_of_lt
  calc
    5 * t
    _ ≤ 5 * 3 := by rel [h1]
    _ < 18 := by numbers

  -- h2 : 4 ≤ t
  apply ne_of_gt
  calc
    5 * t
    _ ≥ 5 * 4 := by rel [h2]
    _ > 18 := by numbers

-- 2.3.6.14
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  obtain h1 | h2 := le_or_succ_le m 5

  -- h1 : x ≤ 5
  apply ne_of_lt
  calc
    m ^ 2 + 4 * m
    _ ≤ 5 ^ 2 + 4 * 5 := by rel [h1]
    _ < 46 := by numbers

  -- h2 : 6 ≤ x
  apply ne_of_gt
  calc
    m ^ 2 + 4 * m
    _ ≥ 6 ^ 2 + 4 * 6 := by rel [h2]
    _ > 46 := by numbers
