/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.1.1
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring

-- 2.1.2
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 : m + 3 ≤ 9 := calc
    m + 3
    _ ≤ 2 * n - 1 := by rel [h1]
    _ ≤ 2 * 5 - 1 := by rel [h2]
    _ = 9 := by numbers
  addarith [h3]

-- 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4]
    _ = 3 := by ring

-- 2.1.4
example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = 3 * t := calc
    t * t
    _ = t ^ 2 := by ring
    _ = 3 * t := by rw [h1]
  cancel t at h3
  addarith [h3]

-- 2.1.5
example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 : a ^ 2 ≥ 1 ^ 2 := calc
    a ^ 2
    _ = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3

-- 2.1.6
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hx1 : x ≤ -1 := by addarith [hx]
  calc
    y ≥ 3 - 2 * x := by addarith [hy]
    _ ≥ 3 - 2 * -1 := by rel [hx1]
    _ > 3 := by numbers

-- 2.1.7
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ b + a := by addarith [h1]
  have h4 : 0 ≤ b - a := by addarith [h2]
  calc
    a ^ 2
    _ ≤ a ^ 2 + (b + a) * (b - a) := by extra
    _ = b ^ 2 := by ring

-- 2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : 0 ≤ b - a := by addarith [h]
  calc
    a ^ 3
    _ ≤ a ^ 3 + ((b - a) * ((b - a) ^ 2 + 3 * (b + a) ^ 2)) / 4 := by extra
    _ = b ^ 3 := by ring

/-! # Exercises -/

-- 2.1.9.1
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x * (x + 2) = 2 * (x + 2) := by calc
    x * (x + 2)
    _ = x ^ 2 + 2 * x := by ring
    _ = 4 + 2 * x := by rw [h1]
    _ = 2 * (x + 2) := by ring
  cancel (x + 2) at h3

-- 2.1.9.2
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 : (n - 2) ^ 2 = 0 ^ 2 := by calc
    (n - 2) ^ 2
    _ = (n ^ 2 + 4) - 4 * n := by ring
    _ = 4 * n - 4 * n := by rw [hn]
    _ = 0 ^ 2 := by ring
  cancel 2 at h1
  addarith [h1]

-- 2.1.9.3
example (x y : ℚ) (h1 : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h3 : x / x = 1 := by exact div_self (left_ne_zero_of_mul_eq_one h1)
  calc
    y = y * 1 := by ring
    _ = y * (x / x) := by rw [← h3]
    _ = (x * y) / x := by ring
    _ = 1 / x := by rw [h1]
    _ ≤ 1 := by exact div_le_self rfl h2
