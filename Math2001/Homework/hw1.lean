/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 1

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-1,
for clearer statements and any special instructions. -/

@[autograded 5]
theorem problem1 {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  have h3 : q = 3 := by addarith [h2]
  calc
    p = 1 - 4 * q := by addarith [h1]
    _ = 1 - 4 * 3 := by rw [h3]
    _ = -11 := by numbers

@[autograded 5]
theorem problem2 {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  have h3 : b = a - 1 := by addarith [h2]

  have h4 : a = 6 - 2 * a := calc
    a = a + 2 * b - 2 * b := by ring
    _ = 4 - 2 * (a - 1) := by rw [h1, h3]
    _ = 6 - 2 * a := by ring

  have h5 : 3 * a = 3 * 2 := by calc
    3 * a
    _ = a + 2 * a := by ring
    _ = 6 := by addarith [h4]
    _ = 3 * 2 := by numbers

  cancel 3 at h5

@[autograded 5]
theorem problem3 {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
    _ = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
    _ ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * 9 := by rel [hx]
    _ = x * x + 18 := by ring
    _ ≥ 9 * 9 + 18 := by rel [hx]
    _ ≥ 3 := by numbers

@[autograded 5]
theorem problem4 {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by
  have h : x ^ 2 - 2 * x + 1 ≥ 0 := by calc
    x ^ 2 - 2 * x + 1
    _ = (x - 1) ^ 2 := by ring
    _ ≥ 0 := by exact sq_nonneg (x - 1)

  addarith [h]

@[autograded 5]
theorem problem5 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ b + a := by addarith [h1]
  have h4 : 0 ≤ b - a := by addarith [h2]
  calc
    a ^ 2
    _ ≤ a ^ 2 + (b + a) * (b - a) := by extra
    _ = b ^ 2 := by ring
