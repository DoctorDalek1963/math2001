/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  calc
    y ^ 2 + 1
    _ ≥ 1 := by extra
    _ > 0 := by numbers

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm

  -- a ^ 2 ≤ 0
  calc
    a ^ 2
    _ ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1

  -- a ^ 2 ≥ 0
  extra

/-! # Exercises -/

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have h : m = 4 := by addarith [hm]
  calc
    3 * m
    _ = 3 * 4 := by rw [h]
    _ > 6 := by numbers

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm

  -- s ≤ -2
  have h : 3 * s ≤ 3 * -2 := by calc
    3 * s
    _ ≤ -6 := h1
    _ = 3 * -2 := by numbers

  cancel 3 at h

  -- s ≥ -2
  have h : 2 * s ≥ 2 * -2 := by calc
    2 * s
    _ ≥ -4 := h2
    _ = 2 * -2 := by numbers

  cancel 2 at h
