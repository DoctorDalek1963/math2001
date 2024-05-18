/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.4.1
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

-- 2.4.2
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc p ^ 2
      _ ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, _⟩ := hp'
  addarith [h1]

-- 2.4.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]

-- 2.4.3 (but done differently)
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · exact hb

-- 2.4.4
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc a ^ 2
      _ ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    exact sq_nonneg a

  have h3 : b ^ 2 = 0
  · calc b ^ 2
      _ = 0 + b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [h2]
      _ = 0 := by rw [h1]

  constructor
  exact pow_eq_zero h2
  exact pow_eq_zero h3

/-! # Exercises -/

-- 2.4.5.1
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * a + b
    _ = a + (a + b) := by ring
    _ ≤ 1 + 3 := by rel [h1, h2]
    _ = 4 := by numbers

-- 2.4.5.2
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc 2 * r
    _ = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel [h1, h2]
    _ = 6 := by numbers

-- 2.4.5.3
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m ≤ n - 5 := by addarith [h2]
    _ ≤ 8 - 5 := by rel [h1]
    _ = 3 := by numbers

-- 2.4.5.4
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp' : p ≥ 7 := by addarith [hp]
  constructor
  calc p ^ 2
    _ ≥ 7 ^ 2 := by rel [hp']
    _ = 49 := by numbers
  exact hp'

-- 2.4.5.5
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h' : a ≥ 6 := by addarith [h]
  constructor
  exact h'
  calc 3 * a
    _ ≥ 3 * 6 := by rel [h']
    _ ≥ 10 := by numbers

-- 2.4.5.6
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have hy : y = 2 := by calc
    y = (x + 2 * y) - (x + y) := by ring
    _ = 7 - 5 := by rw [h1, h2]
    _ = 2 := by numbers

  constructor
  calc
    x = (x + y) - y := by ring
    _ = 5 - 2 := by rw [h1, hy]
    _ = 3 := by numbers
  exact hy

-- 2.4.5.7
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have heq : a = b := by calc
    a = a * b := by rw [h1]
    _ = b := by rw [h2]

  obtain ha_eq0 | ha_ne0 := eq_or_ne a 0

  -- ha_eq0 : a = 0
  · left
    constructor

    -- a = 0
    exact ha_eq0

    -- b = 0
    have hb_eq0 : b = 0 := by calc
      b = a := heq.symm
      _ = 0 := ha_eq0
    exact hb_eq0

  -- ha_ne0 : a ≠ 0
  · right
    have b_eq1 : b = 1 := by
      have h1' : a * b = a * 1 := by calc
        a * b = a := h1
        _ = a * 1 := by ring
      cancel a at h1'

    constructor

    -- a = 1
    have h2' : a * b = 1 * b := by calc
      a * b = b := h2
      _ = 1 * b := by ring
    cancel b at h2'

    -- b = 1
    exact b_eq1
