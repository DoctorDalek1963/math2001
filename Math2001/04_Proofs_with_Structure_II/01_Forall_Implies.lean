/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 4.1.1
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers

-- 4.1.2
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers
  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  -- I feel like Lean is making a big jump here
  · apply Nat.pos_of_dvd_of_pos h1 h2

-- 4.1.2 (my version)
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by numbers

  have h3 : 0 < n := by apply Nat.pos_of_dvd_of_pos h1 h2
  have h4 : 1 ∣ n := by exact one_dvd n

  apply le_antisymm
  · apply Nat.le_of_dvd h2 h1
  · apply Nat.le_of_dvd h3 h4

-- 4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain h1 | h2 := h

  -- (a + b) / 2 ≥ a
  · calc
    b = 2 * ((a + b) / 2) - a := by ring
      _ ≥ 2 * a - a := by rel [h1]
      _ = a := by ring

  -- (a + b) / 2 ≤ b
  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel [h2]
      _ = b := by ring

-- 4.1.4
example {a b : ℝ}
    (ha1 : a ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb1 : b ^ 2 ≤ 2) (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b)
    : a = b := by
  apply le_antisymm

  -- Show a ≤ b
  · apply hb2
    apply ha1

  -- Show b ≤ a
  · apply ha2
    apply hb1

-- 4.1.5
example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _  = x ^ 2 - 2 * x := by ring

-- 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x y h

  have h1 := by calc (x + y) ^ 2
    _ ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ 3 ^ 2 := by numbers

  have h2 : (0 : ℝ) ≤ 3 := by numbers
  exact (abs_le_of_sq_le_sq' h1 h2).left

-- 4.1.7
example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5
  intro n hn
  calc n ^ 3
    _ = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra

-- 4.1.8
example : Prime 2 := by
  constructor
  -- Show 2 ≤ 2
  · numbers
  -- Show that only 1 and 2 divide 2
  · intro m hmp
    have hp : 0 < 2 := by numbers
    have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
    have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
    interval_cases m
    · left
      numbers -- 1 = 1
    · right
      numbers -- 2 = 2

-- 4.1.9
example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- 2 ≠ 1
  · numbers -- 2 ≠ 6
  · numbers -- 6 = 2 * 3

/-! # Exercises -/

-- 4.1.10.1
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  calc
    a ≥ -3 + 4 * 2 - 2 ^ 2 := by apply h
    _ = 1 := by numbers

-- 4.1.10.2
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h3 : 3 ∣ n := by
    apply hn
    numbers
    numbers

  have h5 : 5 ∣ n := by
    apply hn
    numbers
    numbers

  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h5
  use 2 * a - 3 * b
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * a) - 9 * n := by rw [ha]
    _ = 10 * (3 * a) - 9 * (5 * b) := by rw [hb]
    _ = 15 * (2 * a - 3 * b) := by ring

-- 4.1.10.3
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  exact Nat.zero_le

-- 4.1.10.4
example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0
  intro b
  use b + 1
  calc 0 + b
    _ = b := by ring
    _ < b + 1 := by extra

-- 4.1.10.5
example : forall_sufficiently_large x : ℝ,
    x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  dsimp
  use 7
  intro x h
  calc x ^ 3 + 3 * x
    _ = x * x ^ 2 + 3 * x := by ring
    _ ≥ 7 * x ^ 2 + 3 * 7 := by rel [h]
    _ = 7 * x ^ 2 + 12 + 9 := by ring
    _ ≥ 7 * x ^ 2 + 12 := by extra

-- 4.1.10.6
example : ¬(Prime 45) := by
  apply not_prime 5 9
  · numbers
  · numbers
  · numbers
