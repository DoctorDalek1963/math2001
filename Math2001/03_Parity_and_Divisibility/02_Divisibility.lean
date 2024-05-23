/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

-- 3.2.1
example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
  numbers

-- 3.2.2
example : (-2 : ℤ) ∣ 6 := by
  use -3
  numbers

-- 3.2.3
example {a b : ℤ} (hab : a ∣ b) : a ∣ b ^ 2 + 2 * b := by
  obtain ⟨k, hk⟩ := hab
  use k * (a * k + 2)
  calc b ^ 2 + 2 * b
    _ = (a * k) ^ 2 + 2 * (a * k) := by rw [hk]
    _ = a * (k * (a * k + 2)) := by ring

-- 3.2.4
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  use x ^ 2 * y
  calc
    c = b ^ 2 * y := hy
    _ = (a * x) ^ 2 * y := by rw [hx]
    _ = a ^ 2 * (x ^ 2 * y) := by ring

-- 3.2.5
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨k, hk⟩ := h
  use y * k
  calc
    z = x * y * k := hk
    _ = x * (y * k) := by ring

-- 3.2.6
example : ¬(5 : ℤ) ∣ 12 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use 2
  constructor
  · numbers -- show `5 * 2 < 12`
  · numbers -- show `12 < 5 * (2 + 1)`

-- 3.2.7
example {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
  obtain ⟨k, hk⟩ := hab
  have H1 :=
    calc
      0 < b := hb
      _ = a * k := hk
  cancel a at H1
  have H : 1 ≤ k := H1
  calc
    a = a * 1 := by ring
    _ ≤ a * k := by rel [H]
    _ = b := by rw [hk]

-- 3.2.8
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  have h := calc 0 * k
    _ = 0 := by ring
    _ < b := hb
    _ = a * k := hk
  cancel k at h

/-! # Exercises -/

-- 3.2.9.1
example (t : ℤ) : t ∣ 0 := by
  use 0
  ring

-- 3.2.9.2
example : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

-- 3.2.9.3
example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  use 3 * k - 4 * x * k ^ 2
  calc 3 * y - 4 * y ^ 2
    _ = 3 * (x * k) - 4 * (x * k) ^ 2 := by rw [hk]
    _ = x * (3 * k - 4 * x * k ^ 2) := by ring

-- 3.2.9.4
example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  use 2 * m ^ 2 * k ^ 3 + k
  calc 2 * n ^ 3 + n
    _ = 2 * (m * k) ^ 3 + (m * k) := by rw [hk]
    _ = m * (2 * m ^ 2 * k ^ 3 + k) := by ring

-- 3.2.9.5
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use 2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k
  calc 2 * b ^ 3 - b ^ 2 + 3 * b
    _ = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw [hk]
    _ = a * (2 * a ^ 2 * k ^ 3 - a * k ^ 2 + 3 * k) := by ring

-- 3.2.9.6
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x ^ 3 * y
  calc
    m = l ^ 3 * y := hy
    _ = (k * x) ^ 3 * y := by rw [hx]
    _ = k ^ 3 * (x ^ 3 * y) := by ring

-- 3.2.9.7
example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨x, hx⟩ := hpq
  obtain ⟨y, hy⟩ := hqr
  use x ^ 2 * y
  calc
    r = q ^ 2 * y := hy
    _ = (p ^ 3 * x) ^ 2 * y := by rw [hx]
    _ = p ^ 6 * (x ^ 2 * y) := by ring

-- 3.2.9.8
example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  constructor
  · numbers
  · use 7
    numbers

-- 3.2.9.9
example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 3, 2
  constructor
  · numbers
  · constructor
    · numbers
    · use 5
      numbers
