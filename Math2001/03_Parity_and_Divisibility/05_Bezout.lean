/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

-- 3.5.1a
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring

-- 3.5.1b
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use 5 * a - 3 * n
  calc
    n = 5 * (5 * n) - 24 * n := by ring
    _ = 5 * (8 * a) - 24 * n := by rw [ha]
    _ = 8 * (5 * a - 3 * n) := by ring

-- 3.5.2
example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  use 2 * x - n
  calc
    n = 2 * (3 * n) - 5 * n := by ring
    _ = 2 * (5 * x) - 5 * n := by rw [hx]
    _ = 5 * (2 * x - n) := by ring

-- 3.5.3
example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/

-- 3.5.4.1
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨k, hk⟩ := hn
  use 2 * n - k
  calc
    n = 12 * n - 11 * n := by ring
    _ = 12 * n - 6 * k := by rw [hk]
    _ = 6 * (2 * n - k) := by ring

-- 3.5.4.2
example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨k, hk⟩ := ha
  use 3 * a - 4 * k
  calc
    a = 7 * 3 * a - 4 * (5 * a) := by ring
    _ = 7 * 3 * a - 4 * (7 * k) := by rw [hk]
    _ = 7 * (3 * a - 4 * k) := by ring

-- 3.5.4.3
example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use 4 * x - 5 * y
  calc
    n = 36 * n - 35 * n := by ring
    _ = 36 * (7 * x) - 35 * n := by rw [hx]
    _ = 36 * (7 * x) - 35 * (9 * y) := by rw [hy]
    _ = 63 * (4 * x - 5 * y) := by ring

-- 3.5.4.4
example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use 2 * x - 5 * y
  calc
    n = 26 * n - 25 * n := by ring
    _ = 26 * (5 * x) - 25 * n := by rw [hx]
    _ = 26 * (5 * x) - 25 * (13 * y) := by rw [hy]
    _ = 65 * (2 * x - 5 * y) := by ring
