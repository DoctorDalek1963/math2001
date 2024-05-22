/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int

-- 3.1.1
example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers

-- 3.1.2
example : Odd (-3 : ℤ) := by
  dsimp [Odd]
  use -2
  numbers

-- 3.1.3
example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc 3 * n + 2
    _ = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

-- 3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc 7 * n - 4
    _ = 7 * (2 * k + 1) - 4 := by rw [hk]
    -- _ = 14 * k + 3 := by ring
    _ = 2 * (7 * k + 1) + 1 := by ring

-- 3.1.5
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  calc x + y + 1
    _ = 2 * a + 1 + (2 * b + 1) + 1 := by rw [ha, hb]
    _ = 2 * (a + b + 1) + 1 := by ring

-- 3.1.6
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + 3 * b + 1
  calc x * y + 2 * y
    _ = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1) := by rw [ha, hb]
    -- _ = 4 * a * b + 2 * a + 2 * b + 1 + 4 * b + 2 := by ring
    -- _ = 4 * a * b + 2 * a + 6 * b + 3 := by ring
    _ = 2 * (2 * a * b + a + 3 * b + 1) + 1 := by ring

-- 3.1.7
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨t, ht⟩ := hm
  use 3 * t - 1
  calc 3 * m - 5
    _ = 3 * (2 * t + 1) - 5 := by rw [ht]
    -- _ = 6 * t + - 2 := by ring
    _ = 2 * (3 * t - 1) := by ring

-- 3.1.8
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc n ^ 2 + 2 * n - 5
    _ = (2 * k) ^ 2 + 2 * (2 * k) - 5 := by rw [hk]
    -- _ = 4 * k ^ 2 + 4 * k - 5 := by ring
    _ = 2 * (2 * k ^ 2 + 2 * k - 3) + 1 := by ring

-- 3.1.9
example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n

  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc n ^ 2 + n + 4
      _ = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring

  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc n ^ 2 + n + 4
      _ = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/

-- 3.1.10.1
example : Odd (-9 : ℤ) := by
  use -5
  numbers

-- 3.1.10.2
example : Even (26 : ℤ) := by
  use 13
  numbers

-- 3.1.10.3
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc n + m
    _ = 2 * b + (2 * a + 1) := by rw [ha, hb]
    _ = 2 * (a + b) + 1 := by ring

-- 3.1.10.4
example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  use a - b - 2
  calc p - q - 4
    _ = (2 * a + 1) - (2 * b) - 4 := by rw [ha, hb]
    _ = 2 * (a - b - 2) + 1 := by ring

-- 3.1.10.5
example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use 3 * x + y - 1
  calc 3 * a + b - 3
    _ = 3 * (2 * x) + (2 * y + 1) - 3 := by rw [hx, hy]
    _ = 2 * (3 * x + y - 1) := by ring

-- 3.1.10.6
example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  use 3 * a - 5 * b - 1
  calc 3 * r - 5 * s
    _ = 3 * (2 * a + 1) - 5 * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (3 * a - 5 * b - 1) := by ring

-- 3.1.10.7
example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  calc x ^ 3
    _ = (2 * k + 1) ^ 3 := by rw [hk]
    _ = 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k) + 1 := by ring

-- 3.1.10.8
example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 - k
  calc n ^ 2 - 3 * n + 2
    _ = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw [hk]
    -- _ = 4 * k ^ 2 + 4 * k + 1 - 6 * k - 3 + 2 := by ring
    _ = 2 * (2 * k ^ 2 - k) := by ring

-- 3.1.10.9
example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk⟩ := ha
  use 2 * k ^ 2 + 4 * k - 1
  calc a ^ 2 + 2 * a - 4
    _ = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw [hk]
    -- _ = 4 * k ^ 2 + 4 * k + 1 + 4 * k + 2 - 4 := by ring
    _ = 2 * (2 * k ^ 2 + 4 * k - 1) + 1 := by ring

-- 3.1.10.10
example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk⟩ := hp
  use 2 * k ^ 2 + 5 * k - 1
  calc p ^ 2 + 3 * p - 5
    _ = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw [hk]
    -- _ = 4 * k ^ 2 + 4 * k + 1 + 6 * k + 3 - 5 := by ring
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring

-- 3.1.10.11
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a * b + a + b
  calc x * y
    _ = (2 * a + 1) * (2 * b + 1) := by rw [ha, hb]
    _ = 2 * (2 * a * b + a + b) + 1 := by ring

-- 3.1.10.12
example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd n

  -- Even n
  · use 6 * k ^ 2 + 3 * k - 1
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k) ^ 2 + 3 * (2 * k) - 1 := by rw [hk]
      -- _ = 12 * k ^ 2 + 6 * k - 1 := by ring
      _ = 2 * (6 * k ^ 2 + 3 * k - 1) + 1 := by ring

  -- Odd n
  · use 6 * k ^ 2 + 9 * k + 2
    calc 3 * n ^ 2 + 3 * n - 1
      _ = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1 := by rw [hk]
      _ = 3 * (4 * k ^ 2 + 4 * k + 1) + 6 * k + 3 - 1 := by ring
      _ = 2 * (6 * k ^ 2 + 9 * k + 2) + 1 := by ring

-- 3.1.10.13
example (n : ℤ) : ∃ m ≥ n, Odd m := by
  obtain hn_le0 | hn_ge1 := le_or_succ_le n 0

  -- hn_le0 : n ≤ 0
  · use 1
    constructor
    -- 1 ≥ n
    · calc
        1 ≥ 0 := by numbers
        _ ≥ n := by rel [hn_le0]
    -- Odd 1
    · use 0
      ring

  -- hn_ge1 : 1 ≤ n
  · use 2 * n + 1
    constructor
    -- 2 * n + 1 ≥ n
    · calc 2 * n + 1
        _ = n + (n + 1) := by ring
        _ ≥ 1 + (n + 1) := by rel [Int.add_le_add_right hn_ge1 (n + 1)]
        _ = n + 2 := by ring
        _ ≥ n := by extra
    -- Odd (2 * n + 1)
    · use n
      ring

-- These lemmas are mine for Example 3.1.10.14
lemma even_plus_even {a b : ℤ} (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x + y
  calc a + b = 2 * (x + y) := by rw [hx, hy]; ring

lemma even_minus_even {a b : ℤ} (ha : Even a) (hb : Even b) : Even (a - b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x - y
  calc a - b = 2 * (x - y) := by rw [hx, hy]; ring

lemma odd_plus_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x + y + 1
  calc a + b = 2 * (x + y + 1) := by rw [hx, hy]; ring

lemma odd_minus_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) : Even (a - b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  use x - y
  calc a - b = 2 * (x - y) := by rw [hx, hy]; ring

-- 3.1.10.14
-- There's probably a better way to do this instead of analysing all 6 cases, but this works
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain ha_even | ha_odd := Int.even_or_odd a

  -- Even a
  · obtain hb_even | hb_odd := Int.even_or_odd b
    -- Even b
    · left
      exact even_minus_even ha_even hb_even
    -- Odd b
    · obtain hc_even | hc_odd := Int.even_or_odd c
      -- Even c
      · right
        left
        exact even_plus_even ha_even hc_even
      -- Odd c
      · right
        right
        exact odd_minus_odd hb_odd hc_odd

  -- Odd a
  · obtain hb_even | hb_odd := Int.even_or_odd b
    -- Even b
    · obtain hc_even | hc_odd := Int.even_or_odd c
      -- Even c
      · right
        right
        exact even_minus_even hb_even hc_even
      -- Odd c
      · right
        left
        exact odd_plus_odd ha_odd hc_odd
    -- Odd b
    · left
      exact odd_minus_odd ha_odd hb_odd
