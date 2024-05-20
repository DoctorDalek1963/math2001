/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- 2.5.1
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

-- 2.5.2
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨a, hat⟩ := h
  obtain ha | ha := le_or_gt a 0

  -- ha : a ≤ 0
  · have hat' : 0 < (-a) * t := by addarith [hat]
    have ha' : 0 ≤ -a := by addarith [ha]
    cancel -a at hat'
    apply ne_of_gt
    exact hat'

  -- ha : a > 0
  · have hat' : a * t < a * 0 := by calc
      a * t < 0 := hat
      _ = a * 0 := by ring
    cancel a at hat'
    apply ne_of_lt
    exact hat'

-- 2.5.3
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers

-- 2.5.4
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra

-- 2.5.5
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

-- 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

-- 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor

  -- p < (p + q) / 2
  · calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]

  -- (p + q) / 2 < q
  · calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring

-- 2.5.8
example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers -- 1 ^ 3 + 12 ^ 3 = 1729
  constructor
  numbers -- 9 ^ 3 + 10 ^ 3 = 1729
  constructor
  numbers -- 1 ≠ 9
  numbers -- 1 ≠ 10

/-! # Exercises -/

-- 2.5.9.1
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 13 / 10
  numbers

-- 2.5.9.2
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 7, 6
  numbers

-- 2.5.9.3
example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  numbers -- -0.5 < 0
  numbers -- (-0.5) ^ 2 < 1

-- 2.5.9.4
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

-- 2.5.9.5
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  obtain hn | hp := lt_or_ge x 0

  -- hn : x < 0
  · use x - 1
    have h : (x - 1) ^ 2 - x > 0 := by calc
      (x - 1) ^ 2 - x
      _ = (x - 1) ^ 2 - x := by ring
      _ ≥ -x := by extra
      _ > 0 := by addarith [hn]

    calc
      (x - 1) ^ 2
      _ = ((x - 1) ^ 2 - x) + x := by ring
      _ > x := by extra

  -- hp : x ≥ 0
  · use x + 1
    calc
      (x + 1) ^ 2
      _ = (x ^ 2 + x + 1) + x := by ring
      _ > x := by extra

-- 2.5.9.6
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  obtain ht_eq1 | ht_ne1 := eq_or_ne t 1

  -- ht_eq1 : t = 1
  -- t = 1 → a + 1 < a + 1, therefore t = 1 must be false
  · rw [ht_eq1] at ha
    have ha' : a + 1 < a + 1 := by calc
      a + 1 = a * 1 + 1 := by ring
      _ < a + 1 := ha
    exact (LT.lt.false ha').elim

  · exact ht_ne1

-- 2.5.9.7
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, h⟩ := h
  obtain ha_le2 | ha_ge3 := le_or_succ_le a 2

  · apply ne_of_lt
    calc
      m = 2 * a := h.symm
      _ ≤ 2 * 2 := by rel [ha_le2]
      _ < 5 := by numbers

  · apply ne_of_gt
    calc
      m = 2 * a := h.symm
      _ ≥ 2 * 3 := by rel [ha_ge3]
      _ > 5 := by numbers

-- 2.5.9.8
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain hn_le0 | hn_gt0 := le_or_gt n 0

  -- hn_le0 : n ≤ 0
  · use 2
    have h : n * 2 + 7 ≤ 7 := calc
      n * 2 + 7
      _ ≤ 0 * 2 + 7 := by rel [hn_le0]
      _ = 7 := by numbers

    calc
      (2 : ℤ) * 2 ^ 3
      _ ≥ 7 := by numbers
      _ ≥ n * 2 + 7 := h

  -- hn_gt0 : n > 0
  · use n + 7
    calc 2 * (n + 7) ^ 3
      _ = 2 * n ^ 3 + 42 * n ^ 2 + 294 * n + 686 := by ring
      _ = (n * (n + 7) + 7) + (2 * n ^ 3 + 41 * n ^ 2 + 287 * n + 679) := by ring
      _ ≥ n * (n + 7) + 7 := by extra

-- 2.5.9.9
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  -- Without loss of generality, we can assume a ≤ b ≤ c, since all the variables are symmetric.
  -- This wlog boilerplate was written by David Renshaw and I took it from
  -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.E2.9C.94.20How.20to.20use.20symmetry.20in.20wlog.3F/near/439630291
  wlog h_order_ab : a ≤ b generalizing a b with H1
  · push_neg at h_order_ab
    rw [add_comm] at hc
    obtain ⟨x, y, z, hx, hy, hz, ha', hb', hc'⟩ := H1 hb ha hc h_order_ab.le
    rw [add_comm] at hc'
    exact ⟨y, x, z, hy, hx, hz, hb', ha', hc'⟩
  wlog h_order_bc : b ≤ c generalizing a b c with H2
  · push_neg at h_order_bc
    rcases le_total a c with hac | hac
    · rw [add_comm] at ha
      obtain ⟨x, y, z, hx, hy, hz, ha', hb', hc'⟩ := H2 ha hc hb hac h_order_bc.le
      rw [add_comm] at ha'
      exact ⟨x, z, y, hx, hz, hy, ha', hc', hb'⟩
    · rw [add_comm] at ha hb
      obtain ⟨x, y, z, hx, hy, hz, ha', hb', hc'⟩ := H2 hc ha hb hac h_order_ab
      rw [add_comm] at hb' hc'
      exact ⟨y, z, x, hy, hz, hx, hb', hc', ha'⟩

  -- We can also conclude that a, b, c ≥ 0.
  have ha' : a ≥ 0 := by
    -- If a < 0 then we get b < c and c < b, which is a contradiction.
    obtain ha_lt0 | ha_ge0 := lt_or_ge a 0
    · have hbc : b < c := by calc
        b ≤ a + c := hb
        _ < 0 + c := by rel [ha_lt0]
        _ = c := by ring
      have hcb : c < b := by calc
        c ≤ a + b := hc
        _ < 0 + b := by rel [ha_lt0]
        _ = b := by ring
      have h_contra : ¬ b < c := lt_asymm hcb
      contradiction
    · exact ha_ge0
  -- Since a ≥ 0 and a ≤ b ≤ c, we know that b ≥ 0 and c ≥ 0 as well.
  have hb' : b ≥ 0 := by calc
    b ≥ a := by rel [h_order_ab]
    _ ≥ 0 := ha'
  have hc' : c ≥ 0 := by calc
    c ≥ b := by rel [h_order_bc]
    _ ≥ 0 := hb'

  -- We can choose x, y, z to be the following:
  use (-a + b + c) / 2, (a - b + c) / 2, (a + b - c) / 2
  -- I found these values like so:
  --    Let x = t.
  --    Since c = x + y, y = c - x = c - t.
  --    Likewise, z = b - t.
  --    a = y + x = b + c - 2t.
  --    Therefore, t = (b + c - a) / 2.
  --    We can plug that back in to find y and z in terms of a, b, and c as well.

  constructor
  -- x ≥ 0
  · have h : -a + b + c ≥ 0 := by calc
      -a + b + c
      _ ≥ -a + a + c := by rel [h_order_ab]
      _ = c := by ring
      _ ≥ 0 := hc'
    calc (-a + b + c) / 2
      _ ≥ 0 / 2 := by rel [h]
      _ = 0 := by numbers

  constructor
  -- y ≥ 0
  · have h : a - b + c ≥ 0 := by calc
      a - b + c
      _ ≥ a - c + c := by rel [h_order_bc]
      _ = a := by ring
      _ ≥ 0 := ha'
    calc (a - b + c) / 2
      _ ≥ 0 / 2 := by rel [h]
      _ = 0 := by numbers

  constructor
  -- z ≥ 0
  · have h : a + b - c ≥ 0 := by calc
      a + b - c
      _ ≥ c - c := by rel [hc]
      _ = 0 := by ring
    calc (a + b - c) / 2
      _ ≥ 0 / 2 := by rel [h]
      _ = 0 := by numbers

  -- a = y + z
  constructor
  ring

  -- b = x + z
  constructor
  ring

  -- c = x + y
  ring
