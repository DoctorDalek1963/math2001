/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

-- 3.3.1
example : 11 ≡ 3 [ZMOD 4] := by
  use 2
  numbers

-- 3.3.2
example : -5 ≡ 1 [ZMOD 3] := by
  dsimp [Int.ModEq]
  use -2
  numbers

-- 3.3.3
theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc a + c - (b + d)
    _ = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

-- 3.3.4
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x - y
  calc a - c - (b - d)
    _ = a - b - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

-- 3.3.5
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  use -x
  calc -a - -b
    _ = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * -x := by ring

-- 3.3.6
theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc a * c - b * d
    _ = (a - b) * c + b * (c - d) := by ring
    _ = (n * x) * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

-- 3.3.8
theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc a ^ 2 - b ^ 2
    _ = (a - b) * (a + b) := by ring
    _ = (n * x) * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring

-- 3.3.9
theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a ^ 2 + a * b + b ^ 2)
  calc a ^ 3 - b ^ 3
    _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = (n * x) * (a ^ 2 + a * b + b ^ 2) := by rw [hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring

-- 3.3.9 extended
theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] := by
  -- Induction with multiplication rule
  induction k
  -- case zero
  · use 0
    calc a ^ 0 - b ^ 0
     _ = n * 0 := by ring

  -- case succ
  · case _ k k_ih =>
      rw [pow_succ a k, pow_succ b k]
      exact Int.ModEq.mul h k_ih

-- 3.3.10
theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring

-- 3.3.11a
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  obtain ⟨x, hx⟩ := ha
  use x * (b ^ 2 + a * b + 2 * b + 3)
  calc
    a * b ^ 2 + a ^ 2 * b + 3 * a - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2)
    _ = (a - 2) * (b ^ 2 + a * b + 2 * b + 3) := by ring
    _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
    _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring

-- 3.3.11b
example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 * a ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
  apply Int.ModEq.add
  · apply Int.ModEq.add
    · apply Int.ModEq.mul
      · apply ha
      · apply Int.ModEq.refl
    · apply Int.ModEq.mul
      · apply Int.ModEq.pow
        apply ha
      · apply Int.ModEq.refl
  · apply Int.ModEq.mul
    · apply Int.ModEq.refl
    · apply ha

/-! # Exercises -/

-- 3.3.12.1
example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  numbers

-- 3.3.12.2
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨k, hk⟩ := h
  use -k
  calc b - a
    _ = -(a - b) := by ring
    _ = -(n * k) := by rw [hk]
    _ = n * -k := by ring

-- 3.3.12.3
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc a - c
    _ = (a - b) + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

-- 3.3.12.4
example : a + n * c ≡ a [ZMOD n] := by
  use c
  ring

-- 3.3.12.6
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  · apply Int.ModEq.mul
    · apply Int.ModEq.refl
    · exact h
  · apply Int.ModEq.refl

-- 3.3.12.7
example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  apply Int.ModEq.sub
  · apply Int.ModEq.mul
    · apply Int.ModEq.refl
    · exact h
  · apply Int.ModEq.refl

-- 3.3.12.8
example {k : ℤ} (h : k ≡ 3 [ZMOD 5]) : 4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  · apply Int.ModEq.add
    · apply Int.ModEq.mul
      · apply Int.ModEq.refl
      · exact h
    · apply Int.ModEq.pow_three
      exact h
  · apply Int.ModEq.refl
