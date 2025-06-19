/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b,hb⟩ := h
  calc
    a = b ^ 2 + 1 := by rw [hb]
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain h1 | h2 := H
  . have hxt' : (-x) * t > 0 := by addarith [hxt]
    have h1' : (-x) >= 0 := by addarith [h1]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  . have hxt' : x * (-t) > 0 := calc
      x * (-t) = (-x) * t := by ring
      _ > 0 := by addarith [hxt]
    cancel x at hxt'
    have h1' : t < 0 := by addarith [hxt']
    apply ne_of_lt
    apply h1'

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6,5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use (a + 1), a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  constructor
  . calc
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by rel [h]
  . calc
      q = (q + q) / 2 := by ring
      _ > (p + q) / 2 := by rel [h]

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1,12,9,10
  constructor
  . numbers
  . constructor
    . numbers
    . constructor
      . numbers
      . numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  ring

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6, 7
  ring

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  . numbers
  . numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use (x + 1/2)
  calc
    (x + 1/2) ^ 2 = x ^ 2 + x + 1/4 := by ring
    _ = x + (x ^ 2 + 1/4) := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  have h1 : (1 - x) * (t - 1) > 0 := by
    calc
      (1 - x) * (t - 1) = x + t - (x * t + 1) := by ring
      _ > (x * t + 1) - (x * t + 1) := by rel [hxt]
      _ = 0 := by ring
  have h2 := le_or_gt x 1
  obtain hx_le_1 | hx_gt_1 := h2
  . have h3 : 1 - x >= 0 := by addarith [hx_le_1]
    cancel (1 - x) at h1
    have h4 : t > 1 := by addarith [h1]
    apply ne_of_gt
    apply h4
  . have h3 : (x - 1) * (1 - t) > 0 := by
      calc
        (x - 1) * (1 - t) = x + t - (x * t + 1) := by ring
        _ > (x * t + 1) - (x * t + 1) := by rel [hxt]
        _ = 0 := by ring
    have h4 : x - 1 > 0 := by addarith [hx_gt_1]
    cancel (x - 1) at h3
    have h5 : t < 1 := by addarith [h3]
    apply ne_of_lt
    apply h5


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ham⟩ := h
  have H := le_or_succ_le a 2
  obtain h_le_2 | h_ge_3 := H
  apply ne_of_lt
  calc
    m = 2 * a := by rw [ham]
    _ <= 2 * 2 := by rel [h_le_2]
    _ = 4 := by ring
    _ < 5 := by numbers
  apply ne_of_gt
  calc
    m = 2 * a := by rw [ham]
    _ >= 2 * 3 := by rel [h_ge_3]
    _ = 6 := by ring
    _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  obtain h_le_0 | h_gt_1 := le_or_succ_le n 0
  use 3
  calc
    n * 3 + 7 <= 0 * 3 + 7 := by rel [h_le_0]
    _ = 7 := by ring
    _ <= 54 := by numbers
    _ = 2 * 3 ^ 3 := by ring
  use (n + 1)
  calc
    2 * (n + 1) ^ 3 = 2 * n ^ 3 + 6 * n ^ 2 + 6 * n + 2 := by ring
    _ = 2 * n ^ 3 + 5 * n ^ 2 + 5 * n + n ^ 2 + n + 2 := by ring
    _ >= 2 * 1 ^ 3 + 5 * 1 ^ 2 + 5 * 1 + n ^ 2 + n + 2 := by rel [h_gt_1]
    _ = n ^ 2 + n + 7 + 7 := by ring
    _ >= n ^ 2 + n + 7 := by extra
    _ = n * (n + 1) + 7 := by ring



example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
