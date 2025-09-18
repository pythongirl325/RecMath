import Mathlib.Tactic
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Algebra.BigOperators.Basic

-- open BigOperators
-- open Finset

-- Based on matt parker's video: https://www.youtube.com/watch?v=MhJN9sByRS0

-- #check Nat.dvd_sub


abbrev VideoStatement : Prop := ∀ (b n : Nat), b - 1 ∣ b^n - 1

example : VideoStatement := by
  intro b n
  induction n generalizing b with
  | zero => norm_num
  | succ n hn =>
    rw [pow_succ]
    cases b with
    | zero => grind only
    | succ b =>
      specialize hn (b + 1)
      rw [Nat.add_one_sub_one]
      rw [mul_add]
      rw [mul_one]
      -- rw [mul_comm]
      rw [Nat.add_sub_assoc (Nat.one_le_pow' _ _)]
      grind [
        = mul_add, = mul_one, = mul_comm,
        <- Nat.one_le_pow',
        = Nat.add_sub_assoc,
        ← Nat.dvd_add, ← Nat.dvd_mul_right
      ]

theorem video_theorem3 : VideoStatement := by
  intro b n
  induction n with
  | zero => norm_num
  | succ n hn =>
    rw [pow_succ]
    cases b with
    | zero => grind only
    | succ b =>
      rw [Nat.add_one_sub_one, mul_add, mul_one, mul_comm]
      rw [Nat.add_sub_assoc (Nat.one_le_pow' _ _)]
      exact Nat.dvd_add (Nat.dvd_mul_right _ _) hn

theorem video_theorem {b n : Nat} : b - 1 ∣ b^n - 1 := by
  induction' n with n hn
  · norm_num
  rw [pow_succ]
  cases' b with bs
  · norm_num
  rw [Nat.add_one_sub_one, mul_add, mul_one, mul_comm, Nat.add_sub_assoc (Nat.one_le_pow' _ _)]
  exact Nat.dvd_add (Nat.dvd_mul_right _ _) hn

-- theorem video_theorem2 {b n : Nat} : x - 1 ∣ x^n - 1 := by
--   use ∑ m in range n, x^m
--   symm
--   calc (x - 1) * ∑ m ∈ range n, x ^ m
--     _ = ∑ m ∈ range n, x ^ m * (x - 1) := by rw [mul_comm, sum_mul]
--     _ = ∑ m ∈ range n, (x^(m+1) - x^m) := by sorry
--     _ = ∑ m ∈ range n, x^(m+1) - ∑ m ∈ range n, x^m := by sorry
--     _ = x^n - 1 := by sorry

#check sub_one_dvd_pow_sub_one
