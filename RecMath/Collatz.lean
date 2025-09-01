import Mathlib.Tactic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
-- import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Defs.Basic

def step (n : Nat) : Nat :=
  if Even n then
    n / 2
  else
    3 * n + 1

theorem step.odd_even {n} (h : Odd n) : Even (step n) := by
  simp only [step, Nat.not_even_iff_odd.mpr h]
  apply Odd.add_odd
  · exact Nat.odd_mul.mpr ⟨by decide, h⟩
  · decide

theorem step.not_injective : ¬ step.Injective := by
  rw [Function.Injective]
  push_neg
  use 1, 8; decide

theorem step.surjective : step.Surjective := by
  intro n
  use 2 * n
  simp [step]

def step.continuous : Continuous step where
  isOpen_preimage := by simp

theorem step.minimalPeriod_one : step.minimalPeriod 1 = 3 := by
  apply Function.minimalPeriod_eq_prime <;> decide

theorem step.one_had_period_3 : step.IsPeriodicPt 3 1 := by decide

theorem step.isPeriodicPt_one : 1 ∈ step.periodicPts := by
  rw [Function.mem_periodicPts]
  use 3; decide

def step.periodicOrbit_one : Cycle Nat :=
  ↑(List.map (fun (n : ℕ) => step^[n] 1) (List.range 3))

theorem step.periodicOrbit_one_def : step.periodicOrbit 1 = step.periodicOrbit_one := by
  rw [Function.periodicOrbit, step.minimalPeriod_one]
  decide

theorem step.fixedZero : step.fixedPoints = {0} := by
  rw [Function.fixedPoints]
  ext x
  constructor
  · intro x_fixed
    rw [Set.mem_setOf, Function.IsFixedPt, step] at x_fixed
    simp
    by_cases heven : Even x
    · let ⟨r, hx⟩ := heven
      rw [if_pos heven, hx, <- mul_two, Nat.mul_div_cancel r (by linarith)] at x_fixed
      omega
    · rw [if_neg heven] at x_fixed
      omega
  · simp [Function.IsFixedPt]
    rintro rfl
    decide




variable {n m : Nat}

def GoesTo (n m : Nat) : Prop :=
  ∃i, step^[i] n = m

infixr:50 " |=> " => GoesTo

instance GoesTo.Trans : Trans GoesTo GoesTo GoesTo where
  trans {α β γ} := by
    rintro ⟨ia, rfl⟩ ⟨ib, rfl⟩
    exact ⟨ib + ia, Function.iterate_add_apply step ib ia α⟩

def GoesTo.trans : Transitive GoesTo := by intro α β γ αβ βγ; exact GoesTo.Trans.trans αβ βγ

@[refl]
theorem GoesTo.rfl : n |=> n := ⟨0, by simp⟩
theorem GoesTo.reflexive : Reflexive GoesTo := by intro x; rfl


def GoesTo.flow : Flow ℕ ℕ :=
  Flow.fromIter step.continuous

theorem GoesTo.even_path : (n * 2) |=> n := ⟨1, by simp [step]⟩


theorem GoesTo.odd_path : n ≡ 4 [MOD 6] -> (n - 1) / 3 |=> n := by
  intro hm
  have : ¬Even ((n-1)/3) := by
    apply Nat.not_even_iff_odd.mpr
    apply Nat.odd_iff.mpr
    rcases n
    case zero => norm_num; contradiction
    case succ k =>
    · have hm' : k ≡ 3 [MOD 6] := by
        apply (Nat.ModEq.add_right_cancel' 1)
        rw [Nat.add_one]
        simpa
      calc (Nat.succ k - 1) / 3 % 2
        _ = k / 3 % 2 := by omega
        _ = k % 6 / 3 := by omega
        _ = 3 % 6 / 3 := by rw [hm']
        _ = 1 := by norm_num
  have onelen : 1 ≤ n := by
    calc
      _ ≤ 4 := by decide
      _ = 4 % 6 := by decide
      _ = n % 6 := by rw [hm]
      _ ≤ n := Nat.mod_le n 6
  have three_dvd_n_sub_one : 3 ∣ n - 1 := by
    apply (Nat.modEq_iff_dvd' onelen).mp
    rw [Nat.ModEq.comm] at hm
    apply Nat.ModEq.of_dvd ((by decide): 3 ∣ 6) hm
  use 1
  rw [Function.iterate_one, step, if_neg this,
    Nat.mul_div_cancel' three_dvd_n_sub_one, Nat.sub_add_cancel onelen]

theorem GoesTo.even_family : ∀k, (n * 2^k) |=> n := by
  intro k
  induction' k with i hi
  · rw [pow_zero, mul_one]
  · calc n * 2 ^ Nat.succ i
      _ = n * 2 ^ i * 2 := by rw [Nat.pow_succ, <- mul_assoc]
      _ |=> n * 2 ^ i := even_path
      _ |=> n := hi

theorem GoesTo.odd_family : n ≡ 1 [MOD 6] -> ∀k, (n * 2^(2*k+2) - 1)/3 |=> n := by
  intro hn k
  have : n * 2 ^ (2 * k + 2) ≡ 4 [MOD 6] := by
    rw [<- one_mul 4]
    apply Nat.ModEq.mul hn
    induction k with
    | zero => simp; rfl
    | succ i hi =>
      calc 2 ^ (2 * Nat.succ i + 2) % 6
        _ = 2 ^ (2 * i + 2 + 2) % 6 := by rw [Nat.mul_succ]
        _ = (2 ^ (2 * i + 2) * 4) % 6 := by rw [Nat.pow_add]
        _ = 4 % 6 * (4 % 6) % 6 := by rw [Nat.mul_mod, hi]
  calc (n * 2^(2 * k + 2) - 1) / 3
    _ |=> n * 2^(2 * k + 2) := odd_path this
    _ |=> n := even_family _

theorem GoesTo.odd_family2 : n ≡ 5 [MOD 6] -> ∀k, (n * 2^(2*k+1) - 1)/3 |=> n := by
  intro hn k
  calc (n * 2 ^ (2 * k + 1) - 1) / 3
    _ |=> n * 2 ^ (2 * k + 1) := by
      apply odd_path
      rw [Nat.ModEq, ((by decide) : 4 ≡ 5 * 2 [MOD 6]), <- Nat.ModEq]
      apply Nat.ModEq.mul hn
      induction k with
      | zero => simp; rfl
      | succ i ih =>
        calc 2 ^ (2 * i + 2 + 1) % 6
          _ = 2 ^ (2 * i + 1) * 2 ^ 2 % 6 := by ring_nf
          _ = 2 ^ (2 * i + 1) % 6 * (2 ^ 2 % 6) % 6 := by rw [Nat.mul_mod]
          _ = 2 % 6 * (2 ^ 2 % 6) % 6 := by rw [ih]
          _ = 2 % 6 := by norm_num
    _ |=> n := even_family _
