import Mathlib.Tactic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Defs.Basic

-- import Mathlib.LinearAlgeba.AffineSpace.AffineMap



@[grind =]
def step (n : Nat) : Nat :=
  if Even n then
    n / 2
  else
    3 * n + 1

theorem step.odd_even {n} (h : Odd n) : Even (step n) := by
  simp only [step, Nat.not_even_iff_odd.mpr h]
  apply Odd.add_odd (Nat.odd_mul.mpr ⟨by decide, h⟩) (by decide)

theorem step.not_injective : ¬ step.Injective := by
  rw [Function.Injective]
  push_neg
  use 1, 8; decide

theorem step.surjective : step.Surjective := by
  intro n
  use 2 * n
  simp! [step]

def step.continuous : Continuous step where
  isOpen_preimage _ a := a -- by exact fun s a ↦ a

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
    apply Set.mem_singleton_of_eq
    by_cases heven : Even x
    · let ⟨r, hx⟩ := heven
      rw [if_pos heven, hx, <- mul_two, Nat.mul_div_cancel r (by decide)] at x_fixed
      omega
    · rw [if_neg heven] at x_fixed
      omega
  · simp [Function.IsFixedPt]
    rintro rfl
    decide

section stepT

@[grind]
def stepT (n : Nat) : Nat :=
  if Even n then
    n / 2
  else
    (3 * n + 1) / 2

theorem stepT.even {n} (h : Even n) : stepT n = n / 2 := by
  simp! only [stepT, h, ↓reduceIte]

theorem stepT.odd {n} (h : Odd n) : stepT n = (3 * n + 1) / 2 := by
  simp! only [stepT, h, Nat.not_even_iff_odd.mpr h, ↓reduceIte]

@[grind =]
theorem stepT.even_step {n} (h : Even n) : stepT n = step n := by
  simp! only [stepT, step, h, ↓reduceIte]

@[grind =]
theorem stepT.odd_step {n} (h : Odd n) : stepT n = step (step n) := by
  grind only [= Nat.even_iff, = Nat.odd_iff, stepT, step]


theorem stepT.pattern1 {k m} : (1 <= k) -> (k <= m) -> stepT^[k] (2^m - 1) = 3^k * 2^(m-k) - 1 := by
  intro one_le_k k_le_m
  have one_le_m : 1 ≤ m := le_trans one_le_k k_le_m
  induction' k with k hk
  · rw [Function.iterate_zero_apply]; omega
  have : Odd (2^m - 1) := by
    induction' m with m hm
    contradiction
    rw [Nat.pow_add_one]
    sorry
  rw [Nat.add_one, Function.iterate_succ_apply stepT, stepT.odd this]
  sorry


end stepT



abbrev IteratesTo {α : Type*} (F : α -> α) (a b : α) :=
  { i : Nat // F^[i] a = b }

/-- `X ~>[F] Y` is a natural number i such that F^[i] X = Y. -/
notation:25 X " ~>[" F:25 "] " Y:0 => IteratesTo F X Y

@[simp, grind =] def IteratesTo.id {α} {F : α -> α} (x : α) : x ~>[F] x :=
  ⟨0, Function.iterate_zero_apply F x⟩

@[grind]
theorem IteratesTo.zero_eq {α} {X Y : α} {F} {i : X ~>[F] Y} : i.val = 0 -> X = Y := by
  grind only [= Function.iterate_zero_apply]

@[simp, grind =]
def IteratesTo.comp {α} {F : α -> α} {X Y Z : α} (f : X ~>[F] Y) (g : Y ~>[F] Z) : X ~>[F] Z :=
  ⟨g.val + f.val, by grind only [=_ Function.iterate_add_apply]⟩

@[simp, grind =]
def IteratesTo.iterate_n {α} {x : α} {F} (n : Nat) : x ~>[F] (F^[n] x) := ⟨n, rfl⟩

-- @[grind]
def IteratesToCat {α} (_ : α -> α) := α

instance IteratesTo.category {α} (F : α -> α) : CategoryTheory.Category (IteratesToCat F) where
  Hom := IteratesTo F
  id := IteratesTo.id
  comp := IteratesTo.comp
  id_comp := by grind only [= id, = comp]
  comp_id := by grind only [= id, = comp]
  assoc := by grind only [= comp]

abbrev step.iteratesTo := IteratesTo step
abbrev stepT.iteratesTo := IteratesTo stepT


section GoesTo

variable {n m : Nat}

def step.iteratesTo.even_path {n} : n * 2 ~>[step] n := ⟨1, by simp! [step]⟩





def GoesTo (n m : Nat) : Prop := ∃i, step^[i] n = m

theorem GoesTo.iff_nonempty_iteratesTo {n m : Nat} :
    GoesTo n m <-> Nonempty (step.iteratesTo n m) := by
  exact nonempty_subtype.symm

infixr:50 " |=> " => GoesTo
infixr:50 " ⤇ " => GoesTo

instance GoesTo.Trans : Trans GoesTo GoesTo GoesTo where
  trans {α β γ} := by
    rintro ⟨ia, rfl⟩ ⟨ib, rfl⟩
    exact ⟨ib + ia, Function.iterate_add_apply step ib ia α⟩

def GoesTo.transitive : Transitive GoesTo := by intro α β γ αβ βγ; exact GoesTo.Trans.trans αβ βγ

@[refl] theorem GoesTo.rfl : n ⤇ n := ⟨0, by simp⟩
theorem GoesTo.reflexive : Reflexive GoesTo := by intro x; rfl

def GoesTo.flow : Flow ℕ ℕ := Flow.fromIter step.continuous

theorem GoesTo.even_path : n * 2 ⤇ n := ⟨1, by simp [step]⟩

theorem GoesTo.odd_path : n ≡ 4 [MOD 6] -> (n - 1) / 3 ⤇ n := by
  intro hm
  have : ¬Even ((n-1)/3) := by
    apply Nat.not_even_iff_odd.mpr
    apply Nat.odd_iff.mpr
    rcases n
    case zero => norm_num; contradiction
    case succ k =>
    · have hm' : k ≡ 3 [MOD 6] := (Nat.ModEq.add_right_cancel' 1 hm)
      calc (Nat.succ k - 1) / 3 % 2
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

theorem GoesTo.even_family : ∀k, (n * 2^k) ⤇ n := by
  intro k
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ i hi =>
    calc n * 2 ^ Nat.succ i
      _ = n * 2 ^ i * 2 := by rw [Nat.pow_succ, <- mul_assoc]
      _ ⤇ n * 2 ^ i := even_path
      _ ⤇ n := hi

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
    _ ⤇ n * 2^(2 * k + 2) := odd_path this
    _ ⤇ n := even_family _

theorem GoesTo.odd_family2 : n ≡ 5 [MOD 6] -> ∀k, (n * 2^(2*k+1) - 1)/3 |=> n := by
  intro hn k
  calc (n * 2 ^ (2 * k + 1) - 1) / 3
    _ ⤇ n * 2 ^ (2 * k + 1) := by
      apply odd_path
      rw [Nat.ModEq, ((by decide) : 4 ≡ 5 * 2 [MOD 6]), <- Nat.ModEq]
      apply Nat.ModEq.mul hn
      induction k with
      | zero => rfl
      | succ i ih =>
        calc 2 ^ (2 * i + 2 + 1) % 6
          _ = 2 ^ (2 * i + 1) * 2 ^ 2 % 6 := by ring_nf
          _ = 2 ^ (2 * i + 1) % 6 * (2 ^ 2 % 6) % 6 := by rw [Nat.mul_mod]
          _ = 2 % 6 * (2 ^ 2 % 6) % 6 := by rw [ih]
          _ = 2 % 6 := by norm_num
    _ ⤇ n := even_family _

-- theorem CollatzConjecture : n |=> 1 := by sorry

end GoesTo

section Cats

def stepT.iteratesTo.to_step {x y : Nat} (i : x ~>[stepT] y) : x ~>[step] y :=
  match i with
  | ⟨0, hi⟩ => ⟨0, hi⟩
  | ⟨n + 1, hi⟩ =>
    if heven : Even x then
      IteratesTo.comp (IteratesTo.iterate_n 1) (to_step ⟨n, by
        change stepT^[n] (step x) = y
        grind only [= even_step, = Function.iterate_succ_apply]⟩)
    else
      have hodd := Nat.not_even_iff_odd.mp heven
      IteratesTo.comp (IteratesTo.iterate_n 2) (to_step ⟨n, by
        change stepT^[n] (step (step x)) = y
        grind only [= odd_step, = Function.iterate_succ_apply]⟩)

@[simp, grind =]
theorem stepT.iteratesTo.to_step_zero {x y : Nat} {h : stepT^[0] x = y} : (to_step ⟨0, h⟩).val = 0 := by
  simp! only [to_step]

theorem stepT.iteratesTo.to_step_ge {x y : Nat} {i : x ~>[stepT] y} : i.val ≤ (to_step i).val := by
  unfold to_step
  rcases i with ⟨ni, hi⟩
  induction ni generalizing x with
  | zero => rfl
  | succ ni hn =>
    simp_all
    rw [Function.iterate_succ_apply] at hi
    split
    · rename_i heven
      rw [stepT.even_step heven] at hi
      specialize hn hi
      sorry
    · have hodd : Odd x := by grind
      rw [stepT.odd_step hodd] at hi
      specialize hn hi
      sorry

#eval stepT.iteratesTo.to_step (⟨13, by decide⟩ : 9 ~>[stepT] 1)

attribute [grind =] Function.iterate_zero Function.iterate_succ

-- set_option maxHeartbeats 800000

-- @[simp]
-- theorem IteratesTo.coe_cast {α} {F} {X Y : α} {n : Nat} {h₁} :
--     ↑(⟨n, h₁⟩ : X ~>[F] Y) = n := by grind only

-- theorem IteratesTo.mk_coe : ⟨

def stepT.iteratesTo.to_step.da_funky_functor : CategoryTheory.Functor (IteratesToCat stepT) (IteratesToCat step) where
  obj := id
  map {X Y : Nat} (f : X ~>[stepT] Y) : X ~>[step] Y := stepT.iteratesTo.to_step f
  map_comp {X Y Z} (f : X ~>[stepT] Y) (g : Y ~>[stepT] Z) := by
    rcases f with ⟨nf, hf⟩
    rcases g with ⟨ng, hg⟩
    simp [CategoryTheory.CategoryStruct.comp]
    induction nf with
    | zero => bound
    | succ nf hnf =>
      induction ng with
      | zero => bound
      | succ ng hng =>
        ring_nf

        sorry

    -- split
    -- · grind only
    -- · split
    --   · split
    --     · split
    --       · grind only
    --       ·
    --         rename_i hi h i_1 hi_1 i_2 n_1 hi_2 heq
    --         subst hi hi_2
    --         simp at heq
    --         subst heq
    --         grind [= Function.iterate_zero, IteratesTo.comp, IteratesTo.id, = Nat.even_iff,
    --           cases eager Subtype, cases Or]
    --     · split
    --       · split
    --         ·
    --           rename_i hi_1 h_1 i_2 hi_2 heq
    --           subst hi_2 hi_1
    --           grind only [= Function.iterate_zero, IteratesTo.comp, IteratesTo.id, = Nat.even_iff,
    --             cases eager Subtype, cases Or]
    --         · simp


    --           -- hint timeout

    --           sorry
    --       · split
    --         ·
    --           sorry
    --           -- simp
    --         · -- hint gave no good results

    --           sorry
    --   · split
    --     · split
    --       · grind only
    --       ·
    --         rename_i hi h i_1 hi_1 i_2 n_1 hi_2 heq
    --         subst hi hi_2
    --         simp_all
    --         subst heq
    --         simp_all only [cast_eq, zero_add]
    --     · split
    --       · split
    --         ·
    --           sorry
    --         ·
    --           sorry
    --       · split
    --         · rename_i hi_1 h_1 i_2 hi_2 heq
    --           subst hi_1 hi_2
    --           grind [= Function.iterate_zero, = Function.iterate_succ]
    --         ·
    --           sorry
  map_id x := by
    simp! only [id_eq, CategoryTheory.CategoryStruct.id, IteratesTo.id, stepT.iteratesTo.to_step,
      cast_eq]






end Cats
