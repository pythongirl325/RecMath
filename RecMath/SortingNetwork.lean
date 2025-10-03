import Mathlib
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Vector.Basic

universe u v
variable {α : Type u} [LinearOrder α] {β : Type v} [LinearOrder β] {n : Nat}

def Tuple (α n) := Fin n -> α

-- Not using these anymore, but i can change my definitoins to use them if wanted
-- def Sorted (t : Tuple α n) : Prop := Monotone t
-- def SortingFunction (f : Tuple α n -> Tuple α n) : Prop := ∀ (t : Tuple α n), Sorted (f t)

@[grind]
structure IndexPair (n : Nat) where
  i : Fin n
  j : Fin n
  h : i < j

def IndexPair.ofNats (i j : Nat) (h₁ : i < j) (h₂ : j < n) : IndexPair n :=
  ⟨Fin.mk i (h₁.trans h₂), Fin.mk j h₂, h₁⟩

-- These proofs of the cardinality of IndexPair n probably arent useful, but they were fun
instance : IsEmpty (IndexPair 0) where
  false a := IsEmpty.false a.i

instance : IsEmpty (IndexPair 1) where
  false a := by obtain ⟨_, _, h⟩ := a; omega

instance : Unique (IndexPair 2) where
  default := IndexPair.mk 0 1 (by decide)
  uniq := by grind only [cases IndexPair]

-- Not used yet
abbrev IndexPair.Independent (p₁ p₂ : IndexPair n) : Prop :=
  p₁.i ≠ p₂.i ∧ p₁.i ≠ p₂.j ∧ p₁.j ≠ p₂.i ∧ p₁.j ≠ p₂.j

def IndexPair.toPerm (t : Tuple α n) (p : IndexPair n) : Equiv.Perm (Fin n) :=
  if t p.i ≤ t p.j then
    1
  else
    Equiv.swap p.i p.j

def IndexPair.apply (p : IndexPair n) (t : Tuple α n) : Tuple α n :=
  t ∘ p.toPerm t

@[simp, grind =]
theorem IndexPair.apply_i_eq_min {p : IndexPair n} {t : Tuple α n} :
    p.apply t p.i = min (t p.i) (t p.j) := by
  rewrite [apply, toPerm]
  grind only [= Equiv.Perm.one_apply, = Equiv.swap_apply_left, = min_def]

@[simp, grind =]
theorem IndexPair.apply_j_eq_max {p : IndexPair n} {t : Tuple α n} :
    p.apply t p.j = max (t p.i) (t p.j) := by
  rewrite [apply, toPerm]
  grind only [= Equiv.Perm.one_apply, = Equiv.swap_apply_right, = max_def]

@[grind ←]
theorem IndexPair.apply_i_le_apply_j {p : IndexPair n} {t : Tuple α n} :
    p.apply t p.i ≤ p.apply t p.j := by
  simp! only [apply_i_eq_min, apply_j_eq_max, le_sup_iff, inf_le_left, inf_le_right, or_self]

theorem IndexPair.apply.monotoneOn_ij {p : IndexPair n} {t : Tuple α n} :
    MonotoneOn (p.apply t) {p.i, p.j} := by
  intro a ha b hb a_le_b
  by_cases a_eq_b : a = b
  { subst a_eq_b; rfl }
  -- grind only [= apply_i_eq_min, = Set.mem_singleton_iff, = apply_j_eq_max, = Set.subset_def,
  --   = Set.singleton_subset_iff, ← apply_i_le_apply_j, Set.subset_insert, = Set.mem_insert_iff,
  --   cases IndexPair, cases Or]
  have ⟨i_eq_a, j_eq_b⟩: p.i = a ∧ p.j = b := by
    grind only [= Set.mem_singleton_iff, = Set.mem_insert_iff, IndexPair]
  subst i_eq_a j_eq_b
  exact apply_i_le_apply_j

@[simp, grind =]
theorem IndexPair.apply_of_ne_of_ne {p : IndexPair n} {t : Tuple α n} {x : Fin n} :
    x ≠ p.i -> x ≠ p.j -> p.apply t x = t x := by
  intro x_ne_i x_ne_j
  dsimp [apply, toPerm]
  grind only [= Equiv.swap_apply_def, = Equiv.Perm.one_apply]

def ComparisonNetwork (n : Nat) := List (IndexPair n)

instance ComparisonNetwork.instHAppend :
    HAppend (ComparisonNetwork n) (ComparisonNetwork n) (ComparisonNetwork n) where
  hAppend := List.append

def ComparisonNetwork.nil {n} : ComparisonNetwork n := []

def ComparisonNetwork.toPerm (t : Tuple α n) (net : ComparisonNetwork n) : Equiv.Perm (Fin n) :=
  net.foldr (fun p e => (p.toPerm (t ∘ e)).trans e) 1

def ComparisonNetwork.apply (net : ComparisonNetwork n) (t : Tuple α n) : Tuple α n :=
  t ∘ net.toPerm t

-- This proof ensures that the ComparisonNetwork.toPerm implementation is correct
@[grind _=_]
theorem ComparisonNetwork.apply_eq_foldr_apply (net : ComparisonNetwork n) (t : Tuple α n) :
    net.apply t = net.foldr IndexPair.apply t := by
  rw [apply, toPerm]
  induction net with
  | nil => rw [List.foldr_nil, Equiv.Perm.coe_one, Function.comp_id, List.foldr_nil]
  | cons p net h =>
    rw [List.foldr_cons, List.foldr_cons, <- h, IndexPair.apply]
    rw [Equiv.coe_trans, Function.comp_assoc]

@[simp, grind =]
theorem ComparisonNetwork.apply_nil {t : Tuple α n} : apply [] t = t := by
  rw [apply_eq_foldr_apply, List.foldr_nil]

@[simp, grind =]
theorem ComparisonNetwork.apply_cons {p : IndexPair n} {net : ComparisonNetwork n} {t : Tuple α n} :
    apply (p :: net) t = p.apply (net.apply t) := by
  simp! only [apply_eq_foldr_apply, List.foldr_cons]

@[simp, grind =]
theorem ComparisonNetwork.apply_append {net₁ net₂ : ComparisonNetwork n} {t : Tuple α n} :
    (net₁ ++ net₂).apply t = net₁.apply (net₂.apply t) := by
  grind only [= apply_eq_foldr_apply, =_ List.foldr_append]

abbrev ComparisonNetwork.Sorts (net : ComparisonNetwork n) : Prop :=
  ∀ {α : Type u} [LinearOrder α] (t : Tuple α n), Monotone (net.apply t)

abbrev ComparisonNetwork.SortsOn (net : ComparisonNetwork n) (s : Set (Fin n)) : Prop :=
  ∀ {α : Type u} [LinearOrder α] (t : Tuple α n), MonotoneOn (net.apply t) s




-- This is probably a bad name for this. It's not the only network, just the only useful one
def ComparisonNetwork.trivial_network : ComparisonNetwork 2 := [IndexPair.mk 0 1 (by decide)]

theorem ComparisonNetwork.trivial_network_sorts : trivial_network.Sorts := by
  intro α _ t
  have fin_2_set_univ : Set.univ (α := Fin 2) = {0, 1} := by
    grind only [= Set.mem_singleton_iff, Set.mem_univ, = Set.mem_insert_iff]
  rw [<- monotoneOn_univ, fin_2_set_univ]
  rw [trivial_network, apply_eq_foldr_apply, List.foldr_cons, List.foldr_nil]
  exact IndexPair.apply.monotoneOn_ij

-- #eval ComparisonNetwork.trivial_network.apply ![1, 3]
-- #eval ComparisonNetwork.trivial_network.apply ![3, 1]

def net3 : ComparisonNetwork 3 :=
  [IndexPair.mk 0 1 (by decide), IndexPair.mk 1 2 (by decide), IndexPair.mk 0 1 (by decide)]

-- #eval net3.apply ![8, 9, 2]





------------------
-- Todo Section --
------------------




def IndexPair.upgrade (skip : Fin (n + 1)) (p : IndexPair n) : IndexPair (n + 1) :=
  ⟨skip.succAbove p.i, skip.succAbove p.j, by gcongr; exact p.h⟩

def ComparisonNetwork.upgrade (net : ComparisonNetwork n) (skip : Fin (n + 1)) :
    ComparisonNetwork (n + 1) :=
  net.map (IndexPair.upgrade skip)

def ComparisonNetwork.upgrade.sortsOn_old {net : ComparisonNetwork n} {skip : Fin (n + 1)} :
    ComparisonNetwork.Sorts.{u} net -> ComparisonNetwork.SortsOn.{u} (net.upgrade skip) {x | x ≠ skip} := by
  intro h α inst t
  specialize @h α inst
  conv at h => intro t; rw [<- monotoneOn_univ]
  let := Fin.succAboveEmb skip



  intro a ha b hb a_le_b
  rw [Set.mem_setOf_eq] at ha hb
  -- rw [upgrade, List.map_eq_foldr]
  by_cases a_eq_b : a = b
  · subst_vars; rfl
  have a_lt_b : a < b := by order

  sorry

-- instance {n m : Nat} : CoeDep Nat n (Fin (n + Nat.succ m)) where
--   coe := Fin.mk n (by omega)

-- instance ComparisonNetwork.instInhabited : Inhabited (ComparisonNetwork n) where
--   default := []

-- instance [IsEmpty (IndexPair n)] : Unique (ComparisonNetwork n) where
--   default := []
--   uniq := by
--     intro a
--     cases a with
--     | nil => rfl
--     | cons p _ => exfalso; exact IsEmpty.false p


def ComparisonNetwork.sequential_layer {n} : ComparisonNetwork n :=
  match n with
  | 0 | 1 => nil
  | m + 2 =>
    IndexPair.ofNats 0 1 (by decide) (by omega)
    :: (sequential_layer.upgrade 0)

def ComparisonNetwork.bubble_sort_layer (net : ComparisonNetwork n) : ComparisonNetwork (n + 1) :=
  sequential_layer (n := n + 1) ++ net.upgrade (Fin.mk n (by omega))

def ComparisonNetwork.bubble_sort {n : Nat} : ComparisonNetwork n :=
  match n with
  | 0 => nil
  | _ + 1 => bubble_sort.bubble_sort_layer

-- My sorry attempts at trying to prove the bubble sort correct (i think i need better theorems like zero-one principle)
theorem ComparisonNetwork.bubble_sort_layer.sorts {n} {net : ComparisonNetwork n} :
    ComparisonNetwork.Sorts.{u} net -> ComparisonNetwork.Sorts.{u} net.bubble_sort_layer := by
  intro hnet α inst t
  specialize @hnet α inst
  rw [bubble_sort_layer, apply_append]
  rw [sequential_layer.eq_def]
  sorry

theorem ComparisonNetwork.bubble_sort_sorts {n} : (bubble_sort (n := n)).Sorts := by
  intro α _ t
  induction n with
  | zero =>
    simp [bubble_sort]
    rw [nil, apply_eq_foldr_apply, List.foldr_nil]
    apply Subsingleton.monotone t
  | succ m hi =>
    rw [bubble_sort, bubble_sort_layer, apply_eq_foldr_apply, List.foldr_append]
    sorry

#eval ComparisonNetwork.bubble_sort.apply (![4, 3, 2, 1] : Tuple Int _)
#eval ComparisonNetwork.bubble_sort.apply ![7, 8, 6, 1, 5, 2, 4, 3]

-- These are useful to have in the grind set
attribute [grind] Equiv.injective Equiv.surjective Equiv.bijective
attribute [grind =] Equiv.Perm.one_apply Equiv.swap_apply_left Equiv.swap_apply_right
attribute [grind ←] Equiv.swap_apply_of_ne_of_ne
-- attribute [grind →] ne_of_lt
attribute [grind] Monotone.map_max Monotone.map_min

section ZeroOnePrinciple

-- These two lemmas are from the wikipedia proof. I can probably get rid of them
@[grind]
theorem IndexPair.apply_i_eq_min_mono {p : IndexPair n} {t : Tuple α n} {f : α -> β}
    (hf : Monotone f) : f (p.apply t p.i) = min (f (t p.i)) (f (t p.j)) := by
  rw [apply_i_eq_min, Monotone.map_min hf]

@[grind]
theorem IndexPair.apply_j_eq_max_mono {p : IndexPair n} {t : Tuple α n} {f : α -> β}
    (hf : Monotone f) : f (p.apply t p.j) = max (f (t p.i)) (f (t p.j)) := by
  rw [apply_j_eq_max, Monotone.map_max hf]

@[simp, grind _=_]
theorem IndexPair.monotone_comp {p : IndexPair n} {a : Tuple α n} {f : α -> β} (hf : Monotone f) :
    p.apply (f ∘ a) = f ∘ (p.apply a) := by
  funext k
  by_cases k = p.i ∨ k = p.j <;>
  grind only [Monotone.map_min, Monotone.map_max, = apply_i_eq_min, = apply_j_eq_max,
    cases Or, = apply_of_ne_of_ne]

-- Lemme 28.1 in Introduction to algorithms 1e
-- Should probably rename this theorem too
@[grind _=_]
theorem ComparisonNetwork.monotone_comp {net : ComparisonNetwork n} {a : Tuple α n} {f : α -> β}
    (hf : Monotone f) : net.apply (f ∘ a) = f ∘ (net.apply a) := by
  induction net <;> grind only [= apply_nil, = apply_cons, = IndexPair.monotone_comp]

@[simp, grind =]
theorem IndexPair.apply_monotone {p : IndexPair n} {t : Tuple α n} (h : Monotone t) :
    p.apply t = t := by
  funext k
  rw [apply, toPerm]
  grind only [= Monotone, cases IndexPair, = Equiv.Perm.one_apply]

@[simp, grind =]
theorem ComparisonNetwork.apply_monotone {net : ComparisonNetwork n} {t : Tuple α n}
    (h : Monotone t) : net.apply t = t := by
  induction net <;> grind only [= apply_nil, = apply_cons, = IndexPair.apply_monotone]

-- This might be useful to have around
theorem Equiv.Perm.strictmono_of_monotone {α} [PartialOrder α] {p : Equiv.Perm α} :
    Monotone p -> StrictMono p := by
  intro h i j i_lt_j
  specialize @h i j (by order)
  have : p i ≠ p j := Function.Injective.ne (Equiv.injective _) (by order)
  order

def extend_fin.equiv {n : Nat} : Fin n ≃ {x : Fin (n + 1) // x < n } where
  toFun x := Subtype.mk (Fin.mk x.val (by omega)) (by bound)
  invFun x := Fin.mk x.val.val x.prop
  left_inv _ := rfl
  right_inv _ := rfl

theorem monotone_perm_eq_one {n : Nat} {p : Equiv.Perm (Fin n)} (h : Monotone p) : p = 1 := by
  unfold Monotone at h
  -- Induct and try to transfer proofs using MonotoneOn then expand the set
  induction n with
  | zero => exact Subsingleton.allEq p 1
  | succ n h =>
    change p = Equiv.refl _
    rw [<- Equiv.Perm.extendDomain_refl extend_fin.equiv]
    sorry

-- The basic idea that if a comparison network can sort all permuataions, then it can sort anything
-- I see it as a weaker form of the zero-one principle
theorem ComparisonNetwork.permutation_test (net : ComparisonNetwork n) :
    (∀ (p : Equiv.Perm (Fin n)), Monotone (net.apply ⇑p)) -> net.Sorts := by
  intro h α inst a i j i_le_j

  -- i dont know if this approach will actually work
  have my_perm : ∃ (p : Equiv.Perm (Fin n)), net.toPerm ⇑p = net.toPerm a := by
    sorry
  rcases my_perm with ⟨p, hp⟩
  have {i j : Fin n} : p i ≤ p j -> a i ≤ a j := by
    sorry
  specialize h p i_le_j
  simp [apply, hp] at h
  simp [apply, ]
  exact this h


-- I dont know if this would actually be useful, but it's mentioned in the wikipedia article
-- https://en.wikipedia.org/wiki/Sorting_network#Zero-one_principle
--
-- Introduction to Algorithms by Cormen at al pg 641
theorem ComparisonNetwork.zero_one_principle (net : ComparisonNetwork n) :
    (∀ (t : Tuple Bool n), Monotone (net.apply t)) -> ComparisonNetwork.Sorts net := by
  intro h
  contrapose! h
  -- by_contra! h
  dsimp only [Sorts, Monotone] at h
  push_neg at h
  rcases h with ⟨α, inst, a, i, j, i_le_j, bad_swap⟩

  have i_lt_j : i < j := by grind only [-> ne_of_lt]

  let f : α -> Bool := (a i < ·)
  have fmono : Monotone f := by
    grind only [= Monotone, = Bool.le_iff_imp, = decide_eq_true, -> lt_of_lt_of_le]
  have fswap := monotone_iff_forall_lt.mp fmono bad_swap
  have : f ∘ net.apply a = net.apply (f ∘ a) := by
    simp [monotone_comp fmono]

  use f ∘ a
  dsimp [Monotone]
  push_neg
  use i, j
  constructor
  · order
  simp [<- this]

  have : f (net.apply a j) ≠ f (net.apply a i) := by
    unfold f
    simp
    push_neg
    simp [f, Bool.le_iff_imp] at fswap

  order

  -- have : f (a j) = true := by
  --   unfold f
  --   simp; exact ai_lt_aj
  -- have : f (a i) = false := by simp [f]

  -- have : net.apply (f ∘ a) i <= net.apply (f ∘ a) j := by
  --   specialize bh (f ∘ a) i_le_j
  --   simp [monotone_comp fmono, Function.comp_apply] at bh
  --   simp only [monotone_comp fmono, Function.comp_apply]
  --   exact bh

  -- sorry

  sorry

-- Using the zero-one principle i could implement Decidable ComparisonNetwork.Sorts
-- in O(2ⁿ) instead of O(n!).
-- Would need to use Finset.univ (Fin n -> Bool) to do it i think
end ZeroOnePrinciple


theorem IndexPair.independence {p₁ p₂ : IndexPair n} {hi : Independent p₁ p₂} {t : Tuple α n} :
    p₁.apply (p₂.apply t)  = p₂.apply (p₁.apply t) := by
  simp [Function.comp, apply, toPerm]
  -- a disgusting amount of case splitting may lead to a solution here
  sorry


-- TODO: Maybe there's some way i can do this better with List.Perm and a subtype or a List.Perm in
-- a struct
inductive ComparisonNetwork.ParallelEquiv {n : Nat} :
  ComparisonNetwork n -> ComparisonNetwork n -> Prop
| nil : ParallelEquiv nil nil
| cons (p : IndexPair n) {net₁ net₂} :
  ParallelEquiv net₁ net₂ -> ParallelEquiv (p :: net₁) (p :: net₂)
| swap (p₁ p₂ : IndexPair n) (h : p₁.Independent p₂) {net : ComparisonNetwork n} :
  ParallelEquiv (p₁ :: p₂ :: net) (p₂ :: p₁ :: net)
| trans {net₁ net₂ net₃ : ComparisonNetwork n} :
  ParallelEquiv net₁ net₂ -> ParallelEquiv net₂ net₃ -> ParallelEquiv net₁ net₃



example (net₁ net₂ : ComparisonNetwork n) : net₁.Sorts ∧ net₂.Sorts -> net₁.apply = (net₂.apply (α := α)) := by
  rintro ⟨hsnet₁, hsnet₂⟩
  ext

  sorry



-- # Wishlist
--
-- [x] Sorting networks can be lists of index pair
-- [x] Need some sort of proposition that says a network sorts
--
-- Proofs:
-- [ ] Zero-one principle
-- [ ] Asymptotic reasoning about size and depth for certain algorithms
--
-- Depth:
-- [x] Independent index-pair predicate (DecidableRel)
-- [ ] An equivalence relation based on independent permutations
-- [ ] Forms a setoid with an equivalence for reordering independent pairs
-- [ ] A (preferrably computable) method for measuring depth of a network through these permutations
-- [ ] Equivalence relation between sorting networks implies net₁.apply = net₂.apply (prove with
--     funext and cases on the equiv)
--
-- Sorting algorithms:
-- [-] Bubble sort (implemented but unproven)
-- [ ] Insertion sort
-- [ ] Shell sort
-- [ ] Batcher's odd-even merge sort
-- [ ] AKS Sort or more recent innovations with the same asymptotic bounds
--
-- Other:
-- [ ] Array oriented API using Vector.swap
-- [ ] Bitvec oriented API for specializing Vector Bool n to BitVec n (could possibly used with
--     bv_decide)
