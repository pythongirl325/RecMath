import Mathlib
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Vector.Basic

universe u
variable {α : Type u} [LinearOrder α] {n : Nat}

def Tuple (α n) := Fin n -> α



-- Not using these anymore, but i can change my definitoins to use them if wanted
-- def Sorted (t : Tuple α n) : Prop := Monotone t
-- def SortingFunction (f : Tuple α n -> Tuple α n) : Prop := ∀ (t : Tuple α n), Sorted (f t)

structure IndexPair (n : Nat) where
  i : Fin n
  j : Fin n
  h : i < j

-- These proofs of the cardinality of IndexPair n probably arent useful, but they were fun
instance : IsEmpty (IndexPair 0) where
  false a := IsEmpty.false a.i

instance : IsEmpty (IndexPair 1) where
  false a := by obtain ⟨_, _, h⟩ := a; omega

instance : Unique (IndexPair 2) where
  default := IndexPair.mk 0 1 (by decide)
  uniq := by grind only [cases IndexPair]


def IndexPair.permute (p : IndexPair n) (t : Tuple α n) (k : Fin n) : Fin n :=
  let (a, b) := (t p.i, t p.j)
  if k = p.i then
    if a ≤ b then p.i else p.j
  else if k = p.j then
    if a ≤ b then p.j else p.i
  else
    k

theorem IndexPair.permute.involutive {p : IndexPair n} {t : Tuple α n}
    : Function.Involutive (p.permute t) := by
  grind only [Function.Involutive, permute]

-- def IndexPair.toPerm (t : Tuple α n) (p : IndexPair n) : Equiv.Perm (Fin n) where
--   toFun := p.permute t
--   invFun := p.permute t
--   left_inv k := by
--     change (p.permute t ∘ p.permute t) k = k
--     rw [Function.Involutive.comp_self IndexPair.permute.involutive, id]
--   right_inv k := by
--     change (p.permute t ∘ p.permute t) k = k
--     rw [Function.Involutive.comp_self IndexPair.permute.involutive, id]

def IndexPair.toPerm (t : Tuple α n) (p : IndexPair n) : Equiv.Perm (Fin n) :=
  if t p.i ≤ t p.j then
    1
  else
    Equiv.swap p.i p.j

def IndexPair.apply (p : IndexPair n) (t : Tuple α n) : Tuple α n := t ∘ p.toPerm t

-- I dont know what to call this lemma, it needs a better name
theorem IndexPair.apply.asdf (p : IndexPair n) (t : Tuple α n)
    : p.apply t p.i ≤ p.apply t p.j := by
  obtain ⟨i, j, hp⟩ := p
  simp [apply, Function.comp, toPerm]
  split
  · simpa! only [Equiv.refl_apply]
  · rename_i h
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact le_of_not_ge h

theorem IndexPair.apply.monotoneOn_ij (p : IndexPair n) (t : Tuple α n) :
    MonotoneOn (p.apply t) {p.i, p.j} := by
  intro a ha b hb a_le_b
  by_cases a_eq_b : a = b
  { subst a_eq_b; rfl }
  have ⟨i_eq_a, j_eq_b⟩: p.i = a ∧ p.j = b := by
    grind only [= Set.mem_singleton_iff, = Set.mem_insert_iff, IndexPair]
  subst i_eq_a j_eq_b
  exact asdf p t

def ComparisonNetwork (n : Nat) := List (IndexPair n)

-- -- This definition is not needed yet
-- def ComparisonNetwork.nil : ComparisonNetwork n := []

def ComparisonNetwork.toPerm (t : Tuple α n) (net : ComparisonNetwork n) : Equiv.Perm (Fin n) :=
  net.foldr (fun p e => (p.toPerm (t ∘ e)).trans e) 1

def ComparisonNetwork.apply (net : ComparisonNetwork n) (t : Tuple α n) : Tuple α n :=
  t ∘ net.toPerm t

-- This proof ensures that the ComparisonNetwork.toPerm implementation is correct
theorem ComparisonNetwork.apply_eq_foldr_apply (net : ComparisonNetwork n) (t : Tuple α n) :
    net.apply t = net.foldr IndexPair.apply t := by
  rw [apply, toPerm]
  induction net with
  | nil => rw [List.foldr, Equiv.Perm.coe_one, CompTriple.comp_eq, List.foldr]
  | cons p net h =>
    rw [List.foldr_cons, List.foldr_cons, <- h, IndexPair.apply]
    rw [Equiv.coe_trans, Function.comp_assoc]


def ComparisonNetwork.Sorts (net : ComparisonNetwork n) : Prop :=
  {α : Type u} -> [LinearOrder α] -> (t : Tuple α n) -> Monotone (net.apply t)


-- This is probably a bad name for this. It's not the only network, just the only useful one
def ComparisonNetwork.trivial_network : ComparisonNetwork 2 := [IndexPair.mk 0 1 (by decide)]

theorem ComparisonNetwork.trivial_network_sorts : trivial_network.Sorts := by
  intro α _ t a b a_le_b
  simp [trivial_network, apply, toPerm, IndexPair.toPerm]
  by_cases a_eq_b : a = b
  · subst_vars; rfl
  split
  · simp
    grind only
  · have ⟨a0, b1⟩ : a = 0 ∧ b = 1 := by omega
    subst a0 b1
    simp
    order

#eval ComparisonNetwork.trivial_network.apply ![3, 2]
#eval ComparisonNetwork.trivial_network.apply ![1, 2]

def net3 : ComparisonNetwork 3 :=
  [IndexPair.mk 0 1 (by decide), IndexPair.mk 1 2 (by decide), IndexPair.mk 0 1 (by decide)]

#eval net3.apply ![8, 9, 2]


-- [x] Sorting networks can be lists of index pair
-- [x] Need some sort of proposition that says a network sorts
-- [ ] Forms a setoid with an equivalence for reordering independent pairs

-- [x] i can write a function with a given tuple forms a permutation (ComparisonNetwork.toPerm)
-- [x] which can be applied to the tuple `ComparisonNetwork.apply`

-- [ ] Array oriented API using Vector.swap
