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

-- instance Tuple.instGetElem {α n} : GetElem (Tuple α n) Nat α (fun _ i ↦ i < n) where
--  getElem t i h := t (Fin.mk i h)

-- #synth GetElem (Tuple Int 2) Nat Int _
-- #eval ((GetElem.getElem (![1, 2] : Tuple Int 2) 0 (by sorry)) : Nat)

-- def Tuple.toVector (t : Tuple α n) : Vector α n := (Vector.range n).map (fun i ↦ t (Fin.mk i (by sorry)))

-- def Tuple.nil : Tuple α 0 := by nofun

-- instance Tuple.instInhabitedTuple0 : Inhabited (Tuple α 0) where
--   default := Tuple.nil

def Sorted (t : Tuple α n) : Prop := Monotone t

def SortingFunction (f : Tuple α n -> Tuple α n) : Prop := ∀ (t : Tuple α n), Sorted (f t)



-- def IndexPair (n : Nat) := {p : Fin n × Fin n // p.fst < p.snd}
structure IndexPair (n : Nat) where
  i : Fin n
  j : Fin n
  h : i < j

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

def IndexPair.apply (p : IndexPair n) (t : Tuple α n) : Tuple α n := t ∘ p.permute t

-- I dont know what to call this lemma, it needs a better name
theorem IndexPair.apply.asdf (p : IndexPair n) (t : Tuple α n)
    : p.apply t p.i ≤ p.apply t p.j := by
  obtain ⟨i, j, hp⟩ := p
  simp only [apply, Function.comp, permute, ↓reduceIte]
  grind only [le_of_not_ge]

theorem IndexPair.apply.monotoneOn_ij (p : IndexPair n) (t : Tuple α n) :
    MonotoneOn (p.apply t) {p.i, p.j} := by
  intro a ha b hb a_le_b
  by_cases a_eq_b : a = b
  { subst a_eq_b; rfl }
  have ⟨i_eq_a, j_eq_b⟩: p.i = a ∧ p.j = b := by
    grind only [= Set.mem_singleton_iff, = Set.mem_insert_iff, IndexPair]
  subst i_eq_a j_eq_b
  exact asdf p t

theorem IndexPair.permute.involutive {p : IndexPair n} {t : Tuple α n}
    : Function.Involutive (p.permute t) := by
  grind only [Function.Involutive, permute]

def IndexPair.toPerm (t : Tuple α n) (p : IndexPair n) : Equiv.Perm (Fin n) where
  toFun := p.permute t
  invFun := p.permute t
  left_inv k := by
    change (p.permute t ∘ p.permute t) k = k
    rw [Function.Involutive.comp_self IndexPair.permute.involutive, id]
  right_inv k := by
    change (p.permute t ∘ p.permute t) k = k
    rw [Function.Involutive.comp_self IndexPair.permute.involutive, id]

def ComparisonNetwork (n : Nat) := List (IndexPair n)

def ComparisonNetwork.nil : ComparisonNetwork n := []

def ComparisonNetwork.toPerm (t : Tuple α n) (net : ComparisonNetwork n) : Equiv.Perm (Fin n) :=
  net.map (IndexPair.toPerm t) |> List.foldl Equiv.trans (Equiv.refl _)

def ComparisonNetwork.apply (net : ComparisonNetwork n) (t : Tuple α n) : Tuple α n :=
  t ∘ net.toPerm t

def ComparisonNetwork.Sorts (net : ComparisonNetwork n) : Prop :=
  {α : Type u} -> [LinearOrder α] -> (t : Tuple α n) -> Monotone (net.apply t)


-- This is probably a bad name for this. It's not the only network, just the only useful one
def ComparisonNetwork.trivial_network : ComparisonNetwork 2 := [IndexPair.mk 0 1 (by decide)]

theorem ComparisonNetwork.trivial_network_sorts : trivial_network.Sorts := by
  intro α _ t a b a_le_b
  simp [trivial_network, apply, toPerm, IndexPair.toPerm, IndexPair.permute]
  grind only [le_refl, le_of_not_ge]

#eval ComparisonNetwork.trivial_network.apply ![3, 2]
#eval ComparisonNetwork.trivial_network.apply ![1, 2]



-- [x] Sorting networks can be lists of index pair
-- [x] Need some sort of proposition that says a network sorts
-- Forms a setoid with an equivalence for reordering independent pairs

-- then i can write a function with a given tuple forms a permutation that is sorted
-- which can be applied to the tuple to give a sorting function

def Prod.compare_and_exchange (p : α × α) : α × α :=
  let (a, b) := p
  if a ≤ b then (a, b) else (b, a)

@[grind =]
theorem Prod.compare_and_exchange.eq_min_max {p : α × α}
    : p.compare_and_exchange = (min p.fst p.snd, max p.fst p.snd) := by
  rw [Prod.compare_and_exchange]
  split_ifs <;> ext <;> order

example {p : α × α} : p.compare_and_exchange.fst ≤ p.compare_and_exchange.snd := by
  rw [Prod.compare_and_exchange]
  split_ifs <;> order

def Tuple.compare_and_exchange (i j : Fin n) (_ : i < j) (t : Tuple α n) : Tuple α n :=
  fun k ↦
    if k = i ∨ k = j then
      let (less, greater) := (t i, t j).compare_and_exchange
      if k = i then less else greater
    else
      t k

def Tuple.compare_and_exchange.MonotoneOn_ij {i j : Fin n} {h : i < j} (t : Tuple α n)
    : MonotoneOn (compare_and_exchange i j h t) {i, j} := by
  intro a ha b hb a_le_b
  by_cases a_eq_b : a = b
  { subst_vars; rfl }
  have : i = a ∧ j = b := by grind only [= Set.mem_singleton_iff, = Set.mem_insert_iff]
  grind only [= compare_and_exchange, = Prod.compare_and_exchange.eq_min_max,
    inf_le_iff, le_max_left]

-- First proof of a valid sorting function!
example : SortingFunction (Tuple.compare_and_exchange (α := α) (n := 2) 0 1 (by decide)) := by
  intro t
  rw [Sorted, <- monotoneOn_univ, (by grind : Set.univ (α := Fin 2) = {0, 1})]
  exact Tuple.compare_and_exchange.MonotoneOn_ij t

-- def Tuple.compare_and_exchange.Equiv (i j : Fin n) (f : Fin n → α) : Equiv.Perm (Fin n) where
--   toFun := sorry
--   invFun := sorry
--   left_inv := by sorry
--   right_inv := by sorry
