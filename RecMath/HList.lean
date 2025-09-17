import Mathlib
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Sigma.Basic

-- Should i rewrite stack using List.TProd?
-- abbrev Stack := List.TProd id

/-- A typed heterogeneous list -/
inductive HList.{u} : List (Type u) -> Type (u + 1) where
  | nil : HList []
  | cons {α β}: α -> HList β -> HList (α :: β)



infixr:67 "; " => HList.cons

universe u
variable {A B : Type u} {α α' β β' γ : List (Type u)} {a : HList α} {b : HList β} {g : HList γ}

section HList.append

def HList.append {α β : List (Type u)} : HList α -> HList β -> HList (α ++ β)
  | nil, rest => rest
  | head; tail, rest => head; tail.append rest

instance Stack.instHAppend : HAppend (HList α) (HList β) (HList (α ++ β)) := HAppend.mk HList.append

@[simp, grind =] theorem HList.nil_append : (nil ++ a) = a := rfl

@[grind =] theorem HList.cons_append {x : A} : x; a ++ b = x; (a ++ b) := rfl

end HList.append


-- def HList.repeat (n : Nat) (a : HList α) : HList (List.replicate n α).flatten := sorry

def HList.cast (a : HList α) (h : α = β) : HList β := h ▸ a

@[simp, grind ←] theorem HList.cast_rfl (a : HList α) : a.cast rfl = a := rfl

-- This theorem lets me change between eq cast and heq easily
theorem HList.eq_cast_iff_heq {h : β = α} : a = b.cast h <-> a ≍ b := by
  -- grind only [<- cast_rfl, cases Or]
  subst_vars; rw [heq_iff_eq]; rfl

-- theorem HList.cast_heq : a.cast rfl ≍ a := by
--   rw [HList.cast]

@[simp, grind =]
theorem HList.cast_cast {h : α = β} {h' : β = γ} : (a.cast h).cast h' = a.cast (h.trans h') := by
  subst_vars; rfl

-- @[grind ←]
theorem HList.cast_eq_symm {h : α = β} : a.cast h = b <-> b.cast h.symm = a := by
  subst_vars; tauto

@[simp, grind =]
theorem HList.cons_cast {x : A} {h : α = β} : x; (a.cast h) = (x; a).cast (by rw [h]) := by
  subst_vars; rfl

@[simp, grind =]
theorem HList.cast_append {h : α = α'} : a.cast h ++ b = (a ++ b).cast (by rw [h]) := by
  subst_vars; rfl

@[simp, grind =]
theorem HList.append_cast {h : β = β'} : a ++ b.cast h = (a ++ b).cast (by rw [h]) := by
  subst_vars; rfl

@[simp, grind =]
theorem HList.append_nil : (a ++ nil) = a.cast (by rw [List.append_nil]) := by
  -- induction a <;> grind only [= nil_append, = cons_append, ← cast_rfl]
  induction a with
  | nil => rw [nil_append]; rfl
  | cons head tail h => rw [cons_append, h, cons_cast]

@[grind →]
theorem HList.cons_cancel {x : A} {h : β = α} :
    x; a = (x; b).cast (by rw [h]) -> a = b.cast h := by
  -- -- First grindable proof!!
  -- grind only [= cons_cast, <- cast_rfl]
  subst_vars
  intro h
  exact (cons.inj h).2 -- injection h

theorem HList.cons_cancel_iff {x : A} {h : β = α} :
    x; a = (x; b).cast (by rw [h]) <-> a = b.cast h := by
  -- grind only [cases Or, -> cons_cancel, = cons_cast]
  constructor
  { exact cons_cancel }
  { rintro rfl; rw [cons_cast] }

@[grind →]
theorem HList.append_left_cancel {a : HList α} {b c : HList β}
    (h : a ++ b = (a ++ c).cast rfl) : b = c.cast rfl := by
  -- induction a <;> grind only [= nil_append, = cons_append, ← cast_rfl]
  induction a with
  | nil =>
    rwa [nil_append, nil_append] at h
  | cons head tail h' =>
    apply h'
    rw [cons_append] at h
    injection h

theorem HList.append_cons {y : A} :
    a ++ y; b = (a ++ (y; nil) ++ b).cast (by rw [<- List.append_cons]) := by
  -- induction a <;> grind
  induction a with
  | nil => rw [nil_append, nil_append, cons_append, nil_append, cast_rfl]
  | cons x a ha => rw [cons_append, cons_append, cons_append, cons_cancel_iff, ha]

@[simp, grind =]
theorem HList.append_assoc : a ++ b ++ g = (a ++ (b ++ g)).cast (by simp) := by
  -- induction a <;>
  -- grind only [= nil_append, ← List.nil_append, → append_left_cancel, = cons_append, ← cast_rfl]
  induction a with
  | nil => rw [nil_append, nil_append, cast_rfl]
  | cons x a ha => rw [cons_append, cons_append, cons_append, ha, cons_cast]

@[ext (iff := false)]
theorem HList.sigma_ext {a b : Sigma HList}
  (h : a.fst = b.fst) (h' : (a.snd = b.snd.cast h.symm)) : a = b := by
  -- grind [-> Sigma.ext]
  apply Sigma.ext h
  rw [<- eq_cast_iff_heq, h']

@[simp]
theorem HList.nil_inst (a : HList []) : a = nil := by
  -- grind only [cases HList]
  cases a with | nil => rfl

@[grind →]
theorem HList.append_right_cancel {a b : HList α} {c : HList β}
    (h : a ++ c = (b ++ c).cast rfl) : a = b.cast rfl := by
  -- induction a <;> grind? [cases HList]
  induction a with
  | nil => simp only [nil_inst]
  | cons x a ha =>
    cases b with
    | cons y b =>
      injection h with _ _ x_eq_y h'
      rw [x_eq_y]
      congr
      exact ha h'

section Algebra

instance HList.Sigma.instZero : Zero (Sigma HList) where zero := ⟨[], HList.nil⟩

@[simp, grind =]
theorem HList.Sigma.zero_fst : (0 : Sigma HList).fst = [] := rfl

@[simp, grind =]
theorem HList.Sigma.zero_snd : (0 : Sigma HList).snd = HList.nil := rfl

def HList.Sigma.append (a b : Sigma HList) : Sigma HList :=
  ⟨a.fst ++ b.fst, a.snd ++ b.snd⟩

instance HList.Sigma.instAdd : Add (Sigma HList) where add := HList.Sigma.append

@[simp, grind =]
theorem HList.Sigma.add_fst (a b : Sigma HList) : (a + b).fst = a.fst ++ b.fst := rfl

@[simp, grind =]
theorem HList.Sigma.add_snd (a b : Sigma HList) : (a + b).snd = a.snd ++ b.snd := rfl

instance HList.Sigma.instAddZeroClass : AddZeroClass (Sigma HList) where
  zero_add := by rintro a; rfl
  add_zero a := by ext1 <;> simp!
    -- ext1
    -- · rw [add_fst, zero_fst, List.append_nil]
    -- · rw [add_snd, zero_snd, append_nil]

instance HList.Sigma.instAddSemigroup : AddSemigroup (Sigma HList) where
  add_assoc a b c := by ext1 <;> simp!
    -- grind only [sigma_ext, = add_fst, = add_snd, = append_assoc, =_ List.append_assoc]
    -- ext1
    -- · simp! only [add_fst, List.append_assoc]
    -- · simp! only [add_fst, add_snd, append_assoc]

instance HList.Sigma.instAddMonoid : AddMonoid (Sigma HList) where
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

@[simp, grind =]
theorem HList.Sigma.nsmul_fst {n} (a : Sigma HList) :
   (n • a).fst = (List.replicate n a.fst).flatten := by
  induction n with
  | zero => rw [zero_nsmul, zero_fst, List.replicate_zero, List.flatten_nil]
  | succ n hn =>
    rw [succ_nsmul', add_fst, List.replicate_succ, List.flatten_cons, <- hn]

-- -- TODO: Implement a `HList.repeat (n : Nat) (a : HList α) : HList (List.replicate n α).flatten`
-- @[simp]
-- theorem HList.Sigma.nsmul_snd {n} (a : Sigma HList) : (n • a).snd = a.snd

instance HList.Sigma.instAddLeftCancelMonoid : AddLeftCancelMonoid (Sigma HList) where
  add_left_cancel := by
    -- intro a; rw [IsAddLeftRegular, Function.Injective]
    intro a b c h
    injection h with fst_eq snd_eq
    ext1
    · rw [List.append_cancel_left fst_eq]
    · apply append_left_cancel (a := a.snd)
      rw [<- cast, append_cast, cast_cast, eq_cast_iff_heq]
      exact snd_eq

instance HList.Sigma.instAddRightCancelMonoid : AddRightCancelMonoid (Sigma HList) where
  add_right_cancel := by
    -- intro a; rw [IsAddRightRegular, Function.Injective]
    intro a b c h
    injection h with fst_eq snd_eq
    ext1
    · rw [List.append_cancel_right fst_eq]
    · apply append_right_cancel (c := a.snd)
      rw [<- cast, cast_append, cast_cast, eq_cast_iff_heq]
      exact snd_eq
    -- grind? only [= IsAddRightRegular, = Function.Injective, -> sigma_ext,
    --   -> List.append_cancel_right, -> append_right_cancel, = cast_rfl, = add_fst, = add_snd]

instance HList.Sigma.instAddCancelMonoid : AddCancelMonoid (Sigma HList) where

instance HList.Sigma.instMulAction : MulAction Nat (Sigma HList) where
  one_smul b := by rw [one_nsmul]
  mul_smul x y b := by rw [mul_comm, mul_nsmul]

-- -- I dont think i actually need this instance. It should be possible, but probably not useful.
-- instance HList.Sigma.instIsAddTorsionFree : IsAddTorsionFree (Sigma HList) where
--   nsmul_right_injective := by
--     intro n n_nonzero
--     rw [Function.Injective]
--     intro a b h
--     cases n
--     · contradiction
--     rw [succ_nsmul', succ_nsmul'] at h
--     injection h with fst_eq snd_eq
--     simp at fst_eq
--     ext1
--     · sorry
--     · sorry

end Algebra

-- -- Old Stack Stuff
-- section Func
-- def HList.Func (params results : List (Type u)) :=
--   ∀ ⦃S : List (Type u)⦄, HList (params ++ S) -> HList (results ++ S)
-- end Func




section ToStrings

class ToStrings (α : Type u) where
  toStrings : α -> List String

instance : ToStrings (HList []) where
  toStrings _ := []

instance {α β} [Repr α] [ToStrings (HList β)] : ToStrings (HList (α :: β)) where
  toStrings
  | head ; tail => (toString (Repr.reprPrec head 100)) :: (ToStrings.toStrings tail)

instance HList.instToString {T} [ToStrings (HList T)] : ToString (HList T) where
  toString stack :=
    "[" ++ " ".intercalate (ToStrings.toStrings stack) ++ "]"

end ToStrings
