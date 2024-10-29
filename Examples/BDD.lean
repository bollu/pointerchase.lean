import PointerChase.Basic
-- Little engines of proof, lecture 4

-- https://www.csl.sri.com/people/shankar/LEP/LEP5.pdf

/-
/-- A BDD, represented as a tree -/
inductive Tree
| value (value : Bool)
| var (low high : Tree)
deriving DecidableEq, Hashable, Inhabited

def Tree.mkFalse : Tree := Tree.value false

namespace Node


/--
A node is irredundant if either it's not a variable node,
or if it is a variable node, then the low and high nodes are different.
-/
def NoSameChildren (n : Node α) : Prop :=
  ∀ {a low high}, n = .var a low high → low ≠ high

end Node

def Ordered (nodes : Array (Node α)) : Prop :=
  ∀ {i a low high} (hi : i < nodes.size),
     nodes[i] = .var a low high → (low < i) ∧ (high < i)

@[simp]
def Ordered_empty : Ordered (#[] : Array (Node α)) := by
  intros i _a low high hi _hnode
  cases hi

def Cache (α : Type) [DecidableEq α] [Hashable α] : Type :=
  HashMap (Node α) Nat

def Cache.empty {α : Type} [DecidableEq α] [Hashable α] : Cache α := HashMap.empty

inductive Cache.WF (α : Type) [DecidableEq α] [Hashable α] :
    (cache : Cache α) → (nodes : Array (Node α)) → Prop where
/-- The empty cache is always well formed -/
| empty : Cache.WF α (Cache.empty) nodes

structure RODD (α : Type) [DecidableEq α] [Hashable α] where
  nodes : Array (Node α)
  cache : Cache α

/-- A handle to a canonicalized node in the RODD hash map. -/
partial def RODD.canonNode [DecidableEq α] [Hashable α]
  (n : Node α) (rodd : RODD α) : Node α := Id.run do
  match n with
  | .value v =>
    /- TODO: prove that this can't happen -/
    -- We can show that we will never use the default value.
    let .some ix := rodd.cache.get? n | return n
    rodd.nodes.getD ix n
  | .var a low high =>
     let low := RODD.canonNode <| rodd.nodes[low]!
     let high := RODD.canonNode <| rodd.nodes[high]!




def RODD.empty {α : Type} [DecidableEq α] [Hashable α] : RODD α := {
  nodes := #[],
  cache := HashMap.empty,
  }

namespace RODD

variable {α : Type} [DecidableEq α] [Hashable α] {m : Type → Type} [Monad m]
def postorderAt (nodes : Array (Node α)) (ordered : Ordered nodes) (fvar : σ → Bool → m σ) (fnode : (init : σ) → (a : α) →  (lo : σ) → (hi : σ) → m σ)
    (init : σ) (ix : Nat) (hix : ix < nodes.size) : m σ := do
  match hnode : nodes[ix] with
  | .value v => fvar init v
  | .var a lo hi =>
    have := ordered hix hnode
    let loVal ← postorderAt nodes ordered fvar fnode init lo (by omega)
    let hiVal ← postorderAt nodes ordered fvar fnode init hi (by omega)
    fnode init a loVal hiVal

/-- Postorder traversal of BDD -/
def postorder (d : RODD α) (init : σ)
    (fvar : σ → Bool → m σ) (fnode : (init : σ) → (a : α) → (lo : σ) → (hi : σ) → m σ)  : m σ := do
  if h : d.nodes.size = 0
  then return init
  else postorderAt d.nodes d.ordered fvar fnode init (d.nodes.size-1) (by omega)

/-- Convert the subDAG into a tree. -/
def treeAt {ix: Nat} (nodes : Array (Node α)) (ordered : Ordered nodes) (hix : ix < nodes.size): Tree :=
  Id.run <| postorderAt nodes ordered
    (fvar := fun _ v => return Tree.value v)
    (fnode := fun _  _ lo hi => return Tree.var lo hi)
    Tree.mkFalse ix hix

/- An empty RODD. -/
def RODD.empty {α : Type} [DecidableEq α] [Hashable α] : RODD α := {
  nodes := #[],
  cache := HashMap.empty,
  ordered := by simp,
}


namespace Node
end Node
-/
