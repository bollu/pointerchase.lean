import PointerChase.Traversable
import Std
open Std

namespace PointerChase



/-- Coerce any node to a value node, that forgets the pointer data. -/
instance [Functor NodeF] [Foldable NodeF] : CoeOut (NodeF α) (NodeF Unit) where
  coe := Functor.fillUnit

/-- A Node has fields as natural numbers. -/
abbrev PreNode (NodeF : Type → Type) := NodeF Nat

def PreNode.LessThan [Functor NodeF] [Foldable NodeF] (n : PreNode NodeF) (ix : Nat) : Prop := 
  Foldable.ForAll n (fun v => v < ix)


/-
@[simp]
theorem PreNode.LessThan_var :
  (PreNode.LessThan (NodeF.var a low high) ix) ↔ low < ix ∧ high < ix := by
  constructor
  · intros h
    simp [LessThan] at h
    exact h
  · intros h
    simp [LessThan]
    exact h
-/

structure Nodes (NodeF) [Functor NodeF] [Foldable NodeF] where
  heap : Array (PreNode NodeF)
  ordered : ∀ {i : Nat} (hi : i < heap.size), heap[i].LessThan i


/-- A handle to a node in a nodes data structure -/
structure Nodes.Ptr [Functor NodeF] [Foldable NodeF] (nodes : Nodes NodeF) where
  ix : Nat
  hix : ix < nodes.heap.size

@[simp]
theorem Nodes.Ptr.lt_heap_size [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (p : nodes.Ptr) :
  p.ix < nodes.heap.size := p.hix

def Nodes.Ptr.Lt {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF}
  (h₁ h₂ : nodes.Ptr) : Prop := h₁.ix < h₂.ix

@[simp]
def Nodes.Ptr.Lt_trans {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (p q r : nodes.Ptr) :
    p.Lt q → q.Lt r → p.Lt r := by
  simp [Nodes.Ptr.Lt]
  omega

/-- Ptr.Lt is transitive -/
instance {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} :
    Trans (Nodes.Ptr.Lt) (Nodes.Ptr.Lt) (Nodes.Ptr.Lt (nodes := nodes)) where
  trans p q := by apply Nodes.Ptr.Lt_trans <;> assumption

/-- The size of the node pointer is an accessibility relation. -/
def Nodes.Ptr.Lt_Acc {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (n : nodes.Ptr) :
    Acc (Nodes.Ptr.Lt) n :=
  match hn : n.ix with
  | 0 => by
    constructor
    intros x hx
    simp [Lt, hn] at hx
  | n' + 1 => by
    constructor
    intros x hx
    simp [Lt, hn] at hx
    apply Lt_Acc
termination_by n.ix

def Nodes.Ptr.Lt_Wf {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF]
    {nodes : Nodes NodeF} : WellFounded (Nodes.Ptr.Lt (nodes := nodes)) := by
  constructor
  exact Nodes.Ptr.Lt_Acc

instance (priority := high) {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF]
    {nodes : Nodes NodeF}  : WellFoundedRelation (Nodes.Ptr nodes) where
  rel := Nodes.Ptr.Lt
  wf := Nodes.Ptr.Lt_Wf



/-- Get a prenode from the set of nodes. -/
def Nodes.getPreNode {NodeF : Type → Type} [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (ptr : nodes.Ptr) : PreNode NodeF :=
  have := ptr.hix
  nodes.heap[ptr.ix]

/-- An interned node -/
def Nodes.Inode [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF}  := NodeF nodes.Ptr

/-- Erase all pointers in the inode -/
def Nodes.Inode.erasePointers [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (inode : nodes.Inode) : NodeF Unit := Functor.fillUnit inode


/-- A pointer that is derived from a base pointer,
and is thus guaranteed to be smaller.
TODO: it's always possible to keep a sentinel pointer, and derive all pointers from the sentinel?
TODO: The ordering should not be in terms of Nat, but rather directly in terms of the naperian structure?
-/
structure Nodes.Ptr.DerivedPtr {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF} (p : nodes.Ptr) extends nodes.Ptr where
  hlt : toPtr.Lt p

/-- An interned node, whose pointers are derived from a base pointer. -/
def Nodes.Ptr.DerivedInode {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  (p : nodes.Ptr) :=
  NodeF p.DerivedPtr


instance {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  {p : nodes.Ptr} :
    CoeOut (Nodes.Ptr.DerivedPtr p) (nodes.Ptr) where
  coe dp := dp.toPtr

/-- Convert a derived INode into a regular Inode -/
def Nodes.Ptr.DerivedInode.toInode [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  {p : nodes.Ptr} (dinode : p.DerivedInode) : nodes.Inode :=
  Functor.map (fun (q : p.DerivedPtr) => (↑q : nodes.Ptr)) dinode

instance {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  {p : nodes.Ptr} :
    CoeOut (p.DerivedInode) (nodes.Inode) where
  coe dinode := dinode.toInode

@[simp]
theorem Nodes.Ptr.DerivedPtr.Lt {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  (p : nodes.Ptr)
  (q : p.DerivedPtr) : q.Lt p := q.hlt


def Nodes.Ptr.mkDerivedINode {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF} (p : nodes.Ptr) (n : PreNode NodeF)
    (hn : n.LessThan p.ix) :  p.DerivedInode :=
  have hpix := p.hix
  Functor.map (fun hix => {
    ix := hix.val,
    hix := by
      omega
    hlt := by 
      simp [Nodes.Ptr.Lt]
      omega
  }) (Foldable.attachForAll hn) 

/-- Get the value at the handle. -/
def Nodes.Ptr.val {NodeF} [Functor NodeF] [Foldable NodeF]  {nodes : Nodes NodeF}  (p : nodes.Ptr) : p.DerivedInode :=
  have hinbounds := p.hix
  let v := nodes.heap[p.ix]
  have := nodes.ordered hinbounds
  p.mkDerivedINode v this



/-- An empty heap -/
def Nodes.empty [Functor NodeF] [Foldable NodeF] : Nodes NodeF := {
  heap := #[],
  ordered := by
    intros i hi
    cases hi
}


def Nodes.Inode.toPreNode [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (n : nodes.Inode) : PreNode NodeF :=
  Functor.map (fun p => p.ix) n

@[simp]
theorem Nodes.Inode_inboundes [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (n : nodes.Inode) :
    n.toPreNode.LessThan nodes.heap.size := by
  simp [PreNode.LessThan, Nodes.Inode.toPreNode]

def Nodes.lastPtr [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (h : nodes.heap.size > 0) : nodes.Ptr :=
  { ix := nodes.heap.size - 1,
    hix := by
      have := h
      omega
  }

@[simp]
theorem Nodes.ix_lastPtr  [Functor NodeF] [Foldable NodeF] {nodes : Nodes NodeF} (h : nodes.heap.size > 0) : 
  (nodes.lastPtr h).ix = nodes.heap.size - 1 := rfl


structure Nodes.insert.Result (NodeF : Type → Type) [Functor NodeF] [Foldable NodeF] where
  nodes : Nodes NodeF
  ptr : nodes.Ptr

/-- Given a well formed, interned node, insert it into the set of nodes. -/
def Nodes.insert [Functor NodeF] [Foldable NodeF] (nodes : Nodes NodeF) (n : nodes.Inode) : Nodes.insert.Result NodeF :=
  let nodes' := { nodes with
    heap := nodes.heap.push n.toPreNode,
    ordered := by
      intros i hi
      simp at hi
      have hi' : i = nodes.heap.size ∨ i < nodes.heap.size := by omega
      cases hi'
      case inl hi' =>
        subst hi'
        simp
      case inr hi' =>
        simp [Array.get_push_lt (h :=hi')]
        have := nodes.ordered hi'
        simp [this]
  }
  let ptr := nodes'.lastPtr <| by
    have := nodes'.heap.size
    simp
  ⟨nodes', ptr⟩


/-- Grabbing the values gives us equal results -/
@[simp]
theorem Nodes.val_ptr_insert_eq [Functor NodeF] [Foldable NodeF] [LawfulFunctor NodeF]
  (nodes : Nodes NodeF) (n : nodes.Inode) :
  ((nodes.insert n).ptr.val.toInode.erasePointers) = n.erasePointers := by
  simp [Inode.erasePointers, Nodes.Ptr.DerivedInode.toInode, Nodes.Ptr.val, Nodes.insert, Ptr.mkDerivedINode, Inode.toPreNode]
end PointerChase
