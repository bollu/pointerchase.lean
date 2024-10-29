-- Little engines of proof, lecture 4

-- https://www.csl.sri.com/people/shankar/LEP/LEP5.pdf
import Std
open Std

namespace PointerChase

/-- The (polynomial) functor of the data we want to store, parametrized by the pointer locations -/
inductive NodeF (α : Type) (f : Type) where
| value (value : Bool)
| var (a : α) (low high : f)

instance : Functor (NodeF α) where
  map f
  | .value v => .value v
  | .var a low high => .var a (f low) (f high)


def ValueNode α := NodeF α Unit

/-- The value of the node, without any of the pointer information we attach to it. -/
def NodeF.toValueNode : NodeF α f → ValueNode α := Functor.map (fun _ => ())

@[simp]
theorem NodeF.toValueNode_value {α f : Type} (v : Bool) : (@NodeF.value α f v).toValueNode = NodeF.value v := rfl

@[simp]
theorem NodeF.toValueNode_var {α f : Type} {a} {low high} : (@NodeF.var α f a low high).toValueNode = NodeF.var a () () := rfl

/-- Coerce any node to a value node, that forgets the pointer data. -/
instance : CoeOut (NodeF α f) (ValueNode α) where
  coe := NodeF.toValueNode

/-- A Node has fields as natural numbers. -/
abbrev PreNode α := NodeF α Nat

def PreNode.LessThan (n : PreNode α) (ix : Nat) : Prop :=
  match n with
  | .value _ => True
  | .var _ low high => low < ix ∧ high < ix

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


structure Nodes (α : Type) where
  heap : Array (PreNode α)
  ordered : ∀ {i : Nat} (hi : i < heap.size), heap[i].LessThan i


/-- A handle to a node in a nodes data structure -/
structure Nodes.Ptr {α : Type} (nodes : Nodes α) where
  ix : Nat
  hix : ix < nodes.heap.size

def Nodes.Ptr.Lt {α : Type} {nodes : Nodes α}
  (h₁ h₂ : nodes.Ptr) : Prop := h₁.ix < h₂.ix

@[simp]
def Nodes.Ptr.Lt_trans {α : Type} {nodes : Nodes α} (p q r : nodes.Ptr) :
    p.Lt q → q.Lt r → p.Lt r := by
  simp [Nodes.Ptr.Lt]
  omega

/-- Ptr.Lt is transitive -/
instance {α : Type} {nodes : Nodes α} :
    Trans (Nodes.Ptr.Lt) (Nodes.Ptr.Lt) (Nodes.Ptr.Lt (nodes := nodes)) where
  trans p q := by apply Nodes.Ptr.Lt_trans <;> assumption

/-- The size of the node pointer is an accessibility relation. -/
def Nodes.Ptr.Lt_Acc {α : Type} {nodes : Nodes α} (n : nodes.Ptr):
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

def Nodes.Ptr.Lt_Wf {α : Type} {nodes : Nodes α} : WellFounded (Nodes.Ptr.Lt (nodes := nodes)) := by
  constructor
  exact Nodes.Ptr.Lt_Acc

instance (priority := high) : WellFoundedRelation (Nodes.Ptr nodes) where
  rel := Nodes.Ptr.Lt
  wf := Nodes.Ptr.Lt_Wf



/-- Get a prenode from the set of nodes. -/
def Nodes.getPreNode (nodes : Nodes α) (ptr : nodes.Ptr) : PreNode α :=
  have := ptr.hix
  nodes.heap[ptr.ix]

/-- An interned node -/
def Nodes.Inode {α : Type} (nodes : Nodes α) := NodeF α nodes.Ptr


/-- ordering on the nodes, given by the ordering on the pointers. -/
def Nodes.Inode.Lt {α : Type} {nodes : Nodes α} (n₁ n₂ : nodes.Inode) : Prop :=
  match n₁, n₂ with
  |  _, .value _ => False
  | .value _, .var .. => False
  | .var _ low₁ high₁, .var _ low₂ high₂ =>
    low₁.Lt low₂ ∧ high₁.Lt high₂

/--
First show that the subset of nodes that are variables are well founded,
ignoring values
-/
def Nodes.Inode.Lt_AccAux {α : Type} {nodes : Nodes α} (n : nodes.Inode) :
    match n with
    | .value .. => True
    | .var .. => Acc (Inode.Lt (nodes := nodes)) n :=
  match hn : n with
  | .value .. => by simp
  | .var ax low high => by
    simp
    constructor
    intros y hy
    cases y
    case value _ =>
      simp [Inode.Lt] at hy
    case var ay low' high' =>
      simp [Inode.Lt] at hy
      have := Lt_AccAux (NodeF.var ay low' high')
      simp at this
      exact this
  termination_by
    match n with
    | .value .. => 0
    | .var a low high => 1 + low.ix + high.ix
  decreasing_by
    simp_wf
    simp [Lt, Ptr.Lt] at hy
    omega

/-- Now show that all nodes are well founded, by terminating at the values,
and using the auxiliary lemma for variables. -/
def Nodes.Inode.Lt_acc {α : Type} {nodes : Nodes α} (n : nodes.Inode) :
    Acc (Inode.Lt (nodes := nodes)) n :=
  match n with
  | .value .. => by
    constructor
    intros y hy
    simp [Lt] at hy
  | .var ax lowx highx => by
    have := Nodes.Inode.Lt_AccAux (NodeF.var ax lowx highx)
    simp at this
    exact this

def Nodes.Inode.Lt_Wf {α : Type} {nodes : Nodes α} : WellFounded (Inode.Lt (nodes := nodes)) := by
  constructor
  exact Nodes.Inode.Lt_acc

/-- The Lt relation is a wellfounded relation for `nodes.Inode`-/
instance (priority := high) {α : Type} {nodes : Nodes α} : WellFoundedRelation (nodes.Inode) where
  rel := Nodes.Inode.Lt
  wf := Nodes.Inode.Lt_Wf


/-- A pointer that is derived from a base pointer,
and is thus guaranteed to be smaller. -/
structure Nodes.Ptr.DerivedPtr {α : Type} {nodes : Nodes α} (p : nodes.Ptr) extends nodes.Ptr where
  hlt : toPtr.Lt p

/-- An interned node, whose pointers are derived from a base pointer. -/
def Nodes.Ptr.DerivedINode {α : Type} {nodes : Nodes α} (p : nodes.Ptr) :=
  NodeF α p.DerivedPtr

structure Nodes.Ptr.Val {α : Type} {nodes : Nodes α} (p : nodes.Ptr) where
  val : nodes.Inode

instance {α : Type} {nodes : Nodes α} {p : nodes.Ptr} :
    CoeOut (Nodes.Ptr.DerivedPtr p) (nodes.Ptr) where
  coe dp := dp.toPtr

@[simp]
theorem Nodes.Ptr.DerivedPtr.Lt {α : Type} {nodes : Nodes α} (p : nodes.Ptr)
  (q : p.DerivedPtr) : q.Lt p := q.hlt

/-- Get the value at the handle. -/
def Nodes.Ptr.val {α : Type} {nodes : Nodes α} (p : nodes.Ptr) : p.DerivedINode :=
  have hinbounds := p.hix
  match hn : nodes.heap[p.ix] with
  | .value v => NodeF.value v
  | .var a low high =>
    let lowPtr : p.DerivedPtr := {
      ix := low
      hix := by
        have := nodes.ordered hinbounds
        simp [hn] at this
        omega,
      hlt := by
        have := nodes.ordered hinbounds
        simp [hn] at this
        simp [Lt]
        omega
    }
    let highPtr : p.DerivedPtr := {
      ix := high
      hix := by
        have := nodes.ordered hinbounds
        simp [hn] at this
        omega,
      hlt := by
        have := nodes.ordered hinbounds
        simp [hn] at this
        simp [Lt]
        omega
    }
    .var a lowPtr highPtr


/--
Sweet lord, this actually works!
I can write imperative looking code where I dereference pointers,
and have the sweet sweet magic of well founded induction
to ensure that this terminates. Zero overhead :O.
-/
def eg1CaseToEnd {α : Type} (nodes : Nodes α) (p : nodes.Ptr) : Bool :=
  match p.val with
  | .value v => v
  | .var _ low high => eg1CaseToEnd nodes low && eg1CaseToEnd nodes high
termination_by p

/-
Why does termination_by not figure this case out?
It should just chain the inequalities!
We have that low < p, and high < p, so low < high.
-/
def eg2DoubleDeref {α : Type} (nodes : Nodes α) (p : nodes.Ptr) : Bool :=
  match hp : p.val with
  | .value v => v
  | .var _ lowp highp =>
    match hq : lowp.val with
    | .value v => v
    | .var _ lowq highq => eg2DoubleDeref nodes lowq && eg2DoubleDeref nodes highq
termination_by p
/- This is pure tedium, this should be automatically chained. Ask Joachim? -/
decreasing_by
  simp_wf
  · apply Nodes.Ptr.Lt_trans
    · have lt := lowq.Lt
      exact lt
    · have lt := lowp.Lt
      exact lt
  · apply Nodes.Ptr.Lt_trans
    · have lt := highq.Lt
      exact lt
    · have lt := lowp.Lt
      exact lt

/-- An empty heap -/
def Nodes.empty : Nodes α := {
  heap := #[],
  ordered := by
    intros i hi
    cases hi
}

def Nodes.Inode.toPreNode {α : Type} {nodes : Nodes α} (n : nodes.Inode) : PreNode α :=
  match n with
  | .value v => NodeF.value v
  | .var a low high => NodeF.var a low.ix high.ix

@[simp]
theorem Nodes.Inode_inboundes {α : Type} {nodes : Nodes α} (n : nodes.Inode) :
  n.toPreNode.LessThan nodes.heap.size := by
  cases n
  case value v =>
    simp [PreNode.LessThan, Nodes.Inode.toPreNode]
  case var a low high =>
    simp [PreNode.LessThan, Nodes.Inode.toPreNode]
    have hlow := low.hix
    have hhi := high.hix
    omega

def Nodes.lastPtr {α : Type} {nodes : Nodes α} (h : nodes.heap.size > 0) : nodes.Ptr :=
  { ix := nodes.heap.size - 1,
    hix := by
      have := h
      omega
  }

structure Nodes.insert.Result (α : Type) where
  nodes : Nodes α
  ptr : nodes.Ptr

/-- Given a well formed, interned node, insert it into the set of nodes. -/
def Nodes.insert (nodes : Nodes α) (n : nodes.Inode) : Nodes.insert.Result α :=
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
theorem Nodes.val_ptr_insert_eq
  (nodes : Nodes α) (n : nodes.Inode) :
  (nodes.insert n).ptr.val.toValueNode = n.toValueNode := by
  simp [Nodes.insert, Nodes.Ptr.val, Nodes.lastPtr]
  split
  case h_1 v heq =>
    simp [Array.size_push] at heq
    cases n
    case value v =>
      simp [Inode.toPreNode] at heq
      subst v
      simp [NodeF.toValueNode]
      rfl
    case var v lo hi =>
      simp [Inode.toPreNode] at heq
  case h_2 v heq =>
    simp [Array.size_push] at heq
    cases n
    case value v =>
      simp [Inode.toPreNode] at heq
    case var v lo hi =>
      simp [Inode.toPreNode] at heq
      obtain ⟨s1, _, _⟩ := heq
      subst s1 
      simp

end PointerChase
