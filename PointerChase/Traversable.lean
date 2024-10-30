/- Typeclass for folding and traversing a functor -/

-- What I actually want is an indexed container, aka a representable functor.
-- We encode the representable functor in terms of a lens-like API.
class Foldable (f : Type → Type) [Functor f]  where
  Ix : Type -- return the size representing the number of slots in the container.
  /-- Get the kth value -/
  get : f α → (Ix → α)
  /-- Build a container from a function of values -/
  build : (Ix → α) → f α
  positions : f Ix
  get_build (ix2val : Ix → α) : get (build ix2val) = ix2val
  build_get (container : f α) : build (get container) = container
  get_map (container : f α) (fn : α → β) : get (fn <$> container) ix = fn (get container ix) 
  
attribute [simp] Foldable.get_map
attribute [simp] Foldable.get_build
attribute [simp] Foldable.build_get

/-- Get is injective, because it's a bijection -/
theorem Foldable.get_inj [Functor f] [Foldable f] (c c' : f α) (h : get c = get c') : c = c' := by
  have : build (get c) = build (get c') := by simp [h]
  simp only [build_get] at this
  exact this

/-- Build is injective, because it's a bijection -/
theorem Foldable.build_inj [Functor f] [Foldable f] (ix2val ix2val' : Ix f → α) (h : build ix2val = build ix2val') : ix2val = ix2val' := by
  have : get (build ix2val) = get (build ix2val') := by simp [h]
  simp only [get_build] at this
  exact this

/-- Dual of get_map in terms of build. Mapping a function after building is the same as mapping it before building. -/
@[simp]
theorem Foldable.map_build [Functor f] [Foldable f] (ix2val : Ix f → α) (fn : α → β) : 
    fn <$> (build ix2val) = build (fn ∘ ix2val) := by
  apply Foldable.get_inj
  funext ix
  simp

/-- Predicate holds for all indexes -/
def Foldable.ForAll [Functor f] [Foldable f] (container : f α) (p : α → Prop) : Prop := 
  ∀ (ix : Ix f), p (get container ix)

@[simp]
theorem Foldable.ForAll.toForall [Functor f] [Foldable f] : ForAll container p ↔ ∀ (ix : Ix f), p (get container ix) := by
  simp [ForAll]

/-- Attach the rest of a ForAll at every location -/
def Foldable.attachForAll [Functor f] [Foldable f] {container : f α} {p : α → Prop} (h : ForAll container p) : f { a : α // p a } :=
  build fun ix => ⟨get container ix, by simp at h; apply h⟩


namespace Foldable
variable {f : Type → Type} [Functor f] [Foldable f] {α : Type} {σ : Type}

end Foldable

/-
class Traversable (f : Type → Type) [Functor f] extends Foldable f where
  traverseM {m : Type → Type} [Applicative m] : (container : f α) → (eff : α → m β) → m (f β)
-/

/-- For a given functor, fill all the values with `Unit` -/
def Functor.fillUnit [Functor f] : f a → f Unit := Functor.mapConst ()

@[simp]
theorem Functor.fillUnit_fmap [Functor f] [LawfulFunctor f] 
    (container : f α) (fn : α → β) : Functor.fillUnit (fn <$> container) = Functor.fillUnit container := by
  simp [fillUnit, map_const, ← comp_map]

@[simp]
theorem Functor.fillUnit_attachForAll [Functor f] [LawfulFunctor f] [Foldable f]
    (container : f α) {p : α → Prop} (h : Foldable.ForAll container p) : Functor.fillUnit (Foldable.attachForAll h) = Functor.fillUnit container := by
  simp [fillUnit, map_const, ← comp_map, Foldable.attachForAll]
  apply Foldable.get_inj
  funext ix
  simp

