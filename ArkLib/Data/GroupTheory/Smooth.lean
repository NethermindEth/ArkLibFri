import Mathlib.GroupTheory.SpecificGroups.Cyclic

class IsCyclicC (G : Type) [Pow G ℤ] where
  gen : G
  zpow_surjective : Function.Surjective (gen ^ · : ℤ → G)

instance {G} [Pow G ℤ] [inst : IsCyclicC G] : IsCyclic G where
  exists_zpow_surjective := ⟨inst.gen, inst.zpow_surjective⟩

class Smooth2 (n : ℕ) (G : Type) [Pow G ℤ] [Monoid G] [inst : IsCyclicC G] where
  smooth : orderOf inst.gen = 2 ^ n
