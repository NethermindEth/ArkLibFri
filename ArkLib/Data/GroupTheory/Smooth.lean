import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-
  Redefinition of IsCyclic from Mathlib with computable generator.
  This avoids the use of Classical.choose to extract the generator,
  making dependent definitions incomputable.
-/

class IsCyclicWithGen (G : Type) [Pow G ℤ] where
  gen : G
  zpow_surjective : Function.Surjective (gen ^ · : ℤ → G)

instance {G} [Pow G ℤ] [inst : IsCyclicWithGen G] : IsCyclic G where
  exists_zpow_surjective := ⟨inst.gen, inst.zpow_surjective⟩

-- class Smooth
--   (p : ℕ) [Fact (Nat.Prime p)]
--   (n : ℕ) (G : Type) [Pow G ℤ] [Monoid G] [inst : IsCyclicWithGen G] where
--   smooth : orderOf inst.gen = p ^ n

class SmoothPowerOfTwo (n : ℕ) (G : Type) [Pow G ℤ] [Monoid G] [inst : IsCyclicWithGen G] where
  smooth : orderOf inst.gen = 2 ^ n

-- instance {n : ℕ} {G : Type} [Pow G ℤ] [Monoid G] [inst : IsCyclicWithGen G] [inst : Smooth 2 n G] :
--   SmoothPowerOfTwo n G where
--   smooth := inst.smooth

-- instance {n : ℕ} {G : Type} [Pow G ℤ]  [Monoid G]
--   [inst : IsCyclicWithGen G] [inst : SmoothPowerOfTwo n G] :
--     Smooth 2 n G where
--   smooth := inst.smooth
