/-
Copyright (c) 2024-2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland
-/

import Init.Prelude
import Init.Data.List.Control

def replicateM {α : Type} {m} [Monad m] : Nat → m α → m (List α)
| 0, _ => pure []
| n + 1, m => do
  let a ← m
  let as ← replicateM n m
  pure (a::as)

example {α : Type} {m} [Monad m] [LawfulMonad m] {c : m α} {n : Nat} :
  (replicateM n c >>= pure ∘ List.length) = (replicateM n c >>= fun _ => pure n) := by
  induction n with
  | zero =>
    simp [pure_bind, replicateM]
  | succ n ih =>
    rw [replicateM, bind_assoc, bind_assoc]
    simp only [bind_assoc, bind_pure_comp, bind_map_left, Function.comp_apply, List.length_cons,
      Functor.map_map]
    simp only [bind_pure_comp] at ih
    have : (fun a ↦ n + 1) <$> replicateM n c = (fun n ↦ n + 1) <$> ((fun a ↦ n) <$> replicateM n c) := by
      simp
    rw [this, ←ih]
    simp

def mapM_ {α β : Type} {m} [Monad m] (f : α → m β) : List α -> m Unit
| [] => pure ()
| a :: as => do
  let _ ← f a
  mapM_ f as

def scanl {α β : Type} (f : β → α → β) : β → List α → List β
 | b, [] => [b]
 | b, (a :: as) => b :: scanl f (f b a) as

def scanlM {α β : Type} {m} [Monad m] (f : β → α → m β) : β → List α → m (List β)
 | b, [] => pure [b]
 | b, (a :: as) => do
  let b' <- f b a;
  let bs <- scanlM f b' as
  pure (b::bs)
