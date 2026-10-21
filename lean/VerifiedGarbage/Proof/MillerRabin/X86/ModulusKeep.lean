module

public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
import VerifiedGarbage.Proof.MillerRabin.X86.Data

/-! # Scratch updates and array copies keep the candidate prepared -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont

theorem Modulus.keepScalar {g : Geometry} (v : g.Valid) {c d : Nat} {m m' : Mem}
    (M : Modulus g c m) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (scratch : scratchWord d) (O : Outside g.W d 4 m m') : Modulus g c m' := by
  have bound := scratch_fit scratch
  refine M.keep v (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))) ?_ ?_
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    unfold scratchWord at scratch
    dsimp only
    omega
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    right
    exact Nat.le_trans bound (v.arrayHeader 0)

theorem Modulus.keepArray {g : Geometry} (v : g.Valid) {c j : Nat} {m m' : Mem}
    (M : Modulus g c m) (nowrap : g.W.toNat + g.L ≤ 2 ^ 32)
    (notMod : 0 < j) (O : Outside g.W (g.array j) (4 * g.words) m m') : Modulus g c m' := by
  refine M.keep v (WorkspaceFrame.of_outs nowrap (Outs.of_outside O (List.mem_singleton_self _))) ?_ ?_
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader j))
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Or.inl (g.arrayBefore notMod)

end VG.Proof.MillerRabin.X86
