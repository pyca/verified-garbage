module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPro
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailCoreState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Sha3.AArch64.Callee

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64

theorem Saved.keep {σ : State} {m n : Mem} {W : List Region}
    (hs : Saved σ m) (hf : Frame W m n)
    (hd : ∀r∈W,(Region.mk (σ.gpr .x3) 160).Disjoint r) : Saved σ n := by
  constructor
  · intro i hi
    rw [hf.read (r:=⟨σ.gpr .x3,160⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact hs.vec i hi
  · intro i hi
    rw [hf.readW (r:=⟨σ.gpr .x3,160⟩)
      (Offset.contains_base _ (by omega) (by omega)) hd (by decide)]
    exact hs.regs i hi

theorem Saved.keep_core {σ : State} {m n : Mem}
    (hs : Saved σ m) (hf : Frame [bufferRegion (σ.gpr .x3)] m n) : Saved σ n := by
  apply hs.keep hf
  intro r hr
  rcases List.mem_singleton.mp hr with rfl
  exact (Offset.disjoint_base (σ.gpr .x3) (d:=256) (n:=680) (k:=160)
    (by decide) (by decide)).symm

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
