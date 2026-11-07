module
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Formula
public import VerifiedGarbage.Proof.X25519.AArch64.Word.Head

import VerifiedGarbage.Proof.X25519.AArch64.Ladder
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! The 255 public-count ladder iterations and the final conditional swaps. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem setCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t =>
      t.gpr .x19 = n.setWidth 64 ∧ Keeps [.x19] s t := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr =>
    RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩


end VG.Proof.X25519.AArch64.Word
