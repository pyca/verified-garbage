module

import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Prepare
import VerifiedGarbage.Proof.Sm4.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Core
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Spec.Camellia

/-! # Copy the expanded schedule using the existing checked block copier -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Sm4.AArch64 (CopyInv copyBlocks_wp)

theorem copySchedule_wp {s : State}
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128)
    (hw : InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 256) 128)
    (hsep : Region.Disjoint ⟨s.gpr .x0,128⟩ ⟨s.gpr .x5 + BitVec.ofNat 64 256,128⟩) :
    WP isa copySchedule s fun t =>
      (∀ j < 128, t.mem (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 j) =
        s.mem (s.gpr .x0 + BitVec.ofNat 64 j)) ∧
      Frame [⟨s.gpr .x5 + BitVec.ofNat 64 256,128⟩] s.mem t.mem ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → r ≠ .x21 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  let a := s.write .x .x14 (s.gpr .x0)
  let b := a.write .x .x15 (a.gpr .x5 + BitVec.ofNat 64 256)
  let c := b.write .x .x17 8
  have regs : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → c.gpr r = s.gpr r := by
    intro r h14 h15 h17
    simp only [c,b,a,gpr_write_of_ne _ _ _ h14,gpr_write_of_ne _ _ _ h15,gpr_write_of_ne _ _ _ h17]
  have c14 : c.gpr .x14 = s.gpr .x0 := by simp [c,b,a,State.write]
  have c15 : c.gpr .x15 = s.gpr .x5 + BitVec.ofNat 64 256 := by simp [c,b,a,State.write]
  have c17 : c.gpr .x17 = 8 := by simp [c,State.write]
  unfold copySchedule
  refine WP.seq (WP.of_runBlock ⟨c,?_,?_⟩)
  · have ea : exec (VG.Impl.Aes.AArch64.movR .x14 .x0) s = some a := by
      simp [VG.Impl.Aes.AArch64.movR,exec,State.read,a]
    have eb : exec (.addImm .x .x15 .x5 256) a = some b := by
      rw [exec_addImm_x (by decide)]
      simp [State.read,b]
    have ec : exec (.movz .x .x17 8 0) b = some c := rfl
    rw [runBlock_cons,ea,runStep_some,runBlock_cons,eb,runStep_some,
      runBlock_cons,ec,runStep_some,runBlock_nil]
  · have hA : ∀ j < 16, InRegions (c.rd ++ c.wr) (s.gpr .x0 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hr (by omega) (by decide)
    have hB : ∀ j < 16, InRegions c.wr (s.gpr .x5 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (8*j)) 8 := by
      intro j hj
      exact CallLay.inRegions_sub hw (by omega) (by decide)
    have inv : CopyInv (s.gpr .x0) (s.gpr .x5+ BitVec.ofNat 64 256) 8 c 0 c := by
      refine ⟨?_,?_,?_,fun _ h => absurd h (by omega),Frame.refl _ _,fun _ _ _ _ _ => rfl,rfl,rfl⟩
      · simpa using c14
      · simpa using c15
      · simpa using c17
    refine WP.mono (copyBlocks_wp (by decide) (by decide) hA hB hsep inv) fun t ht =>
      ⟨ht.copied,ht.frame,fun r h14 h15 h17 h21 =>
        (ht.regs r h14 h15 h17 h21).trans (regs r h14 h15 h17),ht.rd,ht.wr⟩

end VG.Proof.Sm4.AArch64.Serial
