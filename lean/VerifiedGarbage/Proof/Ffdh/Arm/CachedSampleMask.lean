module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedMask
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.CachedSample
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! The cached sampler's three public mask shifts form one shared computation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedSample
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem mask_ok (s : State) {count : Nat} (fit : count < 8)
    (source : s.gpr .r9 = BitVec.ofNat 32 count) (initial : s.gpr .r3 = 255) :
    WP isa VG.Impl.Ffdh.Arm.CachedSample.mask s fun t =>
      t.gpr .r3 = (BitVec.ofNat 32 255) >>> count ∧ t.mem = s.mem ∧ Rest [.r3, .r12] s t := by
  rw [VG.Impl.Ffdh.Arm.CachedSample.mask, WP.seq_iff]
  refine WP.mono (maskShift_ok s 4 4 (by decide) (by decide) (by decide)) ?_
  rintro u ⟨valueU, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (maskShift_ok u 2 2 (by decide) (by decide) (by decide)) ?_
  rintro v ⟨valueV, memV, restV⟩
  refine WP.mono (maskShift_ok v 1 1 (by decide) (by decide) (by decide)) ?_
  rintro t ⟨valueT, memT, restT⟩
  have countU := (restU.gpr .r9 (by simp)).trans source
  have countV := (restV.gpr .r9 (by simp)).trans countU
  rw [countV, valueV, countU, valueU, source, initial, maskShifts_value count fit] at valueT
  exact ⟨valueT, memT.trans (memV.trans memU), (restU.trans restV).trans restT⟩

end VG.Proof.Ffdh.Arm.CachedSample
