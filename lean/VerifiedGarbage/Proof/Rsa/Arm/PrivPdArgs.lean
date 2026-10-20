module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdPrefixMemory
import VerifiedGarbage.Proof.Rsa.Arm.PrivPdSuffix
import VerifiedGarbage.Proof.Framework.Block

/-! # All arguments and the saved precomputation status before re-exponentiation -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PdArgs (g : PrivGeometry) (s : State) : Prop where
  output : s.gpr .r0 = g.output
  outputLength : s.gpr .r1 = BitVec.ofNat 32 g.length
  precomputation : s.gpr .r2 = g.precomputation
  precomputationLength : s.gpr .r3 = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)
  arguments : ∀ j < 6, s.mem.readW (off (State.addr g.stack) (4 * j)) 32 = pdArgument g j

theorem pdArgs_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) :
    WP isa (.block pdArgs) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧ PdArgs g t ∧
      t.mem.readW (off (State.addr g.stack) oR3) 32 = s.gpr .r0 ∧
      Frame (pdPrefixWrites g) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r12] s t := by
  unfold pdArgs
  rw [WP.block_append_iff]
  refine WP.mono (pdPrefix_ok s h slots) ?_
  rintro u ⟨hu, slotsU, memU, frameU, restU⟩
  refine WP.mono (pdSuffix_ok u hu slotsU) ?_
  rintro t ⟨outT, lenT, preT, preLenT, memT, restT⟩
  have unchanged : Frame (bodyWrites g) u.mem t.mem := by rw [memT]; exact Frame.refl _ _
  refine ⟨hu.after unchanged restT, by rw [memT]; exact slotsU,
    ⟨outT, lenT, preT, preLenT, ?_⟩, ?_, ?_,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩
  · intro j hj
    rw [memT, memU]; exact pdPrefixMem_arguments g s j hj
  · rw [memT, memU]; exact pdPrefixMem_status g s
  · rw [memT]; exact frameU
end VG.Proof.Rsa.Arm
