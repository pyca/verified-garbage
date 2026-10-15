module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerArgs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Restore factor-exponentiation arguments after Montgomery preparation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest)

theorem crt_primePower_ready (s : State) {base xp ep : BitVec 32} {len w k eLen slot M : Nat} {xb eb : List Byte}
    (h : CrtPreparedPower base xp ep len w k eLen slot M xb eb s) :
    WP isa (.block (primePowerArgs slot)) s fun t => SecretPowerInput base xp ep len w k eLen M xb eb t ∧
      t.mem = s.mem ∧ Rest [.r1, .r2, .r4, .r6] s t := by
  refine WP.mono (crt_primePowerArgs_ok s h.sources.stack) ?_
  rintro t ⟨input, count, exponent, ecount, mem, rest⟩
  have sources := h.sources.after_workspace (by rw [mem]; exact Frame.refl _ _) rest
  have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  refine ⟨⟨ready, ?_, h.odd, ?_, sources.input, sources.exponent, sources.inputSeparate,
    sources.exponentSeparate, sources.inputPositive, sources.inputFits, sources.exponentPositive, sources.exponentFits,
    input, count, exponent, ecount⟩, mem, rest⟩
  · rw [mem]; exact h.modulus
  · rw [mem]; exact h.r2

end VG.Proof.Bignum.Arm
