module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPrimePower
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStack
public import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Reload ciphertext and private-exponent pointers after factor preparation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest)

theorem crt_primePowerArgs_ok (s : State) {base xp ep : BitVec 32} {len k eLen slot : Nat}
    (h : CrtPowerStack base xp ep len k eLen slot s) :
    WP isa (.block (primePowerArgs slot)) s fun t => t.gpr .r4 = xp ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧
      t.gpr .r1 = ep ∧ t.gpr .r2 = BitVec.ofNat 32 eLen ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r4, .r6] s t := by
  have nowrap := h.nowrap
  have fit := h.slotFit
  change WP isa (.block ([.ldrSp .r4 56, .ldrSp .r6 12] ++ [.ldrSp .r1 slot, .ldrSp .r2 (slot + 4)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (stackPair_ok s .r4 .r6 56 12 (by decide) (by decide) (by decide)
    (by omega) (by omega) h.readable.1 h.readable.2.1) ?_
  rintro u ⟨input, count, memU, restU⟩
  refine WP.mono (stackPair_ok u .r1 .r2 slot (slot + 4) (by decide) (by omega) (by omega)
    (by rw [restU.sp]; omega) (by rw [restU.sp]; omega)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.readable.2.2.1)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.readable.2.2.2)) ?_
  rintro t ⟨exponent, ecount, memT, restT⟩
  rw [memU, restU.sp, h.exponent] at exponent
  rw [memU, restU.sp, h.exponentCount] at ecount
  exact ⟨(restT.gpr .r4 (by simp)).trans (input.trans h.input),
    (restT.gpr .r6 (by simp)).trans (count.trans h.inputCount), exponent, ecount,
    memT.trans memU, (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Bignum.Arm
