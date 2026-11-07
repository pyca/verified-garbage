module

import VerifiedGarbage.Proof.Bignum.Arm.StackPair
import VerifiedGarbage.Proof.Bignum.Arm.MaskOutput
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Arm.PublicData
public import VerifiedGarbage.Proof.Bignum.Arm.PublicStack
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Invalid public keys produce an all-zero output and failure status -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem publicFailArgs_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    (h : PublicStack base dst np ep xp len k eLen s) :
    WP isa (.block PublicFn.failArgs) s fun t => t.gpr .r0 = dst ∧ t.gpr .lr = BitVec.ofNat 32 k ∧
      t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r0, .r2, .lr] s t := by
  change WP isa (.block ([.ldrSp .r0 4, .ldrSp .lr 12] ++ [.mov .r2 (.imm 0)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (stackPair_ok s .r0 .lr 4 12 (by decide) (by decide) (by decide)
    (by have := h.nowrap; omega) (by have := h.nowrap; omega)
    (h.read (by decide) (by decide)) (h.read (by decide) (by decide))) ?_
  rintro u ⟨output, count, mem, rest⟩
  refine wp_mov (op2_imm (by decide)) fun t a => WP.block_nil ?_
  exact ⟨(a.other .r0 (by decide)).trans (output.trans h.savedOutput),
    (a.other .lr (by decide)).trans (count.trans h.savedCount), a.gpr, a.mem.trans mem,
    (rest.mono (by decide)).trans (a.rest (by decide))⟩

end VG.Proof.Bignum.Arm
