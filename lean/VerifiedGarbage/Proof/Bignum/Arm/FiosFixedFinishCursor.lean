module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedAdvance
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Advance the cursors once after the fixed scan. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFixed
open VG VG.Arm VG.Proof.Bignum.Arm

theorem finishCursor_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n) (h : Inv s0 x q base acc b mod n start i s)
    (h4 : encodable (BitVec.ofNat 32 (4*(i-start)))=true)
    (h1 : encodable (BitVec.ofNat 32 (i-start))=true) :
    WP isa (.block (VG.Impl.Bignum.Arm.FiosPipelined.advance (i-start))) s
      (Fios.Inv s0 x q base acc b mod n i) := by
  refine WP.mono (advance_ok s (i-start) h4 h1) ?_
  rintro t ⟨p0,p12,p4,count,_,mem,rt⟩
  have small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega
  refine ⟨h.index,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [p0,h.outPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [p12,h.bPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [p4,h.mPtr,Offset.add_add]
    congr 2
    have := h.progress;omega
  · rw [count,h.count,BitVec.ofNat_sub_ofNat_of_le _ _ (by have := h.index;omega) (by have := h.progress;have := h.index;omega)]
    congr 1
    have := h.progress;have := h.index;omega
  · rw [rt.gpr .r1 (by simp)];exact h.scalar
  · rw [rt.gpr .r2 (by simp)];exact h.quotient
  · rw [mem];exact h.outside
  · rw [mem,rt.gpr .r7 (by simp),rt.gpr .r8 (by simp)];exact h.value
  · exact h.rest.trans (rt.mono (by simp [roundClobbers]))

end VG.Proof.Bignum.Arm.FiosFixed
