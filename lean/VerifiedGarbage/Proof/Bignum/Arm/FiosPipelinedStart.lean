module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedState
public import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedOps
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedValue
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Issue the first pending product before the streaming scan. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem start_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start : Nat}
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : FiosFixed.Inv s0 x q base acc b mod n start start s) (hi : start+2≤n) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.productAt 0 .r6) s
      (Inv s0 x q base acc b mod n start start .r6) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  refine WP.mono (productAt_ok s .r6 (Or.inl rfl) (ctx.workspace.congr h.rest.wr)
    (by decide) (by omega) (by omega) h.bPtr h.outPtr) ?_
  rintro t ⟨value,mem,rest⟩
  simp only [Nat.add_zero] at value
  have oldT := h.outside.w32 (d:=acc+4*(start+1)) (by omega) (by omega)
  have oldB := h.outside.w32 (d:=b+4*(start+1))
    (by rcases ctx.accB with h|h <;> omega) (by omega)
  rw [h.scalar,show acc+4*start+4=acc+4*(start+1) by omega,oldT,oldB] at value
  have product : (t.gpr .r6).toNat+2^32*(t.gpr .r7).toNat=
      w32 s0.mem (State.addr base) (acc+4*(start+1))+
      x.toNat*w32 s0.mem (State.addr base) (b+4*(start+1))+(s.gpr .r7).toNat := by omega
  refine ⟨hi,Nat.le_refl _,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rest.gpr .r0 (by decide)];exact h.outPtr
  · rw [rest.gpr .r12 (by decide)];exact h.bPtr
  · rw [rest.gpr .r4 (by decide)];exact h.mPtr
  · rw [rest.gpr .lr (by decide)];exact h.count
  · rw [rest.gpr .r1 (by decide)];exact h.scalar
  · rw [rest.gpr .r2 (by decide)];exact h.quotient
  · rw [mem];exact h.outside
  · rw [mem,rest.gpr .r8 (by decide)]
    exact start_prefix h.value product
  · exact h.rest.trans (rest.mono (by decide))

end VG.Proof.Bignum.Arm.FiosPipelined
