module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosFixedState
public import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedOps
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedValue
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedMemory
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Cancel the final pending product and recover the ordinary quotient invariant. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem finish_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    {pending : Reg} (hp : pending=.r6 ∨ pending=.r10)
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : Inv s0 x q base acc b mod n start i pending s)
    (offsetFits : 4*(i-start)<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.cancelAt (4*(i-start)) pending) s
      (FiosFixed.Inv s0 x q base acc b mod n start (i+1)) := by
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have modf := ctx.mFits
  have progress := h.progress
  have index := h.index
  refine WP.mono (cancelAt_ok s pending hp (ctx.workspace.congr h.rest.wr) offsetFits
    (by omega_using [modf, progress, index]) (by omega_using [outf, progress, index]) h.mPtr h.outPtr) ?_
  rintro t ⟨cancel,mem,rest⟩
  have eM : mod+4*(start+1)+4*(i-start)=mod+4*(i+1) := by omega_using [progress]
  have eO : acc+4*start+4*(i-start)=acc+4*i := by omega_using [progress]
  rw [eO] at mem
  have oldM := h.outside.w32 (d:=mod+4*(i+1)) (by rcases ctx.accM with h|h <;> omega_arith) (by omega_using [nowrap, modf, index])
  rw [eM,oldM,h.quotient] at cancel
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := store_prefix nowrap' (by omega_using [outf, index]) mem
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem t.mem :=
    (h.outside.mono (Nat.le_refl _) (by omega_using [])).trans (writes.mono (by omega_using []) (by omega_using []))
  refine ⟨by omega_using [index],by omega_using [progress],?_,?_,?_,?_,?_,?_,outside,?_,?_⟩
  · rw [rest.gpr .r0 (by rcases hp with rfl|rfl <;> decide)];exact h.outPtr
  · rw [rest.gpr .r12 (by rcases hp with rfl|rfl <;> decide)];exact h.bPtr
  · rw [rest.gpr .r4 (by rcases hp with rfl|rfl <;> decide)];exact h.mPtr
  · rw [rest.gpr .lr (by rcases hp with rfl|rfl <;> decide)];exact h.count
  · rw [rest.gpr .r1 (by rcases hp with rfl|rfl <;> decide)];exact h.scalar
  · rw [rest.gpr .r2 (by rcases hp with rfl|rfl <;> decide)];exact h.quotient
  · rw [rest.gpr .r7 (by rcases hp with rfl|rfl <;> decide)]
    exact finish_prefix h.value cancel stored
  · exact h.rest.trans (rest.mono (by rcases hp with rfl|rfl <;> simp [roundClobbers]))

end VG.Proof.Bignum.Arm.FiosPipelined
