module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
public import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedState
public import VerifiedGarbage.Impl.Bignum.Arm.FiosPipelined
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedOps
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedValue
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Issue a product, then cancel the preceding product in the other register. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosPipelined
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

abbrev clobbers : List Reg := [.r3,.r5,.r6,.r7,.r8,.r10]

theorem step_ok {s0 s : State} {x q base : BitVec 32} {size acc b mod n start i : Nat}
    {pending next : Reg} (regs : (pending=.r6 ∧ next=.r10) ∨ (pending=.r10 ∧ next=.r6))
    (ctx : Fios.Ctx s0 base size acc b mod n)
    (h : Inv s0 x q base acc b mod n start i pending s)
    (hi : i+3≤n) (offsetFits : 4*(i-start)+8<4096) :
    WP isa (VG.Impl.Bignum.Arm.FiosPipelined.step (4*(i-start)) pending next) s
      (Inv s0 x q base acc b mod n start (i+1) next) := by
  have hp : pending=.r6 ∨ pending=.r10 := by rcases regs with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
  have hn : next=.r6 ∨ next=.r10 := by rcases regs with ⟨_,rfl⟩|⟨_,rfl⟩ <;> simp
  have nowrap := ctx.workspace.nowrap
  have outf := ctx.accFits
  have inf := ctx.bFits
  have modf := ctx.mFits
  have progress := h.progress
  have ws := ctx.workspace.congr h.rest.wr
  rw [VG.Impl.Bignum.Arm.FiosPipelined.step,WP.seq_iff]
  refine WP.mono (productAt_ok s next hn ws (by omega) (by omega) (by omega) h.bPtr h.outPtr) ?_
  rintro u ⟨product,memU,restU⟩
  have eB : b+4*(start+1)+(4*(i-start)+4)=b+4*(i+2) := by omega
  have eT : acc+4*start+(4*(i-start)+4)+4=acc+4*(i+2) := by omega
  have oldB := h.outside.w32 (d:=b+4*(i+2)) (by rcases ctx.accB with h|h <;> omega) (by omega)
  have oldT := h.outside.w32 (d:=acc+4*(i+2)) (by omega) (by omega)
  rw [eB,eT,h.scalar,oldB,oldT] at product
  refine WP.mono (cancelAt_ok u pending hp (ws.congr restU.wr) (by omega) (by omega) (by omega)
    ((restU.gpr .r4 (by rcases hn with rfl|rfl <;> decide)).trans h.mPtr)
    ((restU.gpr .r0 (by rcases hn with rfl|rfl <;> decide)).trans h.outPtr)) ?_
  rintro v ⟨cancel,memV,restV⟩
  have eM : mod+4*(start+1)+4*(i-start)=mod+4*(i+1) := by omega
  have eO : acc+4*start+4*(i-start)=acc+4*i := by omega
  rw [eO,memU] at memV
  have oldM := h.outside.w32 (d:=mod+4*(i+1)) (by rcases ctx.accM with h|h <;> omega) (by omega)
  rw [memU,eM,oldM,restU.gpr pending (by rcases regs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),
    restU.gpr .r2 (by rcases hn with rfl|rfl <;> decide),h.quotient,
    restU.gpr .r8 (by rcases hn with rfl|rfl <;> decide)] at cancel
  have productFinal : (v.gpr next).toNat+2^32*(v.gpr .r7).toNat=
      w32 s0.mem (State.addr base) (acc+4*(i+2))+
      x.toNat*w32 s0.mem (State.addr base) (b+4*(i+2))+(s.gpr .r7).toNat := by
    rw [restV.gpr next (by rcases regs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide),
      restV.gpr .r7 (by rcases hp with rfl|rfl <;> decide)]
    omega
  have nowrap' : (State.addr base).toNat+size≤2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨writes,stored⟩ := store_prefix nowrap' (by omega) memV
  have outside : Outside (State.addr base) acc (4*(i+1)) s0.mem v.mem :=
    (h.outside.mono (Nat.le_refl _) (by omega)).trans (writes.mono (by omega) (by omega))
  have rest : Rest clobbers s v :=
    (restU.mono (by rcases hn with rfl|rfl <;> simp [clobbers])).trans
      (restV.mono (by rcases hp with rfl|rfl <;> simp [clobbers]))
  refine ⟨by omega,by omega,?_,?_,?_,?_,?_,?_,outside,?_,?_⟩
  · rw [rest.gpr .r0 (by simp [clobbers])];exact h.outPtr
  · rw [rest.gpr .r12 (by simp [clobbers])];exact h.bPtr
  · rw [rest.gpr .r4 (by simp [clobbers])];exact h.mPtr
  · rw [rest.gpr .lr (by simp [clobbers])];exact h.count
  · rw [rest.gpr .r1 (by simp [clobbers])];exact h.scalar
  · rw [rest.gpr .r2 (by simp [clobbers])];exact h.quotient
  · exact step_prefix h.value productFinal cancel stored
  · exact h.rest.trans (rest.mono (by simp [clobbers,roundClobbers]))

end VG.Proof.Bignum.Arm.FiosPipelined
