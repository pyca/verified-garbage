module

public import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
public import VerifiedGarbage.Proof.Bignum.Arm.MontFnBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.MontCallArithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallStack
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Preserve the RSA workspace while saving registers and loading the fifth argument -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

structure CallInput (base : BitVec 32) (len w o a b : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  outIndex : s.gpr .r2 = BitVec.ofNat 32 o
  aIndex : s.gpr .r3 = BitVec.ofNat 32 a
  bArg : s.mem.readW (State.addr s.sp) 32 = BitVec.ofNat 32 b
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0
  stackFit : 40 ≤ s.sp.toNat
  argRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackWorkspace : (FrameStack.belowA s.sp 40).Disjoint ⟨State.addr base, 8 * len⟩
  stackArg : (FrameStack.belowA s.sp 40).Disjoint ⟨State.addr s.sp, 4⟩

theorem CallInput.pushed_eq {s : State} {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) : WorkspaceEq (State.addr base) (8 * len) s.mem (callPushed s).mem := by
  have nowrap := h.workspace.nowrap
  exact WorkspaceEq.of_frame (by omega) (FrameStack.pushed_frameA h.stackFit) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackWorkspace.symm)

theorem call_entry_ok (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : CallInput base len w o a b s) (hb : b < 8) :
    WP isa (.block [.ldrSp .r12 40]) (callPushed s) fun t =>
      FnBodyReady base len w o a b t ∧ t.mem = (callPushed s).mem ∧ Rest [.r12] (callPushed s) t := by
  have frame := FrameStack.pushed_frameA (rs := MontCall.savedRegs) h.stackFit
  have arg : (callPushed s).mem.readW (State.addr s.sp) 32 = BitVec.ofNat 32 b := by
    rw [frame.readW (r := ⟨State.addr s.sp, 4⟩) (by simp [Region.Contains])
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackArg.symm) (by decide)]
    exact h.bArg
  have read : InRegions ((callPushed s).rd ++ (callPushed s).wr) (State.addr s.sp) 4 :=
    InRegions_append_cons.mpr (Or.inr h.argRead)
  have addr : State.addr ((callPushed s).sp + BitVec.ofNat 32 40) = State.addr s.sp := by
    change State.addr (s.sp - 40 + 40) = _
    rw [BitVec.sub_add_cancel]
  refine wp_loadStack (by decide) addr read fun t ut => WP.block_nil ?_
  have eq := h.pushed_eq
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have small : 64 ≤ 8 * len := by
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits
    omega
  have mFits := array_end_le (w := w) (j := 0) (k := 8) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ut.gpr.trans arg, ?_, ?_⟩, ut.mem, ut.rest (by simp)⟩
  · refine ⟨h.workspace.nowrap, ?_⟩
    rw [ut.wr]
    exact List.mem_cons_of_mem _ h.workspace.writable
  · rw [ut.mem]; exact eq.layout h.layout
  · rw [ut.mem, eq.width (by omega), h.width]
  · exact (ut.other .r0 (by decide)).trans h.ptr
  · exact (ut.other .r2 (by decide)).trans h.outIndex
  · exact (ut.other .r3 (by decide)).trans h.aIndex
  · rw [ut.mem]
    have modulus : word (callPushed s).mem (State.addr base) (arrAt w 0) =
        word s.mem (State.addr base) (arrAt w 0) := eq.word (d := arrAt w 0) (bits := 64) (by omega)
    rw [modulus]
    have inv := eq.word (d := 56) (bits := 64) (by omega)
    change wordAt (callPushed s).mem (State.addr base) Proof.Rsa.Mont.minvWord =
      wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord at inv
    rw [inv]; exact h.inverse
  · rw [ut.mem, eq.number fits hb, eq.number fits (by decide : 0 < 8)]
    exact h.operand

end VG.Proof.Bignum.Arm
