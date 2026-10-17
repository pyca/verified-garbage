module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover
meta import VerifiedGarbage.Impl.Rsa.Arm.Recover
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the pieces the taint analysis checks

Each piece between the loads from the stack, the Montgomery products and the
divisions computes its addresses and loop counts from the registers given
here, which two runs agree on by correctness: `r8` after the base is loaded,
and `r7`–`r9` once the working space's context is set.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover

theorem ctxw_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ctxw) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ctxW_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8]) (.block ctxW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clrTopY_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (clrTop (mBase + iY))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clrTopG_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (clrTop (mBase + iG))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clrTopXm_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (clrTop (mBase + iXm))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem clrTopX_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (clrTop (mBase + iX))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `setupK` after the loads of the base and `n_len`. -/
abbrev setupKTail : List Instr :=
  [.dp .add .r9 .r9 (.imm 7), .mov .r9 (.shifted .r9 .lsr 3), .mov .r9 (.shifted .r9 .lsl 1),
    .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

theorem setupK_eq : setupK = ctxB ++ (([.ldrSp .r9 aoK] : List Instr) ++ setupKTail) := rfl

theorem setupKTail_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8, .r9]) (.block setupKTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zero_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r0, .lr]) VG.Impl.Bignum.Arm.zero hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem loadN_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load aN) hc).isSome = true := ⟨_, by taint_decide⟩

theorem loadE_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load (2 * wE)) hc).isSome = true := ⟨_, by taint_decide⟩

theorem loadD_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load (2 * wD)) hc).isSome = true := ⟨_, by taint_decide⟩

theorem setTop_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (.block (setTop wMod)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem shl3_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) (.block [.mov .r6 (.shifted .r6 .lsl 3)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mulMod_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r6, .r7, .r8, .r9])
    (mulMod wZ wE wD wM wMod wT) hc).isSome = true := ⟨_, by taint_decide⟩

theorem skip_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (.seq (.block skipBits) (.seq (sub3 wT wZ wM) (.block skipTest))) hc).isSome = true := ⟨_, by taint_decide⟩

theorem copyRM_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (copy wR wM) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tZero_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8])
    (.block [.mov .r1 (.imm 0), .str .r1 .r8 sTc]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem cntStore_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8])
    (.block [.dp .add .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem halfBody_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) halfBody hc).isSome = true :=
  ⟨_, by taint_decide⟩

end VG.Proof.Rsa.Arm.Recover
