module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Key
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.RsaKeyGen.Arm.Key
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # An RSA key on ARMv7: the shared pieces the taint analysis checks

The loops counted by `r6` (`mulMod`, `inverse`), checked with `r6` and
`r7`–`r9` public, and the counts.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Key

theorem lsl3_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6])
    (.block [.mov .r6 (.shifted .r6 .lsl 3)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem mov64_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [])
    (.block [.mov .r6 (.imm 64)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem mulMod_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r6, .r7, .r8, .r9])
    (mulMod aZero aMy aMx aMa aMod aMt) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev Cert (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r7, .r8, .r9]) c hc).isSome = true

theorem copy1M_taint : Cert (copy 1 aM) := ⟨_, by taint_decide⟩
theorem copy2One_taint : Cert (copy 2 aOne) := ⟨_, by taint_decide⟩
theorem copy3Zero_taint : Cert (copy 3 aZero) := ⟨_, by taint_decide⟩
theorem subNM_taint : Cert (sub3 aNM aZero aM) := ⟨_, by taint_decide⟩

theorem ctxW_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8]) (.block ctxW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mov11_taint : Cert (.block [.mov .r11 (.imm 0)]) := ⟨_, by taint_decide⟩
theorem halfT2_taint : Cert (half aTmp2) := ⟨_, by taint_decide⟩
theorem dZero_taint : Cert (.block dZero) := ⟨_, by taint_decide⟩

/-- `setupK` after the loads of `scratch` and `p_len`. -/
abbrev setupTail : List Instr :=
  [.mov .r9 (.shifted .r9 .lsr 1), .dp .add .r9 .r9 (.imm 4)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

theorem setupK_eq : setupK = ctxB ++ (([.ldrSp .r9 aoPl] : List Instr) ++ setupTail) := rfl

theorem setupTail_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r8, .r9]) (.block setupTail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem zero_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .lr]) VG.Impl.Bignum.Arm.zero hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A load, with its source pointer and length and the working space's registers public. -/
abbrev LCert (j : Nat) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r4, .r6, .r7, .r8, .r9])
    (VG.Impl.Rsa.Arm.CrtValues.load j) hc).isSome = true

theorem loadP_taint : LCert aP0 := ⟨_, by taint_decide⟩
theorem loadQ_taint : LCert aQ0 := ⟨_, by taint_decide⟩
theorem loadE_taint : LCert aE := ⟨_, by taint_decide⟩

theorem one_taint : Cert (.block (setWd aOne 0 1)) := ⟨_, by taint_decide⟩
theorem two_taint : Cert (.block (setWd aTwo 0 2)) := ⟨_, by taint_decide⟩
theorem three_taint : Cert (.block (setWd aThree 0 3)) := ⟨_, by taint_decide⟩
theorem mod_taint : Cert (.block (setHi aMod 2 4 0x80000000)) := ⟨_, by taint_decide⟩
theorem top_taint : Cert (.block (setHi aTop 2 20 0x80000000)) := ⟨_, by taint_decide⟩
theorem c33_taint : Cert (.block (setWd aC33 4 2)) := ⟨_, by taint_decide⟩

end VG.Proof.RsaKeyGen.Arm.Key
