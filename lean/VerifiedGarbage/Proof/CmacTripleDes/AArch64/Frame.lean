import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# TDEA-CMAC on AArch64, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame of 640 bytes that allocates it
(`Verified.stackScratch`).
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.Impl.CmacTripleDes.AArch64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract AArch64.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x3 init)
      (Spec.Cmac.tdesInitContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesInitPost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) init_verified (by decide) (by decide) initFrameSat_pre

theorem update_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x4 update)
      (Spec.Cmac.tdesUpdateContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) update_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 640 .x4 finalize)
      (Spec.Cmac.tdesFinalizeContract AArch64.abi 640) :=
  AArch64.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre AArch64.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost AArch64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 640) finalize_verified (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))

end VG.Proof.CmacTripleDes.AArch64
