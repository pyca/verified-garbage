import VerifiedGarbage.Proof.CmacTripleDes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# TDEA-CMAC on x86-64, with its working space on the stack

The functions run their code, proved with the working space as an argument
(`Verified.lean`), in a frame of 648 bytes that allocates it
(`Verified.stackScratch`): the 640 bytes of working space, and 8 more to keep
`rsp` aligned.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.Impl.CmacTripleDes.X86_64

/-- A state satisfying `vg_cmac_triple_des_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 400⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesInitContract X86_64.abi 648).pre s := by
  implies_sat [Spec.Cmac.tdesInitContract, Spec.Cmac.tdesInitSig, Spec.Cmac.tdesInitPre,
    Spec.Cmac.tdesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed : Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .rcx init)
    (Spec.Cmac.tdesInitContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesInitPre X86_64.abi.ptrBits) (post := Spec.Cmac.tdesInitPost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) init_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) initFrameSat_pre

theorem update_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .r8 update)
      (Spec.Cmac.tdesUpdateContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesUpdateSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesUpdatePost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) update_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 648 .r8 finalize)
      (Spec.Cmac.tdesFinalizeContract X86_64.abi 648) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.tdesFinalizeSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesFinalizePre X86_64.abi.ptrBits)
    (post := Spec.Cmac.tdesFinalizePost X86_64.abi.ptrBits)
    (wa := false) (stack := 0) (bytes := 648) finalize_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl))

end VG.Proof.CmacTripleDes.X86_64
