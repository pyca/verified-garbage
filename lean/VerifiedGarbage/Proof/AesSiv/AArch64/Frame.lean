import VerifiedGarbage.Proof.AesSiv.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# AES-SIV's key setup on AArch64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2560 bytes that allocates it
(`Verified.stackScratch`). Its calls keep their return address in `x30`, so
they use no stack below it.
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.Impl.AesSiv.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre AArch64.abi.ptrBits) (post := Spec.Siv.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide) initFrameSat_pre

end VG.Proof.AesSiv.AArch64
