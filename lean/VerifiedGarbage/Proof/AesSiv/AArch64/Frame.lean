import VerifiedGarbage.Proof.AesSiv.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# AES-SIV on AArch64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2560 bytes that allocates it
(`Verified.stackScratch`). Its calls keep their return address in `x30`, so
they use no stack below it.

`encrypt` and `decrypt` run theirs, proved with the working space as their
last argument (in `x7`), in a frame of 2576 bytes that allocates it, the
same way: the frame leaves the memory as it is, so the list of slices they
take needs nothing more.
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

/-- A state satisfying `vg_aes_siv_encrypt`'s precondition, without the
working space. -/
def encFrameSat : State := { encSat with wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩] }

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, AArch64.abi, AArch64.argRegs]
    [encFrameSat, encSat] using encFrameSat

theorem encrypt_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2576 .x7 (encrypt v.callee v.ctr.callee v.ctr.suffix))
      (Spec.Siv.encryptContract AArch64.abi 2576) :=
  AArch64.Verified.stackScratch (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre AArch64.abi.ptrBits) (post := Spec.Siv.encryptPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) (encrypt_verified v) (by decide) (by decide) encFrameSat_pre

/-- A state satisfying `vg_aes_siv_decrypt`'s precondition, without the
working space. -/
def decFrameSat : State := { decSat with wr := [⟨0x3000, 0⟩] }

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract AArch64.abi 2576).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, AArch64.abi, AArch64.argRegs] [decFrameSat, decSat, encSat] using decFrameSat

theorem decrypt_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2576 .x7 (decrypt v.callee v.ctr.callee v.ctr.suffix))
      (Spec.Siv.decryptContract AArch64.abi 2576) :=
  AArch64.Verified.stackScratch (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre AArch64.abi.ptrBits) (post := Spec.Siv.decryptPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2576) (leak := some (Spec.Siv.decryptLeak AArch64.abi.ptrBits))
    (decrypt_verified v) (by decide) (by decide) decFrameSat_pre

end VG.Proof.AesSiv.AArch64
