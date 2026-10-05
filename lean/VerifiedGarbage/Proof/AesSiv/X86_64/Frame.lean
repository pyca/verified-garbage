import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch

/-!
# AES-SIV on x86-64, with its working space on the stack

`vg_aes_siv_init` runs its code, proved with the working space as an argument
(`Verified.lean`), in a frame of 2568 bytes that allocates it
(`Verified.stackScratch`): the 2560 bytes of working space, and 8 more to
keep `rsp` aligned. Its own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no stack.

`encrypt` and `decrypt` run their code, proved with the working space as
their last argument, in a frame that allocates it
(`Verified.stackArgScratchL`): their working space is passed on the stack
after `siv`, so the frame of 2600 bytes holds the 2576 bytes of working
space, a copy of `siv`, the word that stands for the return address and the
address of the working space. The code's own calls use 16 bytes below it.
The frame copies `siv`, so the postconditions and `decrypt`'s leak must read
the memory on entry only within the buffers and the list of slices
(`encryptPost_local`, `decryptPost_local`, `decryptLeak_local`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.Impl.AesSiv.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, v.expandNoStack]
  decide +kernel

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 512⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract X86_64.abi 2584).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.expand v.callee v.suffix))
      (Spec.Siv.initContract X86_64.abi 2584) :=
  X86_64.Verified.stackScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre X86_64.abi.ptrBits) (post := Spec.Siv.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2568) (init_verified v) (by decide) (by decide) (by decide)
    (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem encrypt_xdepth (v : Ctr32Impl) : (encrypt v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [encrypt, encryptCore, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrBody, ctrMin, xorBytes, callUpdate, callFinalize, Impl.CmacAes.X86_64.update,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.body, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.noStack]
  decide +kernel

theorem decrypt_xdepth (v : Ctr32Impl) : (decrypt v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [decrypt, openTail, encS2v, s2vAds, cmacOf, cmacPre, finish, shortTail, longTail, shortMac, longMac,
    copy, ctr, ctrBody, ctrMin, xorBytes, maskData, callUpdate, callFinalize, Impl.CmacAes.X86_64.update,
    Impl.CmacAes.X86_64.finalize, Impl.CmacAes.X86_64.body, Impl.CmacAes.X86_64.finPre,
    Impl.CmacAes.Stream.X86_64.copy, Code.x86_64Depth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_aes_siv_encrypt`'s precondition, without the
working space. -/
def encFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩, ⟨0x5000, 16⟩] }

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, X86_64.abi, X86_64.argRegs,
    X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop]
    [encFrameSat, encSat, Mem.readW, Mem.read] using encFrameSat

theorem encrypt_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (encrypt v.callee v.suffix))
      (Spec.Siv.encryptContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.encryptPre X86_64.abi.ptrBits) (post := Spec.Siv.encryptPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (encrypt_verified v) (by decide) (by decide) (by decide)
    (encrypt_spSafe v) (encrypt_xdepth v) (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _)
    encFrameSat_pre

/-- A state satisfying `vg_aes_siv_decrypt`'s precondition, without the
working space. -/
def decFrameSat : State :=
  { encSat with rd := [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8008, 8⟩], wr := [⟨0x3000, 0⟩] }

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract X86_64.abi 2616).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, X86_64.abi, X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
    List.range.loop] [decFrameSat, encSat, Mem.readW, Mem.read] using decFrameSat

theorem decrypt_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2600 1 (decrypt v.callee v.suffix))
      (Spec.Siv.decryptContract X86_64.abi 2616) :=
  X86_64.Verified.stackArgScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64) (n := 322)
    (pre := Spec.Siv.decryptPre X86_64.abi.ptrBits) (post := Spec.Siv.decryptPost X86_64.abi.ptrBits)
    (wa := true) (stack := 16) (bytes := 2600) (leak := some (Spec.Siv.decryptLeak X86_64.abi.ptrBits))
    (decrypt_verified v) (by decide) (by decide) (by decide) (decrypt_spSafe v) (decrypt_xdepth v)
    (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _) decFrameSat_pre
    (hleak := Proof.AesSiv.decryptLeak_local _)

end VG.Proof.AesSiv.X86_64
