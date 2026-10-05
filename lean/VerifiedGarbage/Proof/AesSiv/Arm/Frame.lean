import VerifiedGarbage.Proof.AesSiv.Arm.Verified
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# AES-SIV on ARMv7, with the working space on the stack

`encrypt` and `decrypt` run their code, proved with the working space as
their last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackScratchL`): their working space is their fourth stack
argument, after `data`, `len` and `siv`, so the frame holds a copy of those
three words, the address of the working space, the saved `lr` and the 2576
bytes of the working space, 2608 bytes in all (2596 rounded up to a multiple
of 8 that an instruction can encode). The copies are read only where the
pre- and postconditions read the buffers and the list of slices, and
`decrypt`'s leak, whether it succeeds, reads only those too
(`Proof/AesSiv/Scratch.lean`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm

theorem encFrameSat_pre : ∃ s, (Spec.Siv.encryptContract Arm.abi 2624).pre s := by
  implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Spec.Siv.encryptPre, Spec.Siv.encryptPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8000, 12⟩] [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem encrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2608 3 encrypt)
      (Spec.Siv.encryptContract Arm.abi 2624) :=
  Arm.Verified.stackScratchL (sig := Spec.Siv.encryptSig) (nm := "work") (e := .u64)
    (n := 322) (pre := Spec.Siv.encryptPre Arm.abi.ptrBits)
    (post := Spec.Siv.encryptPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (m := 3) encrypt_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesSiv.encryptPre_local _) (Proof.AesSiv.encryptPost_local _) encFrameSat_pre

theorem decFrameSat_pre : ∃ s, (Spec.Siv.decryptContract Arm.abi 2624).pre s := by
  implies_sat [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.decryptPre, Spec.Siv.decryptPost,
    Spec.Siv.decryptLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat [⟨0x1000, 512⟩, ⟨0x5000, 16⟩, ⟨0x2000, 0⟩, ⟨0x8000, 12⟩] [⟨0, 0⟩]

theorem decrypt_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 2608 3 decrypt)
      (Spec.Siv.decryptContract Arm.abi 2624) :=
  Arm.Verified.stackScratchL (sig := Spec.Siv.decryptSig) (nm := "work") (e := .u64)
    (n := 322) (pre := Spec.Siv.decryptPre Arm.abi.ptrBits)
    (post := Spec.Siv.decryptPost Arm.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Siv.decryptLeak Arm.abi.ptrBits))
    (m := 3) decrypt_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.AesSiv.decryptPre_local _) (Proof.AesSiv.decryptPost_local _) decFrameSat_pre
    (hleak := Proof.AesSiv.decryptLeak_local _)

end VG.Proof.AesSiv.Arm
