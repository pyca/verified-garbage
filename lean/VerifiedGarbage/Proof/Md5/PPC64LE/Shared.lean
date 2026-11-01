module

public import VerifiedGarbage.Proof.Md5.Contract
import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Md5.PPC64LE.Stream.Md
import VerifiedGarbage.Proof.Md5.Scratch
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.Md5.PPC64LE.Stream
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# MD5 on PPC64LE: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/PPC64LE/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`), 112 bytes after the
frame's 32-byte header.
-/

@[expose] public section

namespace VG.Proof.Md5.PPC64LE.Shared

theorem compress :
    Verified PPC64LE.target Impl.Md5.PPC64LE.compress (Proof.Md5.compressContract PPC64LE.abi) :=
  Proof.Md5.PPC64LE.compress_verified.of_implies (by
    contract_implies [Proof.Md5.compressContract, Proof.Md5.compressSig,
      Proof.Md5.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Md5.PPC64LE.satState] using Proof.Md5.PPC64LE.satState)

theorem init :
    Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.init (Spec.Md5.initContract PPC64LE.abi) :=
  Proof.Md5.PPC64LE.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Md5.PPC64LE.Stream.initSat] using Proof.Md5.PPC64LE.Stream.initSat)

theorem updateScratch :
    Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.update (Proof.Md5.updateScratchContract PPC64LE.abi 48) :=
  Proof.Md5.PPC64LE.Stream.Update.update_verified.of_implies (by
    contract_implies [Proof.Md5.updateScratchContract, Proof.Md5.updateScratchSig, Proof.Md5.updatePPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Md5.PPC64LE.Stream.Update.sat,
        MdStream.PPC64LE.Update.sat, Impl.Md5.PPC64LE.Stream.params] using Proof.Md5.PPC64LE.Stream.Update.sat)

theorem finalizeScratch :
    Verified PPC64LE.target Impl.Md5.PPC64LE.Stream.finalize (Proof.Md5.finalizeScratchContract PPC64LE.abi 48) :=
  Proof.Md5.PPC64LE.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Md5.finalizeScratchContract, Proof.Md5.finalizeScratchSig,
      Proof.Md5.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Md5.PPC64LE.Stream.Finalize.sat,
        MdStream.PPC64LE.Finalize.satD, Impl.Md5.PPC64LE.Stream.params]
      using Proof.Md5.PPC64LE.Stream.Finalize.sat)

/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 144 .r7 Impl.Md5.PPC64LE.Stream.update)
    (Spec.Md5.updateContract PPC64LE.abi (48 + 144)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 48) (bytes := 144)
    updateScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Md5.updatePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 144 .r6 Impl.Md5.PPC64LE.Stream.finalize)
    (Spec.Md5.finalizeContract PPC64LE.abi (48 + 144)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 48) (bytes := 144)
    finalizeScratch (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Md5.finalizePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Md5.PPC64LE.Shared
