module

public import VerifiedGarbage.Proof.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Md
import VerifiedGarbage.Proof.Sha1.Scratch
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Stream
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# SHA-1 on PPC64LE: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha1/PPC64LE/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha1/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`), 160 bytes after the
frame's 32-byte header.
-/

@[expose] public section

namespace VG.Proof.Sha1.PPC64LE.Shared

theorem compress :
    Verified PPC64LE.target Impl.Sha1.PPC64LE.compress (Proof.Sha1.compressContract PPC64LE.abi) :=
  Proof.Sha1.PPC64LE.compress_verified.of_implies (by
    contract_implies [Proof.Sha1.compressContract, Proof.Sha1.compressSig,
      Proof.Sha1.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha1.PPC64LE.satState] using Proof.Sha1.PPC64LE.satState)

theorem init :
    Verified PPC64LE.target Impl.Sha1.PPC64LE.Stream.init (Spec.Sha1.initContract PPC64LE.abi) :=
  Proof.Sha1.PPC64LE.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha1.PPC64LE.Stream.initSat] using Proof.Sha1.PPC64LE.Stream.initSat)

theorem updateScratch :
    Verified PPC64LE.target Impl.Sha1.PPC64LE.Stream.update (Proof.Sha1.updateScratchContract PPC64LE.abi 48) :=
  Proof.Sha1.PPC64LE.Stream.Update.update_verified.of_implies (by
    contract_implies [Proof.Sha1.updateScratchContract, Proof.Sha1.updateScratchSig, Proof.Sha1.updatePPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha1.PPC64LE.Stream.Update.sat,
        MdStream.PPC64LE.Update.sat, Impl.Sha1.PPC64LE.Stream.params] using Proof.Sha1.PPC64LE.Stream.Update.sat)

theorem finalizeScratch :
    Verified PPC64LE.target Impl.Sha1.PPC64LE.Stream.finalize (Proof.Sha1.finalizeScratchContract PPC64LE.abi 48) :=
  Proof.Sha1.PPC64LE.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sha1.finalizeScratchContract, Proof.Sha1.finalizeScratchSig,
      Proof.Sha1.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha1.PPC64LE.Stream.Finalize.sat,
        MdStream.PPC64LE.Finalize.satD, Impl.Sha1.PPC64LE.Stream.params]
      using Proof.Sha1.PPC64LE.Stream.Finalize.sat)

/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update)
    (Spec.Sha1.updateContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 48) (bytes := 192)
    updateScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha1.updatePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize)
    (Spec.Sha1.finalizeContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 48) (bytes := 192)
    finalizeScratch (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha1.finalizePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha1.PPC64LE.Shared
