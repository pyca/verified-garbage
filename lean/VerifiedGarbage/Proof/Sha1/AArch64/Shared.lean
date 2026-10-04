import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.AArch64.Compress
import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Sha1 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha1/AArch64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha1/Contract.lean`, which the artifacts are emitted with.

`update_of` and `finalize_of` keep the working space in a frame of their
own: they are `updateScratch_of` and `finalizeScratch_of` (the shared
contracts with the working space as an argument, which HMAC's and PBKDF2's
code calls) run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha1.AArch64.Shared

theorem compress_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.compressAArch64) :
    Verified AArch64.target code (Spec.Sha1.compressContract AArch64.abi) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.satState] using Proof.Sha1.AArch64.satState)

theorem init :
    Verified AArch64.target Impl.Sha1.AArch64.Stream.init (Spec.Sha1.initContract AArch64.abi) :=
  Proof.Sha1.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.initSat] using Proof.Sha1.AArch64.Stream.initSat)

theorem updateScratch_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.updateAArch64) :
    Verified AArch64.target code (Spec.Sha1.updateScratchContract AArch64.abi 16) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.updateScratchContract, Spec.Sha1.updateScratchSig, Proof.Sha1.updateAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Sha1.AArch64.Stream.params] using Proof.Sha1.AArch64.Stream.Update.sat)

theorem finalizeScratch_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.finalizeAArch64) :
    Verified AArch64.target code (Spec.Sha1.finalizeScratchContract AArch64.abi 16) :=
  hv.of_implies (by
    sig_implies [Spec.Sha1.finalizeScratchContract, Spec.Sha1.finalizeScratchSig,
      Proof.Sha1.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sha1.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Sha1.AArch64.Stream.params] using Proof.Sha1.AArch64.Stream.Finalize.sat)

theorem compress :
    Verified AArch64.target Impl.Sha1.AArch64.compress (Spec.Sha1.compressContract AArch64.abi) :=
  compress_of Proof.Sha1.AArch64.compress_verified

/-- `update`: `updateScratch_of` with its working space in a frame of its own. -/
theorem update_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.updateAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 160 .x4 code)
      (Spec.Sha1.updateContract AArch64.abi (16 + 160)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 16) (bytes := 160)
    (updateScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize`: `finalizeScratch_of` with its working space in a frame of its own. -/
theorem finalize_of {code : Prog AArch64.isa}
    (hv : Verified AArch64.target code Proof.Sha1.finalizeAArch64) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 160 .x3 code)
      (Spec.Sha1.finalizeContract AArch64.abi (16 + 160)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 16) (bytes := 160)
    (finalizeScratch_of hv) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha1.AArch64.Shared
