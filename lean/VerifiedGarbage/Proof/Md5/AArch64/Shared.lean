import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Md5.AArch64.Compress
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Init
import VerifiedGarbage.Proof.Md5.AArch64.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# Md5 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/AArch64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Md5.AArch64.Shared

theorem compress :
    Verified AArch64.target Impl.Md5.AArch64.compress (Spec.Md5.compressContract AArch64.abi) :=
  Proof.Md5.AArch64.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.satState] using Proof.Md5.AArch64.satState)

theorem init :
    Verified AArch64.target Impl.Md5.AArch64.Stream.init (Spec.Md5.initContract AArch64.abi) :=
  Proof.Md5.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.initSat] using Proof.Md5.AArch64.Stream.initSat)

theorem updateScratch :
    Verified AArch64.target Impl.Md5.AArch64.Stream.update (Spec.Md5.updateScratchContract AArch64.abi 16) :=
  Proof.Md5.AArch64.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Md5.updateScratchContract, Spec.Md5.updateScratchSig, Proof.Md5.updateAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Md5.AArch64.Stream.params] using Proof.Md5.AArch64.Stream.Update.sat)

theorem finalizeScratch :
    Verified AArch64.target Impl.Md5.AArch64.Stream.finalize (Spec.Md5.finalizeScratchContract AArch64.abi 16) :=
  Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Spec.Md5.finalizeScratchContract, Spec.Md5.finalizeScratchSig,
      Proof.Md5.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Md5.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Md5.AArch64.Stream.params] using Proof.Md5.AArch64.Stream.Finalize.sat)

theorem update : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Md5.AArch64.Stream.update)
    (Spec.Md5.updateContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    updateScratch (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Md5.AArch64.Stream.finalize)
    (Spec.Md5.finalizeContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    finalizeScratch (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Md5.AArch64.Shared
