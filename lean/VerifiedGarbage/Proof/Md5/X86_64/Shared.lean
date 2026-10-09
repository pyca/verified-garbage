module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Md5.X86_64.Compress
public import VerifiedGarbage.Proof.Md5.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
public import VerifiedGarbage.Spec.Md5.Contract
public import VerifiedGarbage.Proof.Md5.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# MD5 on x86-64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/X86_64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section


namespace VG.Proof.Md5.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Md5.X86_64.compress (Spec.Md5.compressContract X86_64.abi) :=
  Proof.Md5.X86_64.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.satState] using Proof.Md5.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Md5.X86_64.Stream.init (Spec.Md5.initContract X86_64.abi) :=
  Proof.Md5.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.Stream.initSat] using Proof.Md5.X86_64.Stream.initSat)

theorem updateScratch :
    Verified X86_64.target Impl.Md5.X86_64.Stream.update (Spec.Md5.updateScratchContract X86_64.abi 8) :=
  Proof.Md5.X86_64.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Md5.updateScratchContract, Spec.Md5.updateScratchSig, Proof.Md5.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Md5.X86_64.Stream.params] using Proof.Md5.X86_64.Stream.Update.sat)

theorem finalizeScratch :
    Verified X86_64.target Impl.Md5.X86_64.Stream.finalize (Spec.Md5.finalizeScratchContract X86_64.abi 8) :=
  Proof.Md5.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Spec.Md5.finalizeScratchContract, Spec.Md5.finalizeScratchSig,
      Proof.Md5.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Md5.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Md5.X86_64.Stream.params] using Proof.Md5.X86_64.Stream.Finalize.sat)

theorem update : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 120 .r8 Impl.Md5.X86_64.Stream.update)
    (Spec.Md5.updateContract X86_64.abi (8 + 120)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 8) (bytes := 120)
    updateScratch (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 120 .rcx Impl.Md5.X86_64.Stream.finalize)
    (Spec.Md5.finalizeContract X86_64.abi (8 + 120)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 8) (bytes := 120)
    finalizeScratch (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Md5.X86_64.Shared
