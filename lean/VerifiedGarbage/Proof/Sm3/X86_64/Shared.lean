import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm3.X86_64.Compress
import VerifiedGarbage.Proof.Sm3.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sm3.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# SM3 on x86-64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/X86_64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space (78 words: the compression
function's 576 bytes, then our caller's callee-saved registers) in a frame of
their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sm3.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sm3.X86_64.compress (Spec.Sm3.compressContract X86_64.abi) :=
  Proof.Sm3.X86_64.compress_verified.of_implies (by
    sig_implies [Spec.Sm3.compressContract, Spec.Sm3.compressSig,
      Proof.Sm3.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.satState] using Proof.Sm3.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.init (Spec.Sm3.initContract X86_64.abi) :=
  Proof.Sm3.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.initSat] using Proof.Sm3.X86_64.Stream.initSat)

theorem updateScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.update (Proof.Sm3.updateScratchContract X86_64.abi 78 8) :=
  Proof.Sm3.X86_64.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Update.sat)

theorem finalizeScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.finalize (Proof.Sm3.finalizeScratchContract X86_64.abi 78 8) :=
  Proof.Sm3.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Finalize.sat)

theorem update : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 632 .r8 Impl.Sm3.X86_64.Stream.update)
    (Spec.Sm3.updateContract X86_64.abi (8 + 632)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 78)
    (stack := 8) (bytes := 632)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (by decide) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 632 .rcx Impl.Sm3.X86_64.Stream.finalize)
    (Spec.Sm3.finalizeContract X86_64.abi (8 + 632)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 78)
    (stack := 8) (bytes := 632)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (by decide) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.X86_64.Shared
