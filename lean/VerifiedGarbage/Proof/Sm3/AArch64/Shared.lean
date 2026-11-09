module

public import VerifiedGarbage.Proof.Sm3.AArch64.Compress
import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm3.AArch64.Stream
import VerifiedGarbage.Proof.Sm3.AArch64.Lit

/-!
# SM3 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/AArch64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space (14 words: the compression
function's 64 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Shared

open _root_.VG.AArch64

theorem init :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.init (Spec.Sm3.initContract AArch64.abi) :=
  Proof.Sm3.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.initSat] using Proof.Sm3.AArch64.Stream.initSat)

theorem updateScratch :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.update (Proof.Sm3.updateScratchContract AArch64.abi 14 16) :=
  Proof.Sm3.AArch64.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Update.sat)

theorem finalizeScratch :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.finalize (Proof.Sm3.finalizeScratchContract AArch64.abi 14 16) :=
  Proof.Sm3.AArch64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Finalize.sat)

theorem update : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Sm3.AArch64.Stream.update)
    (Spec.Sm3.updateContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Sm3.AArch64.Stream.finalize)
    (Spec.Sm3.finalizeContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.AArch64.Shared
