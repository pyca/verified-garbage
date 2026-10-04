import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Sha1.Arm.Compress
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# Sha1 on Arm: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha1/Arm/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha1/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sha1.Arm.Shared

theorem compress :
    Verified Arm.target Impl.Sha1.Arm.compress (Spec.Sha1.compressContract Arm.abi) :=
  Proof.Sha1.Arm.compress_verified.of_implies (by
    sig_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.satState)

theorem init : Verified Arm.target Impl.Sha1.Arm.Stream.init (Spec.Sha1.initContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.init_verified.of_implies (by
    sig_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.initSat)

theorem updateScratch :
    Verified Arm.target Impl.Sha1.Arm.Stream.update (Spec.Sha1.updateScratchContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Sha1.updateScratchContract, Spec.Sha1.updateScratchSig, Proof.Sha1.updateArm,
      Proof.Sha1.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Sha1.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.Update.sat)

theorem finalizeScratch :
    Verified Arm.target Impl.Sha1.Arm.Stream.finalize (Spec.Sha1.finalizeScratchContract Arm.abi) :=
  Proof.Sha1.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Sha1.finalizeScratchContract, Spec.Sha1.finalizeScratchSig,
      Proof.Sha1.finalizeArm, Proof.Sha1.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sha1.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Sha1.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha1.Arm.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { MdStream.Arm.Update.sat Impl.Sha1.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 84⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 176 2 Impl.Sha1.Arm.Stream.update)
    (Spec.Sha1.updateContract Arm.abi 176) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 0) (bytes := 176) (m := 2)
    updateScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha1.updatePost_local _)
    (by implies_sat [Spec.Sha1.updateContract, Spec.Sha1.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, MdStream.Arm.Update.sat, Impl.Sha1.Arm.Stream.params, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 84⟩, ⟨0x2000, 20⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 176 1 Impl.Sha1.Arm.Stream.finalize)
    (Spec.Sha1.finalizeContract Arm.abi 176) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 0) (bytes := 176) (m := 1)
    finalizeScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sha1.finalizePost_local _)
    (by implies_sat [Spec.Sha1.finalizeContract, Spec.Sha1.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Sha1.Arm.Shared
