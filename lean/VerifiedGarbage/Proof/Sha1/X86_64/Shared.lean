import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Sha1 on X86_64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha1/X86_64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha1/Contract.lean`, which the artifacts are emitted with.
`update` and `finalize` hold for any implementation `f` of the compression
function.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`), for an `f` that uses
no stack.
-/

namespace VG.Proof.Sha1.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sha1.X86_64.compress (Spec.Sha1.compressContract X86_64.abi) :=
  Proof.Sha1.X86_64.compress_verified.of_implies (by
    sig_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.satState] using Proof.Sha1.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Sha1.X86_64.Stream.init (Spec.Sha1.initContract X86_64.abi) :=
  Proof.Sha1.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.Stream.initSat] using Proof.Sha1.X86_64.Stream.initSat)

theorem compress_shani :
    Verified X86_64.target Impl.Sha1.X86_64.ShaNi.compress (Spec.Sha1.compressContract X86_64.abi) :=
  Proof.Sha1.X86_64.ShaNi.compress_verified.of_implies (by
    sig_implies [Spec.Sha1.compressContract, Spec.Sha1.compressSig,
      Proof.Sha1.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.satState] using Proof.Sha1.X86_64.satState)

theorem updateScratchImplies :
    Proof.Sha1.updateX86_64.Implies (Spec.Sha1.updateScratchContract X86_64.abi 8) := by
  sig_implies [Spec.Sha1.updateScratchContract, Spec.Sha1.updateScratchSig, Proof.Sha1.updateX86_64,
    X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Update.sat

theorem finalizeScratchImplies :
    Proof.Sha1.finalizeX86_64.Implies (Spec.Sha1.finalizeScratchContract X86_64.abi 8) := by
  sig_implies [Spec.Sha1.finalizeScratchContract, Spec.Sha1.finalizeScratchSig,
    Proof.Sha1.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Finalize.sat

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `updateScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem updateScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha1.X86_64.Stream.update f) (Spec.Sha1.updateScratchContract X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha1.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies updateScratchImplies

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha1.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha1.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `finalizeScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem finalizeScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha1.X86_64.Stream.finalize f)
      (Spec.Sha1.finalizeScratchContract X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha1.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies finalizeScratchImplies

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha1.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha1.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem update_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha1.X86_64.Stream.update f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha1.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha1.X86_64.Stream (Callee) in
theorem finalize_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha1.X86_64.Stream.finalize f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha1.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 168 .r8 (Impl.Sha1.X86_64.Stream.update f))
      (Spec.Sha1.updateContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 8) (bytes := 168)
    (updateScratch hf hm) (by decide) (by decide) (by decide) (update_spSafe hs) (update_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 168 .rcx (Impl.Sha1.X86_64.Stream.finalize f))
      (Spec.Sha1.finalizeContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 20) (stack := 8) (bytes := 168)
    (finalizeScratch hf hm) (by decide) (by decide) (by decide) (finalize_spSafe hs) (finalize_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha1.X86_64.Shared
