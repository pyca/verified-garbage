module

public import VerifiedGarbage.Proof.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
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

@[expose] public section

namespace VG.Proof.Sha1.X86_64.Shared

theorem init :
    Verified X86_64.target Impl.Sha1.X86_64.Stream.init (Spec.Sha1.initContract X86_64.abi) :=
  Proof.Sha1.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha1.initContract, Spec.Sha1.initSig, Proof.Sha1.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha1.X86_64.Stream.initSat] using Proof.Sha1.X86_64.Stream.initSat)

theorem updateScratchImplies :
    Proof.Sha1.updateX86_64.Implies (Proof.Sha1.updateScratchContract X86_64.abi 8) := by
  sig_implies [Proof.Sha1.updateScratchContract, Proof.Sha1.updateScratchSig, Proof.Sha1.updateX86_64,
    X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Update.sat

theorem finalizeScratchImplies :
    Proof.Sha1.finalizeX86_64.Implies (Proof.Sha1.finalizeScratchContract X86_64.abi 8) := by
  sig_implies [Proof.Sha1.finalizeScratchContract, Proof.Sha1.finalizeScratchSig,
    Proof.Sha1.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [Proof.Sha1.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha1.X86_64.Stream.params] using Proof.Sha1.X86_64.Stream.Finalize.sat

open VG.Impl.Sha1.X86_64.Stream (Callee) in
/-- `updateScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem updateScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha1.X86_64.Stream.update f) (Proof.Sha1.updateScratchContract X86_64.abi 8) :=
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
      (Proof.Sha1.finalizeScratchContract X86_64.abi 8) :=
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

/-! ## With no working space for the compression function

`update` and `finalize` made with none (`Stream.params0`), for an
implementation that uses none (`vg_sha1_compress_shani`): in a frame of 56
bytes, where the code made for every implementation takes 168. -/

section Zero

open VG.Impl.Sha1.X86_64.Stream (Callee)
open VG.Proof.Sha1.X86_64.Stream (params0)
open Impl.MdStream.X86_64 (updateBody updateTail compressN compressAt compressWith finalizeBody)

variable {f : Callee}

theorem update0_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.update params0 f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.allInstrs, hm,
    Bool.true_and]
  decide +kernel

theorem update0_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.update params0 f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.all, hs,
    Bool.true_and]
  decide +kernel

theorem update0_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.update params0 f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.x86_64Depth, hd]
  decide +kernel

theorem finalize0_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.finalize params0 f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.allInstrs, hm,
    Bool.true_and]
  decide +kernel

theorem finalize0_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.finalize params0 f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs, Bool.true_and]
  decide +kernel

theorem finalize0_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.finalize params0 f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.x86_64Depth, hd]
  decide +kernel

variable (hf : MdStream.X86_64.CalleeOk (P := params0) md f.code)
  (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
include hf hm

/-- `update` made with no working space for the compression function,
against the shared contract with the 6 words of working space it uses. -/
theorem updateScratch0 :
    Verified X86_64.target (Impl.MdStream.X86_64.update params0 f.name f.code)
      (Proof.Sha1.updateScratchContractW 6 X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Update.verified0 hf (update0_mxcsr hm)).of_implies (by
    sig_implies [Proof.Sha1.updateScratchContractW, Proof.Sha1.updateScratchSigW, Proof.Sha1.updateX86_64S,
      X86_64.abi, X86_64.argRegs]
      [MdStream.X86_64.Update.sat, Impl.Sha1.X86_64.Stream.params] using MdStream.X86_64.Update.sat params0)

/-- `finalize` made with no working space for the compression function, likewise. -/
theorem finalizeScratch0 :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize params0 f.name f.code)
      (Proof.Sha1.finalizeScratchContractW 6 X86_64.abi 8) :=
  (Proof.Sha1.X86_64.Stream.Finalize.verified0 hf (finalize0_mxcsr hm)).of_implies (by
    sig_implies [Proof.Sha1.finalizeScratchContractW, Proof.Sha1.finalizeScratchSigW,
      Proof.Sha1.finalizeX86_64S, X86_64.abi, X86_64.argRegs]
      [MdStream.X86_64.Finalize.sat, Impl.Sha1.X86_64.Stream.params] using MdStream.X86_64.Finalize.sat params0)

variable (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0)
include hs hd

/-- `update` made with no working space for the compression function, with
its working space in a frame of its own. -/
theorem update0 :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 56 .r8 (Impl.MdStream.X86_64.update params0 f.name f.code))
      (Spec.Sha1.updateContract X86_64.abi (8 + 56)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 6) (stack := 8) (bytes := 56)
    (updateScratch0 hf hm) (by decide) (by decide) (by decide) (update0_spSafe hs) (update0_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize` made with no working space for the compression function, likewise. -/
theorem finalize0 :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 56 .rcx (Impl.MdStream.X86_64.finalize params0 f.name f.code))
      (Spec.Sha1.finalizeContract X86_64.abi (8 + 56)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 6) (stack := 8) (bytes := 56)
    (finalizeScratch0 hf hm) (by decide) (by decide) (by decide) (finalize0_spSafe hs) (finalize0_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end Zero
end VG.Proof.Sha1.X86_64.Shared
