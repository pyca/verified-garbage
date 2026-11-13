module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit

/-!
# Sha512 on X86_64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/X86_64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted with.
`update` and `finalize` hold for any implementation `f` of the compression
function.

The scalar compression function's own contract has less scratch than the
shared one; it is widened first (`Proof/Sha512/X86_64/Wide.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Shared

open _root_.VG.X86_64

/-- A state satisfying `updateX86_64.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86_64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeX86_64.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86_64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.init iv) (Spec.Sha512.initContract X86_64.abi iv) :=
  (Proof.Sha512.X86_64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.initSat] using Proof.Sha512.X86_64.Stream.initSat)

theorem updateScratchImplies :
    Proof.Sha512.updateX86_64.Implies (Proof.Sha512.updateScratchContract X86_64.abi 8) := by
  sig_implies [Proof.Sha512.updateScratchContract, Proof.Sha512.updateScratchSig,
    Proof.Sha512.updateX86_64, X86_64.abi, X86_64.argRegs]
    [updateSat, Proof.Sha512.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha512.X86_64.Stream.params] using updateSat

theorem finalizeScratchImplies :
    Proof.Sha512.finalizeX86_64.Implies (Proof.Sha512.finalizeScratchContract X86_64.abi 8) := by
  sig_implies [Proof.Sha512.finalizeScratchContract, Proof.Sha512.finalizeScratchSig,
    Proof.Sha512.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeSat, Proof.Sha512.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha512.X86_64.Stream.params] using finalizeSat

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `updateScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem updateScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update f)
      (Proof.Sha512.updateScratchContract X86_64.abi 8) :=
  (Proof.Sha512.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha512.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies updateScratchImplies

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha512.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha512.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `finalizeScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem finalizeScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalize f)
      (Proof.Sha512.finalizeScratchContract X86_64.abi 8) :=
  (Proof.Sha512.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha512.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies finalizeScratchImplies

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha512.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha512.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem update_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha512.X86_64.Stream.update f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha512.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem finalize_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha512.X86_64.Stream.finalize f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha512.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1384 .r8 (Impl.Sha512.X86_64.Stream.update f))
      (Spec.Sha512.updateContract X86_64.abi (8 + 1384)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 8) (bytes := 1384)
    (updateScratch hf hm) (by decide) (by decide) (by decide) (update_spSafe hs) (update_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1384 .rcx (Impl.Sha512.X86_64.Stream.finalize f))
      (Spec.Sha512.finalizeContract X86_64.abi (8 + 1384)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 8) (bytes := 1384)
    (finalizeScratch hf hm) (by decide) (by decide) (by decide) (finalize_spSafe hs) (finalize_depth hd)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sha512.X86_64.Shared

/-! ## The truncated digests

`finalizeDigest` (SHA-384's, SHA-512/256's and SHA-512/224's `finalize`)
takes its working space in `scratch`, as `finalizeScratchSig` does; with it
in a frame of its own, it is `Spec.Sha512.finalizeDigestContract`. -/

namespace VG.Proof.Sha512.X86_64.Shared

open _root_.VG.X86_64
open VG.Impl.Sha512.X86_64.Stream (Callee params params384 params512_256 params512_224 finalizeDigest)

/-- A state satisfying `finalizeDigestX86_64.pre`. -/
def finalizeDigestSat (D : Nat) : State :=
  { Proof.Sha512.X86_64.Stream.Finalize.satD D with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 1376⟩] }

theorem finalizeDigestScratchImplies48 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (Stream.finalizeDigestX86_64 iv 48 digest).Implies (finalizeDigestScratchContract X86_64.abi iv 48 digest 8) := by
  sig_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig, Spec.Sha512.finalizeDigestPost,
    Stream.finalizeDigestX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeDigestSat, Proof.Sha512.X86_64.Stream.Finalize.satD,
      MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSat 48

theorem finalizeDigestScratchImplies32 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (Stream.finalizeDigestX86_64 iv 32 digest).Implies (finalizeDigestScratchContract X86_64.abi iv 32 digest 8) := by
  sig_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig, Spec.Sha512.finalizeDigestPost,
    Stream.finalizeDigestX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeDigestSat, Proof.Sha512.X86_64.Stream.Finalize.satD,
      MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSat 32

theorem finalizeDigestScratchImplies28 (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) :
    (Stream.finalizeDigestX86_64 iv 28 digest).Implies (finalizeDigestScratchContract X86_64.abi iv 28 digest 8) := by
  sig_implies [Proof.Sha512.finalizeDigestScratchContract, Proof.Sha512.finalizeDigestScratchSig, Spec.Sha512.finalizeDigestPost,
    Stream.finalizeDigestX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeDigestSat, Proof.Sha512.X86_64.Stream.Finalize.satD,
      MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSat 28

theorem finalizeDigestScratchImplies (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) {D : Nat}
    (hD : D = 48 ∨ D = 32 ∨ D = 28) :
    (Stream.finalizeDigestX86_64 iv D digest).Implies (finalizeDigestScratchContract X86_64.abi iv D digest 8) := by
  rcases hD with rfl | rfl | rfl
  exacts [finalizeDigestScratchImplies48 iv digest, finalizeDigestScratchImplies32 iv digest,
    finalizeDigestScratchImplies28 iv digest]

/-- What the generic proofs need of SHA-384's, SHA-512/256's and
SHA-512/224's `finalizeDigest`, whose digest `o` writes the first `D` bytes
of the final hash value, from one check of each. -/
structure DigestCode (o : List Instr) (D : Nat) : Prop where
  shape : MdStream.X86_64.ShapeD (P := { params with out := o }) md D
  taints : MdStream.X86_64.Taints { params with out := o }
  hD : D = 48 ∨ D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true →
    (finalizeDigest { params with out := o } f).allInstrs (fun i => !X86_64.loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !X86_64.isa.writesSp i) = true →
    (finalizeDigest { params with out := o } f).all (fun i => !X86_64.isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 → (finalizeDigest { params with out := o } f).x86_64Depth ≤ 8

/-- `finalizeDigest` of a `D`-byte `digest` of the messages hashed from
`iv`, with its working space in `scratch`. -/
theorem finalizeDigestScratch {o : List Instr} {D : Nat} (c : DigestCode o D)
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m)
    {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (finalizeDigest { params with out := o } f)
      (finalizeDigestScratchContract X86_64.abi iv D digest 8) :=
  (Stream.Finalize.verifiedDigest c.shape c.taints hdg hf (c.mxcsr f hm)).of_implies
    (finalizeDigestScratchImplies iv digest c.hD)

/-- `finalizeDigest`, with its working space in a frame of its own. -/
theorem finalizeDigestStack {o : List Instr} {D : Nat} (c : DigestCode o D)
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m)
    {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1384 .rcx (finalizeDigest { params with out := o } f))
      (Spec.Sha512.finalizeDigestContract X86_64.abi iv D digest (8 + 1384)) := by
  have h := finalizeDigestScratch c hdg hf hm
  have hsp := c.spSafe f hs
  have hdp := c.depth f hd
  rcases c.hD with rfl | rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 172) (stack := 8) (bytes := 1384)
    h (by decide) (by decide) (by decide) hsp hdp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem digest384 : DigestCode (Impl.MdStream.X86_64.out64 6) 48 where
  shape := Stream.shape384
  taints := Stream.taints384
  hD := .inl rfl
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, hm, Bool.true_and]
    decide +kernel
  spSafe f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, h, Bool.true_and]
    decide +kernel
  depth f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.x86_64Depth, h]
    decide +kernel

theorem digest512_256 : DigestCode (Impl.MdStream.X86_64.out64 4) 32 where
  shape := Stream.shape512_256
  taints := Stream.taints512_256
  hD := .inr (.inl rfl)
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, hm, Bool.true_and]
    decide +kernel
  spSafe f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, h, Bool.true_and]
    decide +kernel
  depth f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.x86_64Depth, h]
    decide +kernel

theorem digest512_224 : DigestCode (Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) 28 where
  shape := Stream.shape512_224
  taints := Stream.taints512_224
  hD := .inr (.inr rfl)
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, hm, Bool.true_and]
    decide +kernel
  spSafe f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, h, Bool.true_and]
    decide +kernel
  depth f h := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
      Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.x86_64Depth, h]
    decide +kernel

/-! ## With the working space the compression function uses

`update`, `finalize` and `finalizeDigest` made with `so` bytes of working
space for the compression function (`Stream.paramsS`), for an implementation
that uses no more than that (`Proof.Sha512.compressWideX86_64S so`): in a
frame of `so + 56` bytes, where the code made for every implementation
(`Stream.params`) takes 1384. -/

section S

open VG.Proof.Sha512.X86_64.Stream (paramsS)
open Impl.MdStream.X86_64 (updateBody updateTail compressN compressAt compressWith finalizeBody)

variable {so : Nat} (h : so = 0 ∨ so = 192) {f : Callee}
include h

theorem updateS_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.allInstrs, hm,
    Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem updateS_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.all, hs,
    Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem updateS_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.x86_64Depth, hd]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.allInstrs, hm,
    Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.x86_64Depth, hd]
  rcases h with rfl | rfl <;> decide +kernel

variable (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
  (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
  (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
include hf hv hm

/-- `update` made with `so` bytes for the compression function, against the
shared contract with the `so / 8 + 6` words of working space it uses. -/
theorem updateScratchS :
    Verified X86_64.target (Impl.MdStream.X86_64.update (paramsS so) f.name f.code)
      (Proof.Sha512.updateScratchContractW (so / 8 + 6) X86_64.abi 8) := by
  have v := Proof.Sha512.X86_64.Stream.Update.verifiedS h hf hv (updateS_mxcsr h hm)
  rcases h with rfl | rfl
  · exact v.of_implies (by
      sig_implies [Proof.Sha512.updateScratchContractW, Proof.Sha512.updateScratchSigW,
        Proof.Sha512.updateX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Update.sat, Impl.Sha512.X86_64.Stream.params] using MdStream.X86_64.Update.sat (paramsS 0))
  · exact v.of_implies (by
      sig_implies [Proof.Sha512.updateScratchContractW, Proof.Sha512.updateScratchSigW,
        Proof.Sha512.updateX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Update.sat, Impl.Sha512.X86_64.Stream.params] using MdStream.X86_64.Update.sat (paramsS 192))

/-- `finalize` made with `so` bytes for the compression function, likewise. -/
theorem finalizeScratchS :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code)
      (Proof.Sha512.finalizeScratchContractW (so / 8 + 6) X86_64.abi 8) := by
  have v := Proof.Sha512.X86_64.Stream.Finalize.verifiedS h hf hv (finalizeS_mxcsr h hm)
  rcases h with rfl | rfl
  · exact v.of_implies (by
      sig_implies [Proof.Sha512.finalizeScratchContractW, Proof.Sha512.finalizeScratchSigW,
        Proof.Sha512.finalizeX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.sat, Impl.Sha512.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.sat (paramsS 0))
  · exact v.of_implies (by
      sig_implies [Proof.Sha512.finalizeScratchContractW, Proof.Sha512.finalizeScratchSigW,
        Proof.Sha512.finalizeX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.sat, Impl.Sha512.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.sat (paramsS 192))

variable (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0)
include hs hd

/-- `update` made with `so` bytes for the compression function, with its
working space in a frame of its own. -/
theorem updateS :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .r8 (Impl.MdStream.X86_64.update (paramsS so) f.name f.code))
      (Spec.Sha512.updateContract X86_64.abi (8 + (so + 56))) := by
  have v := updateScratchS h hf hv hm
  have sp := updateS_spSafe h hs
  have dp := updateS_depth h hd
  rcases h with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    v (by decide) (by decide) (by decide) sp dp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize` made with `so` bytes for the compression function, likewise. -/
theorem finalizeS :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code))
      (Spec.Sha512.finalizeContract X86_64.abi (8 + (so + 56))) := by
  have v := finalizeScratchS h hf hv hm
  have sp := finalizeS_spSafe h hs
  have dp := finalizeS_depth h hd
  rcases h with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    v (by decide) (by decide) (by decide) sp dp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end S

/-! ### The truncated digests, likewise -/

section S

open VG.Proof.Sha512.X86_64.Stream (paramsS)
open Impl.MdStream.X86_64 (compressAt compressWith finalizeBody)

/-- A state satisfying `finalizeDigestX86_64S`'s precondition. -/
def finalizeDigestSatS (so D : Nat) : State :=
  { Proof.Sha512.X86_64.Stream.Finalize.satD D with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, so + 48⟩] }

theorem finalizeDigestScratchImpliesS (iv : Spec.Sha512.HashValue) (digest : List Byte → List Byte) {so D : Nat}
    (h : so = 0 ∨ so = 192) (hD : D = 48 ∨ D = 32 ∨ D = 28) :
    (Stream.finalizeDigestX86_64S iv D digest (so + 48)).Implies
      (Proof.Sha512.finalizeDigestScratchContractW (so / 8 + 6) X86_64.abi iv D digest 8) := by
  rcases h with rfl | rfl <;> rcases hD with rfl | rfl | rfl
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 0 48
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 0 32
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 0 28
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 192 48
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 192 32
  · sig_implies [Proof.Sha512.finalizeDigestScratchContractW, Proof.Sha512.finalizeDigestScratchSigW,
      Spec.Sha512.finalizeDigestPost, Stream.finalizeDigestX86_64S, X86_64.abi, X86_64.argRegs]
      [finalizeDigestSatS, Proof.Sha512.X86_64.Stream.Finalize.satD,
        MdStream.X86_64.Finalize.satD, Impl.Sha512.X86_64.Stream.params] using finalizeDigestSatS 192 28

/-- `DigestCode`, made with `so` bytes for the compression function. -/
structure DigestCodeS (so : Nat) (o : List Instr) (D : Nat) : Prop where
  shape : MdStream.X86_64.ShapeD (P := { paramsS so with out := o }) md D
  taints : MdStream.X86_64.Taints { paramsS so with out := o }
  hso : so = 0 ∨ so = 192
  hD : D = 48 ∨ D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true →
    (finalizeDigest { paramsS so with out := o } f).allInstrs (fun i => !X86_64.loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !X86_64.isa.writesSp i) = true →
    (finalizeDigest { paramsS so with out := o } f).all (fun i => !X86_64.isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 → (finalizeDigest { paramsS so with out := o } f).x86_64Depth ≤ 8

/-- `finalizeDigestStack`, made with `so` bytes for the compression function:
in a frame of `so + 56` bytes. -/
theorem finalizeDigestStackS {so : Nat} {o : List Instr} {D : Nat} (c : DigestCodeS so o D)
    {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m)
    {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx (finalizeDigest { paramsS so with out := o } f))
      (Spec.Sha512.finalizeDigestContract X86_64.abi iv D digest (8 + (so + 56))) := by
  have h := (Stream.Finalize.verifiedDigestS c.hso c.shape c.taints hdg hf hv (c.mxcsr f hm)).of_implies
    (finalizeDigestScratchImpliesS iv digest c.hso c.hD)
  have hsp := c.spSafe f hs
  have hdp := c.depth f hd
  rcases c.hso with rfl | rfl <;> rcases c.hD with rfl | rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    h (by decide) (by decide) (by decide) hsp hdp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem digest384S {so : Nat} (h : so = 0 ∨ so = 192) : DigestCodeS so (Impl.MdStream.X86_64.out64 6) 48 where
  shape := Stream.shape384S so
  taints := Stream.taints384S h
  hso := h
  hD := .inl rfl
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.allInstrs, hm, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs,
      Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem digest512_256S {so : Nat} (h : so = 0 ∨ so = 192) : DigestCodeS so (Impl.MdStream.X86_64.out64 4) 32 where
  shape := Stream.shape512_256S so
  taints := Stream.taints512_256S h
  hso := h
  hD := .inr (.inl rfl)
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.allInstrs, hm, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs,
      Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem digest512_224S {so : Nat} (h : so = 0 ∨ so = 192) :
    DigestCodeS so (Impl.MdStream.X86_64.out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) 28 where
  shape := Stream.shape512_224S so
  taints := Stream.taints512_224S h
  hso := h
  hD := .inr (.inr rfl)
  mxcsr f hm := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.allInstrs, hm, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs,
      Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [finalizeDigest, Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith,
      Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

end S

end VG.Proof.Sha512.X86_64.Shared
