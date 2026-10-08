import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

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

namespace VG.Proof.Sha512.X86_64.Shared

open _root_.VG.X86_64

/-- A state satisfying `updateX86_64.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86_64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeX86_64.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86_64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compressImplies :
    Proof.Sha512.compressWideX86_64.Implies (Spec.Sha512.compressContract X86_64.abi) := by
  sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, Proof.Sha512.compressWideX86_64,
    Proof.Sha512.compressX86_64, X86_64.abi, X86_64.argRegs]
    [Proof.Sha512.X86_64.wideSat, Proof.Sha512.X86_64.satState] using Proof.Sha512.X86_64.wideSat

theorem compress :
    Verified X86_64.target Impl.Sha512.X86_64.compress (Spec.Sha512.compressContract X86_64.abi) :=
  Proof.Sha512.X86_64.compressWide_verified.of_implies compressImplies

theorem compress_avx2 :
    Verified X86_64.target Impl.Sha512.X86_64.Avx2.compress (Spec.Sha512.compressContract X86_64.abi) :=
  Proof.Sha512.X86_64.Avx2.compress_verified.of_implies compressImplies

theorem compress_shani :
    Verified X86_64.target Impl.Sha512.X86_64.ShaNi.compress (Spec.Sha512.compressContract X86_64.abi) :=
  Proof.Sha512.X86_64.ShaNi.compressWide_verified.of_implies compressImplies

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.init iv) (Spec.Sha512.initContract X86_64.abi iv) :=
  (Proof.Sha512.X86_64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.initSat] using Proof.Sha512.X86_64.Stream.initSat)

theorem updateScratchImplies :
    Proof.Sha512.updateX86_64.Implies (Spec.Sha512.updateScratchContract X86_64.abi 8) := by
  sig_implies [Spec.Sha512.updateScratchContract, Spec.Sha512.updateScratchSig,
    Proof.Sha512.updateX86_64, X86_64.abi, X86_64.argRegs]
    [updateSat, Proof.Sha512.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha512.X86_64.Stream.params] using updateSat

theorem finalizeScratchImplies :
    Proof.Sha512.finalizeX86_64.Implies (Spec.Sha512.finalizeScratchContract X86_64.abi 8) := by
  sig_implies [Spec.Sha512.finalizeScratchContract, Spec.Sha512.finalizeScratchSig,
    Proof.Sha512.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeSat, Proof.Sha512.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha512.X86_64.Stream.params] using finalizeSat

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `updateScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem updateScratch {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update f)
      (Spec.Sha512.updateScratchContract X86_64.abi 8) :=
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
      (Spec.Sha512.finalizeScratchContract X86_64.abi 8) :=
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

end VG.Proof.Sha512.X86_64.Shared
