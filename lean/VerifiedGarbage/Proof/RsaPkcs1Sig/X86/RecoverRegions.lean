module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `RsaPkcs1Sig.X86.RecoverGeometry`, which this module and modules that import it used -/

section

/-! # Public buffers and the two encoding buffers used by i686 verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

def recoverStack : Nat := 2228

structure Geometry where
  stack : BitVec 32
  output : BitVec 32
  outputLength : Nat
  workspace : BitVec 32
  sources : Fin 4 → BitVec 32
  length : Nat
  hash : BitVec 32
  exponentLength : Nat
  signatureLength : Nat
  preLength : Nat
  scratchLength : Nat

namespace Geometry

def sourceLength (g : Geometry) (i : Fin 4) : Nat :=
  match i.val with
  | 1 => g.exponentLength
  | 2 => g.signatureLength
  | 3 => 8 * g.preLength
  | _ => g.length

def sourceRegion (g : Geometry) (i : Fin 4) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def outputRegion (g : Geometry) : Region := ⟨byteAddr g.output, g.outputLength⟩
def workspaceRegion (g : Geometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : Geometry) : Region := ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩
def savedRegion (g : Geometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes, 16⟩
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack 100
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20), 52⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - 100), recoverStack⟩
def em1 (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 em1Offset
def em2 (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 em2Offset

def argument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.outputLength
  | 2 => g.sources 0 | 3 => BitVec.ofNat 32 g.length
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.hash | 7 => g.sources 2 | 8 => BitVec.ofNat 32 g.signatureLength
  | 9 => g.workspace | 10 => BitVec.ofNat 32 g.scratchLength
  | 11 => g.sources 3 | _ => BitVec.ofNat 32 g.preLength

structure Valid (g : Geometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  hashValid : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat = some h ∧ g.outputLength = h.len
  signatureBound : g.signatureLength < 2 ^ 32
  precomputed : g.preLength = Spec.Rsa.precomputedWords g.length
  space : Spec.Rsa.publicScratchWords g.length ≤ g.scratchLength
  stackLow : 100 ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52 ≤ 2 ^ 32
  outputFit : g.output.toNat + g.outputLength ≤ 2 ^ 32
  outputSources : ∀ i, g.outputRegion.Disjoint (g.sourceRegion i)
  outputWorkspace : g.outputRegion.Disjoint g.workspaceRegion
  outputArguments : g.outputRegion.Disjoint g.argumentsRegion
  stackOutput : g.wholeStack.Disjoint g.outputRegion
  sourceFits : ∀ i, (g.sources i).toNat + g.sourceLength i ≤ 2 ^ 32
  workspaceFit : g.workspace.toNat + 8 * g.scratchLength ≤ 2 ^ 32
  sourcesWorkspace : ∀ i, (g.sourceRegion i).Disjoint g.workspaceRegion
  workspaceArguments : g.workspaceRegion.Disjoint g.argumentsRegion
  stackSources : ∀ i, g.wholeStack.Disjoint (g.sourceRegion i)
  stackWorkspace : g.wholeStack.Disjoint g.workspaceRegion
  stackArguments : g.wholeStack.Disjoint g.argumentsRegion

end Geometry
end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Disjoint wrapper, callee, saved-register, and argument stack regions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
namespace Geometry

theorem Valid.stackBase {g : Geometry} (h : g.Valid) :
    byteAddr g.stack = byteAddr (g.stack - BitVec.ofNat 32 100) + BitVec.ofNat 64 100 := by
  change g.stack.setWidth 64 = (g.stack - BitVec.ofNat 32 100).setWidth 64 + BitVec.ofNat 64 100
  rw [VG.X86.Taint.sub_setWidth h.stackLow]
  exact (BitVec.sub_add_cancel _ _).symm

theorem Valid.innerSub {g : Geometry} (h : g.Valid) : g.innerRegion.Sub g.wholeStack := by
  unfold innerRegion wholeStack
  rw [h.stackBase]
  exact Offset.sub_base _ (by decide : 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ recoverStack)

theorem Valid.savedSub {g : Geometry} (h : g.Valid) : g.savedRegion.Sub g.wholeStack := by
  unfold savedRegion wholeStack
  rw [h.stackBase, Offset.add_add]
  exact Offset.sub_base _ (by decide : (100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) + 16 ≤ recoverStack)

theorem Valid.calleeSub {g : Geometry} (_h : g.Valid) : g.calleeRegion.Sub g.wholeStack :=
  Region.sub_prefix (by decide : 100 ≤ recoverStack)

theorem Valid.calleeInner {g : Geometry} (h : g.Valid) : g.calleeRegion.Disjoint g.innerRegion := by
  unfold calleeRegion VG.X86.below innerRegion
  rw [h.stackBase]
  exact (Offset.disjoint_base _ (by decide : 100 ≤ 100) (by decide : 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ 2 ^ 64)).symm

theorem Valid.innerSaved {g : Geometry} (_h : g.Valid) : g.innerRegion.Disjoint g.savedRegion :=
  (Offset.disjoint_base _ (by decide : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) (by decide : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 16 ≤ 2 ^ 64)).symm

theorem Valid.offsetAddr {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52) :
    byteAddr (g.stack + BitVec.ofNat 32 d) = byteAddr g.stack + BitVec.ofNat 64 d :=
  byteAddr_add (by have := h.stackHigh; omega_using [fit, this])

theorem Valid.offsetNat {g : Geometry} (h : g.Valid) {d : Nat} (fit : d < VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52) :
    (g.stack + BitVec.ofNat 32 d).toNat = g.stack.toNat + d := by
  have sum : g.stack.toNat + d < 2 ^ 32 := by have := h.stackHigh; omega_using [fit, this]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [sum] : d < 2 ^ 32), Nat.mod_eq_of_lt sum]

theorem Valid.encodingFit {g : Geometry} (h : g.Valid) {d : Nat} (hd : d + g.length ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) :
    (g.stack + BitVec.ofNat 32 d).toNat + g.length ≤ 2 ^ 32 := by
  rw [h.offsetNat (by omega_using [hd])]
  have := h.stackHigh
  omega_using [hd, this]

end Geometry
end VG.Proof.RsaPkcs1Sig.X86.Rcv
