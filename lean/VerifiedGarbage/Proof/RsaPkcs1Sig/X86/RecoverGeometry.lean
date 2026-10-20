module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Spec.Rsa.Contract


/-! # Public buffers and the two encoding buffers used by i686 verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

def recoverStack : Nat := 2152

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
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack 24
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20), 52⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - 24), recoverStack⟩
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
  stackLow : 24 ≤ g.stack.toNat
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
