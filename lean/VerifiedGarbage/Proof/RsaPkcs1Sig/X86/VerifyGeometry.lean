module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public buffers and the two encoding buffers used by i686 verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

def verifyStack : Nat := 2152

structure Geometry where
  stack : BitVec 32
  workspace : BitVec 32
  sources : Fin 5 → BitVec 32
  length : Nat
  hash : BitVec 32
  exponentLength : Nat
  digestLength : Nat
  signatureLength : Nat
  preLength : Nat
  scratchLength : Nat

namespace Geometry

def sourceLength (g : Geometry) (i : Fin 5) : Nat :=
  match i.val with
  | 1 => g.exponentLength
  | 2 => g.digestLength
  | 3 => g.signatureLength
  | 4 => 8 * g.preLength
  | _ => g.length

def sourceRegion (g : Geometry) (i : Fin 5) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def workspaceRegion (g : Geometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : Geometry) : Region := ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩
def savedRegion (g : Geometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes, 16⟩
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack 24
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20), 52⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - 24), verifyStack⟩
def em1 (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 em1Offset
def em2 (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 em2Offset

def argument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.sources 0 | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 1 | 3 => BitVec.ofNat 32 g.exponentLength
  | 4 => g.hash | 5 => g.sources 2 | 6 => BitVec.ofNat 32 g.digestLength
  | 7 => g.sources 3 | 8 => BitVec.ofNat 32 g.signatureLength
  | 9 => g.workspace | 10 => BitVec.ofNat 32 g.scratchLength
  | 11 => g.sources 4 | _ => BitVec.ofNat 32 g.preLength

structure Valid (g : Geometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  digestBound : g.digestLength < 2 ^ 32
  signatureBound : g.signatureLength < 2 ^ 32
  precomputed : g.preLength = Spec.Rsa.precomputedWords g.length
  space : Spec.Rsa.publicScratchWords g.length ≤ g.scratchLength
  stackLow : 24 ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52 ≤ 2 ^ 32
  sourceFits : ∀ i, (g.sources i).toNat + g.sourceLength i ≤ 2 ^ 32
  workspaceFit : g.workspace.toNat + 8 * g.scratchLength ≤ 2 ^ 32
  sourcesWorkspace : ∀ i, (g.sourceRegion i).Disjoint g.workspaceRegion
  workspaceArguments : g.workspaceRegion.Disjoint g.argumentsRegion
  stackSources : ∀ i, g.wholeStack.Disjoint (g.sourceRegion i)
  stackWorkspace : g.wholeStack.Disjoint g.workspaceRegion
  stackArguments : g.wholeStack.Disjoint g.argumentsRegion

end Geometry
end VG.Proof.RsaPkcs1Sig.X86.Ver
