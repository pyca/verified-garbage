module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
public import VerifiedGarbage.Proof.Rsa.X86.PrivBytes
public import VerifiedGarbage.Proof.Rsa.X86.PrivWorkspace
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract

/-! # Public decryption geometry, private-key sources and disjoint work buffers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def calleeBytes : Nat := 3372
def decryptStack : Nat := 3548

structure Geometry where
  stack : BitVec 32
  output : BitVec 32
  messageLength : BitVec 32
  workspace : BitVec 32
  sources : Fin 9 → BitVec 32
  length : Nat
  exponentLength : Nat
  privateLength : Nat
  pLength : Nat
  qLength : Nat
  scratchLength : Nat

namespace Geometry

def sourceLength (g : Geometry) (i : Fin 9) : Nat :=
  match i.val with
  | 1 => g.exponentLength | 2 => g.privateLength
  | 4 | 6 | 8 => g.pLength | 5 | 7 => g.qLength | _ => g.length

def sourceRegion (g : Geometry) (i : Fin 9) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def outputRegion (g : Geometry) : Region := ⟨byteAddr g.output, g.length⟩
def lengthRegion (g : Geometry) : Region := ⟨byteAddr g.messageLength, 8⟩
def workspaceRegion (g : Geometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : Geometry) : Region := ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes⟩
def savedRegion (g : Geometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes, 16⟩
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack calleeBytes
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20), 92⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - BitVec.ofNat 32 calleeBytes), decryptStack⟩
def scratch (g : Geometry) (d n : Nat) : Region := ⟨byteAddr g.workspace + BitVec.ofNat 64 d, n⟩

def argument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length | 2 => g.messageLength
  | 3 => g.sources 0 | 4 => BitVec.ofNat 32 g.length
  | 5 => g.sources 1 | 6 => BitVec.ofNat 32 g.exponentLength
  | 7 => g.sources 2 | 8 => BitVec.ofNat 32 g.privateLength
  | 9 => g.sources 3 | 10 => BitVec.ofNat 32 g.length
  | 11 => g.sources 4 | 12 => BitVec.ofNat 32 g.pLength
  | 13 => g.sources 5 | 14 => BitVec.ofNat 32 g.qLength
  | 15 => g.sources 6 | 16 => BitVec.ofNat 32 g.pLength
  | 17 => g.sources 7 | 18 => BitVec.ofNat 32 g.qLength
  | 19 => g.sources 8 | 20 => BitVec.ofNat 32 g.pLength
  | 21 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

structure Valid (g : Geometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  privatePositive : 0 < g.privateLength
  privateFits : g.privateLength ≤ g.length
  pPositive : 0 < g.pLength
  pShort : g.pLength < g.length
  qPositive : 0 < g.qLength
  qShort : g.qLength < g.length
  space : Spec.Rsa.scratchWords g.length ≤ g.scratchLength
  stackLow : calleeBytes ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92 ≤ 2 ^ 32
  outputFit : g.output.toNat + g.length ≤ 2 ^ 32
  lengthFit : g.messageLength.toNat + 8 ≤ 2 ^ 32
  sourceFits : ∀ i, (g.sources i).toNat + g.sourceLength i ≤ 2 ^ 32
  workspaceFit : g.workspace.toNat + 8 * g.scratchLength ≤ 2 ^ 32
  outputSources : ∀ i, g.outputRegion.Disjoint (g.sourceRegion i)
  lengthSources : ∀ i, g.lengthRegion.Disjoint (g.sourceRegion i)
  outputLength : g.outputRegion.Disjoint g.lengthRegion
  outputWorkspace : g.outputRegion.Disjoint g.workspaceRegion
  lengthWorkspace : g.lengthRegion.Disjoint g.workspaceRegion
  outputArguments : g.outputRegion.Disjoint g.argumentsRegion
  lengthArguments : g.lengthRegion.Disjoint g.argumentsRegion
  sourcesWorkspace : ∀ i, (g.sourceRegion i).Disjoint g.workspaceRegion
  workspaceArguments : g.workspaceRegion.Disjoint g.argumentsRegion
  stackOutput : g.wholeStack.Disjoint g.outputRegion
  stackLength : g.wholeStack.Disjoint g.lengthRegion
  stackSources : ∀ i, g.wholeStack.Disjoint (g.sourceRegion i)
  stackWorkspace : g.wholeStack.Disjoint g.workspaceRegion
  stackArguments : g.wholeStack.Disjoint g.argumentsRegion

end Geometry
end VG.Proof.RsaPkcs1Enc.X86.Dec
