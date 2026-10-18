module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encrypt
public import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
public import VerifiedGarbage.Proof.Rsa.X86.PrivBytes
public import VerifiedGarbage.Proof.Rsa.X86.PrivWorkspace
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Precomputed

/-! # Public encryption geometry and the isolated encoded-message frame -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Enc.X86.Encrypt

def calleeBytes : Nat := 24
def encryptStack : Nat := 1128

structure Geometry where
  stack : BitVec 32
  output : BitVec 32
  workspace : BitVec 32
  sources : Fin 5 → BitVec 32
  length : Nat
  exponentLength : Nat
  messageLength : Nat
  paddingLength : Nat
  preLength : Nat
  scratchLength : Nat

namespace Geometry

def sourceLength (g : Geometry) (i : Fin 5) : Nat :=
  match i.val with
  | 1 => g.exponentLength | 2 => g.messageLength | 3 => g.paddingLength | 4 => 8 * g.preLength | _ => g.length

def sourceRegion (g : Geometry) (i : Fin 5) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def outputRegion (g : Geometry) : Region := ⟨byteAddr g.output, g.length⟩
def workspaceRegion (g : Geometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : Geometry) : Region := ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes⟩
def savedRegion (g : Geometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes, 16⟩
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack 24
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20), 56⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - 24), encryptStack⟩
def temporary (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 emOffset

def argument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 0 | 3 => BitVec.ofNat 32 g.length
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.sources 2 | 7 => BitVec.ofNat 32 g.messageLength
  | 8 => g.sources 3 | 9 => BitVec.ofNat 32 g.paddingLength
  | 10 => g.workspace | 11 => BitVec.ofNat 32 g.scratchLength
  | 12 => g.sources 4 | _ => BitVec.ofNat 32 g.preLength

structure Valid (g : Geometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  messageFits : g.messageLength + 11 ≤ g.length
  padding : g.paddingLength = g.length - g.messageLength - 3
  precomputed : g.preLength = Spec.Rsa.precomputedWords g.length
  space : Spec.Rsa.publicScratchWords g.length ≤ g.scratchLength
  stackLow : 24 ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 56 ≤ 2 ^ 32
  outputFit : g.output.toNat + g.length ≤ 2 ^ 32
  sourceFits : ∀ i, (g.sources i).toNat + g.sourceLength i ≤ 2 ^ 32
  workspaceFit : g.workspace.toNat + 8 * g.scratchLength ≤ 2 ^ 32
  outputSources : ∀ i, g.outputRegion.Disjoint (g.sourceRegion i)
  outputWorkspace : g.outputRegion.Disjoint g.workspaceRegion
  outputArguments : g.outputRegion.Disjoint g.argumentsRegion
  sourcesWorkspace : ∀ i, (g.sourceRegion i).Disjoint g.workspaceRegion
  workspaceArguments : g.workspaceRegion.Disjoint g.argumentsRegion
  stackOutput : g.wholeStack.Disjoint g.outputRegion
  stackSources : ∀ i, g.wholeStack.Disjoint (g.sourceRegion i)
  stackWorkspace : g.wholeStack.Disjoint g.workspaceRegion
  stackArguments : g.wholeStack.Disjoint g.argumentsRegion

end Geometry
end VG.Proof.RsaPkcs1Enc.X86.Enc
