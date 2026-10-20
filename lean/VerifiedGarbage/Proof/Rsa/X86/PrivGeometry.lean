module

public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public buffer geometry of checked private RSA

The eight source buffers are n, e, input, p, q, dp, dq, and qInv. Stack
arguments lie above the wrapper's two frames and return address; each callee has a separate
44-byte frame below the inner frame.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

structure PrivGeometry where
  stack : BitVec 32
  output : BitVec 32
  workspace : BitVec 32
  sources : Fin 8 → BitVec 32
  length : Nat
  exponentLength : Nat
  pLength : Nat
  qLength : Nat
  scratchLength : Nat

namespace PrivGeometry

def sourceLength (g : PrivGeometry) (i : Fin 8) : Nat :=
  match i.val with
  | 1 => g.exponentLength
  | 3 | 5 | 7 => g.pLength
  | 4 | 6 => g.qLength
  | _ => g.length

def sourceRegion (g : PrivGeometry) (i : Fin 8) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def outputRegion (g : PrivGeometry) : Region := ⟨byteAddr g.output, g.length⟩
def workspaceRegion (g : PrivGeometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : PrivGeometry) : Region := ⟨byteAddr g.stack, VG.Impl.Rsa.X86.PrivChecked.frameBytes⟩
def savedRegion (g : PrivGeometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.Rsa.X86.PrivChecked.frameBytes, 16⟩
def calleeRegion (g : PrivGeometry) : Region := VG.X86.below g.stack 44
def argumentsRegion (g : PrivGeometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20), 80⟩
def wholeStack (g : PrivGeometry) : Region := ⟨byteAddr (g.stack - BitVec.ofNat 32 44), stackBytes⟩
def temporary (g : PrivGeometry) : BitVec 32 := g.stack + BitVec.ofNat 32 candidateOffset
def precomputation (g : PrivGeometry) : BitVec 32 := g.stack + BitVec.ofNat 32 precomputeOffset

def argument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 0 | 3 => BitVec.ofNat 32 g.length
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.sources 2 | 7 => BitVec.ofNat 32 g.length
  | 8 => g.sources 3 | 9 => BitVec.ofNat 32 g.pLength
  | 10 => g.sources 4 | 11 => BitVec.ofNat 32 g.qLength
  | 12 => g.sources 5 | 13 => BitVec.ofNat 32 g.pLength
  | 14 => g.sources 6 | 15 => BitVec.ofNat 32 g.qLength
  | 16 => g.sources 7 | 17 => BitVec.ofNat 32 g.pLength
  | 18 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

structure Valid (g : PrivGeometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  pPositive : 0 < g.pLength
  pFits : g.pLength < g.length
  qPositive : 0 < g.qLength
  qFits : g.qLength < g.length
  space : Spec.Rsa.scratchWords g.length ≤ g.scratchLength
  stackLow : 44 ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.Rsa.X86.PrivChecked.frameBytes + 20 + 80 ≤ 2 ^ 32
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
end PrivGeometry
end VG.Proof.Rsa.X86.PrivChecked
