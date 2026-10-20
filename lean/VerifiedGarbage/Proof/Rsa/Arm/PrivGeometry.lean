module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl

/-! # Public buffer geometry of checked private RSA

The eight source buffers are n, e, input, p, q, dp, dq, and qInv. Stack
arguments lie above the wrapper's two frames; each callee has a separate
56-byte frame below the inner frame.
-/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked

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

def sourceRegion (g : PrivGeometry) (i : Fin 8) : Region := ⟨State.addr (g.sources i), g.sourceLength i⟩
def outputRegion (g : PrivGeometry) : Region := ⟨State.addr g.output, g.length⟩
def workspaceRegion (g : PrivGeometry) : Region := ⟨State.addr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : PrivGeometry) : Region := ⟨State.addr g.stack, frameBytes⟩
def savedRegion (g : PrivGeometry) : Region := ⟨State.addr g.stack + BitVec.ofNat 64 frameBytes, 56⟩
def calleeRegion (g : PrivGeometry) : Region := FrameStack.belowA g.stack 56
def argumentsRegion (g : PrivGeometry) : Region := ⟨State.addr g.stack + BitVec.ofNat 64 (frameBytes + 56), 64⟩
def wholeStack (g : PrivGeometry) : Region := ⟨State.addr (g.stack - BitVec.ofNat 32 56), stackBytes⟩
def temporary (g : PrivGeometry) : BitVec 32 := g.stack + BitVec.ofNat 32 oM
def precomputation (g : PrivGeometry) : BitVec 32 := g.stack + BitVec.ofNat 32 oPre

def argument (g : PrivGeometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.sources 1 | 1 => BitVec.ofNat 32 g.exponentLength
  | 2 => g.sources 2 | 3 => BitVec.ofNat 32 g.length
  | 4 => g.sources 3 | 5 => BitVec.ofNat 32 g.pLength
  | 6 => g.sources 4 | 7 => BitVec.ofNat 32 g.qLength
  | 8 => g.sources 5 | 9 => BitVec.ofNat 32 g.pLength
  | 10 => g.sources 6 | 11 => BitVec.ofNat 32 g.qLength
  | 12 => g.sources 7 | 13 => BitVec.ofNat 32 g.pLength
  | 14 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

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
  stackLow : 56 ≤ g.stack.toNat
  stackHigh : g.stack.toNat + frameBytes + 56 + 64 ≤ 2 ^ 32
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
end VG.Proof.Rsa.Arm
