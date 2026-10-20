module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! # Public buffers and frame geometry of PKCS #1 signing

The eight source buffers are n, e, digest, p, q, dp, dq, and qInv. Stack
arguments lie above the wrapper's two frames and return address; each callee has a separate
3392-byte region below the inner frame.
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86

def sigStack : Nat := 4528
def calleeBytes : Nat := 3392

structure Geometry where
  stack : BitVec 32
  output : BitVec 32
  workspace : BitVec 32
  sources : Fin 8 → BitVec 32
  length : Nat
  hash : BitVec 32
  digestLength : Nat
  exponentLength : Nat
  pLength : Nat
  qLength : Nat
  scratchLength : Nat

namespace Geometry

def sourceLength (g : Geometry) (i : Fin 8) : Nat :=
  match i.val with
  | 1 => g.exponentLength
  | 2 => g.digestLength
  | 3 | 5 | 7 => g.pLength
  | 4 | 6 => g.qLength
  | _ => g.length

def sourceRegion (g : Geometry) (i : Fin 8) : Region := ⟨byteAddr (g.sources i), g.sourceLength i⟩
def outputRegion (g : Geometry) : Region := ⟨byteAddr g.output, g.length⟩
def workspaceRegion (g : Geometry) : Region := ⟨byteAddr g.workspace, 8 * g.scratchLength⟩
def innerRegion (g : Geometry) : Region := ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes⟩
def savedRegion (g : Geometry) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes, 16⟩
def calleeRegion (g : Geometry) : Region := VG.X86.below g.stack calleeBytes
def argumentsRegion (g : Geometry) : Region :=
  ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20), 84⟩
def wholeStack (g : Geometry) : Region := ⟨byteAddr (g.stack - BitVec.ofNat 32 calleeBytes), sigStack⟩
def temporary (g : Geometry) : BitVec 32 := g.stack + BitVec.ofNat 32 emOffset

def argument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.output | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 0 | 3 => BitVec.ofNat 32 g.length
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.hash
  | 7 => g.sources 2 | 8 => BitVec.ofNat 32 g.digestLength
  | 9 => g.sources 3 | 10 => BitVec.ofNat 32 g.pLength
  | 11 => g.sources 4 | 12 => BitVec.ofNat 32 g.qLength
  | 13 => g.sources 5 | 14 => BitVec.ofNat 32 g.pLength
  | 15 => g.sources 6 | 16 => BitVec.ofNat 32 g.qLength
  | 17 => g.sources 7 | 18 => BitVec.ofNat 32 g.pLength
  | 19 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

structure Valid (g : Geometry) : Prop where
  minLength : 64 ≤ g.length
  maxLength : g.length ≤ 1024
  digestBound : g.digestLength < 2 ^ 32
  exponentPositive : 0 < g.exponentLength
  exponentFits : g.exponentLength ≤ g.length
  pPositive : 0 < g.pLength
  pFits : g.pLength < g.length
  qPositive : 0 < g.qLength
  qFits : g.qLength < g.length
  space : Spec.Rsa.scratchWords g.length ≤ g.scratchLength
  stackLow : calleeBytes ≤ g.stack.toNat
  stackHigh : g.stack.toNat + VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84 ≤ 2 ^ 32
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
end VG.Proof.RsaPkcs1Sig.X86.Sgn
