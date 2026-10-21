module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-! # Public lengths, pointers, and cdecl arguments for native key assembly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

structure Environment where
  workspace : BitVec 32
  capacity : Nat
  out : Nat → BitVec 32
  primeLength : Nat
  exponent : BitVec 32
  exponentLength : Nat

def Environment.base (E : Environment) : Addr := E.workspace.setWidth 64
def Environment.size (E : Environment) : Nat := 8 * E.capacity
def Environment.n (E : Environment) : Nat := E.primeLength / 2
def Environment.k (E : Environment) : Nat := E.primeLength / 4
def Environment.outputLength (E : Environment) (i : Nat) : Nat := if i < 2 then 2 * E.primeLength else E.primeLength
def Environment.outputRegion (E : Environment) (i : Nat) : Region := ⟨(E.out i).setWidth 64, E.outputLength i⟩
def Environment.workspaceRegion (E : Environment) : Region := ⟨E.base, E.size⟩
def Environment.exponentRegion (E : Environment) : Region := ⟨E.exponent.setWidth 64, E.exponentLength⟩

def Environment.argument (E : Environment) : Nat → BitVec 32
  | 0 => E.out 0
  | 1 => BitVec.ofNat 32 (2 * E.primeLength)
  | 2 => E.out 1
  | 3 => BitVec.ofNat 32 (2 * E.primeLength)
  | 4 => E.out 2
  | 5 => BitVec.ofNat 32 E.primeLength
  | 6 => E.out 3
  | 7 => BitVec.ofNat 32 E.primeLength
  | 8 => E.out 4
  | 9 => BitVec.ofNat 32 E.primeLength
  | 10 => E.out 5
  | 11 => BitVec.ofNat 32 E.primeLength
  | 12 => E.out 6
  | 13 => BitVec.ofNat 32 E.primeLength
  | 14 => E.exponent
  | 15 => BitVec.ofNat 32 E.exponentLength
  | 16 => E.workspace
  | _ => BitVec.ofNat 32 E.capacity

def Environment.outputs (E : Environment) : OutputGeometry := ⟨E.base, E.size, E.n, E.argument⟩

structure Environment.Valid (E : Environment) : Prop where
  length : Spec.RsaKeyGen.primeLenValid E.primeLength
  exponentLength : 1 ≤ E.exponentLength ∧ E.exponentLength ≤ 8
  capacity : Spec.Rsa.scratchWords (2 * E.primeLength) ≤ E.capacity
  workspaceFit : E.workspace.toNat + E.size ≤ 2 ^ 32
  outFit : ∀ i < 7, (E.out i).toNat + E.outputLength i ≤ 2 ^ 32
  exponentFit : E.exponent.toNat + E.exponentLength ≤ 2 ^ 32
  outputScratch : ∀ i < 7, (E.outputRegion i).Disjoint E.workspaceRegion
  outputSeparate : ∀ i < 7, ∀ j < 7, i ≠ j → (E.outputRegion i).Disjoint (E.outputRegion j)
  exponentScratch : E.exponentRegion.Disjoint E.workspaceRegion
  exponentOutput : ∀ i < 7, E.exponentRegion.Disjoint (E.outputRegion i)

end VG.Proof.RsaKeyGen.X86.Key
