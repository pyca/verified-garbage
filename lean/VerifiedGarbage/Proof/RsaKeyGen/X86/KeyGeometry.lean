module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Spec.RsaKeyGen.Contract

/-! ### `RsaKeyGen.X86.KeyEnvironment`, which this module and modules that import it used -/

section

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

end

end

/-! # Every supported native width fits its shared RSA scratch allocation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem Environment.Valid.widths {E : Environment} (v : E.Valid) :
    16 ≤ E.n ∧ E.n ≤ 256 ∧ E.n = 2 * E.k ∧ 0 < E.k ∧ E.k % 2 = 0 ∧ E.primeLength = 2 * E.n := by
  obtain ⟨lower, upper, multiple⟩ := v.length
  unfold Environment.n Environment.k
  omega_using [lower, upper, multiple]

theorem Environment.Valid.bankFit {E : Environment} (v : E.Valid) : arr E.n 32 ≤ E.size := by
  have cap := v.capacity
  have lower := v.length.1
  unfold Spec.Rsa.scratchWords at cap
  unfold Environment.n Environment.size arr S hdr
  omega_using [cap, lower]

theorem Environment.outputPointer (E : Environment) {i : Nat} (hi : i < 7) : E.outputs.pointer i = E.out i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega_using [hi]
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem Environment.Valid.outputLength {E : Environment} (v : E.Valid) {i : Nat} (hi : i < 7) :
    E.outputs.length i = E.outputLength i := by
  have small : E.outputLength i < 2 ^ 32 := by
    have H := v.length.2.1
    unfold Environment.outputLength
    split <;> omega_using [H]
  have arg : E.argument (2 * i + 1) = BitVec.ofNat 32 (E.outputLength i) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  change (E.argument (2 * i + 1)).toNat = _
  rw [arg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem Environment.Valid.outputRegion {E : Environment} (v : E.Valid) {i : Nat} (hi : i < 7) :
    E.outputs.region i = E.outputRegion i := by
  unfold OutputGeometry.region Environment.outputRegion
  rw [E.outputPointer hi, v.outputLength hi]

theorem Environment.Valid.outputs {E : Environment} (v : E.Valid) : E.outputs.Valid := by
  have lengths := v.widths
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [v.outputLength hi]
    have lower := v.length.1
    unfold Environment.outputLength
    split <;> omega_using [lengths]
  · intro i hi
    rw [v.outputLength hi]
    change E.outputLength i ≤ 4 * E.n
    unfold Environment.outputLength
    split <;> omega_using [lengths]
  · intro i hi
    rw [E.outputPointer hi, v.outputLength hi]
    exact v.outFit i hi
  · intro i hi
    rw [v.outputRegion hi]
    exact (v.outputScratch i hi).symm
  · intro i hi j hj ne
    rw [v.outputRegion hi, v.outputRegion hj]
    exact v.outputSeparate i hi j hj ne

end VG.Proof.RsaKeyGen.X86.Key
