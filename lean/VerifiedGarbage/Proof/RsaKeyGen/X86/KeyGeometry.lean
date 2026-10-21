module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

/-! # Every supported native width fits its shared RSA scratch allocation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot

theorem Environment.Valid.widths {E : Environment} (v : E.Valid) :
    16 ≤ E.n ∧ E.n ≤ 256 ∧ E.n = 2 * E.k ∧ 0 < E.k ∧ E.k % 2 = 0 ∧ E.primeLength = 2 * E.n := by
  obtain ⟨lower, upper, multiple⟩ := v.length
  unfold Environment.n Environment.k
  omega

theorem Environment.Valid.bankFit {E : Environment} (v : E.Valid) : arr E.n 32 ≤ E.size := by
  have cap := v.capacity
  have lower := v.length.1
  unfold Spec.Rsa.scratchWords at cap
  unfold Environment.n Environment.size arr S hdr
  omega

theorem Environment.outputPointer (E : Environment) {i : Nat} (hi : i < 7) : E.outputs.pointer i = E.out i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem Environment.Valid.outputLength {E : Environment} (v : E.Valid) {i : Nat} (hi : i < 7) :
    E.outputs.length i = E.outputLength i := by
  have small : E.outputLength i < 2 ^ 32 := by
    have H := v.length.2.1
    unfold Environment.outputLength
    split <;> omega
  have arg : E.argument (2 * i + 1) = BitVec.ofNat 32 (E.outputLength i) := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
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
    split <;> omega
  · intro i hi
    rw [v.outputLength hi]
    change E.outputLength i ≤ 4 * E.n
    unfold Environment.outputLength
    split <;> omega
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
