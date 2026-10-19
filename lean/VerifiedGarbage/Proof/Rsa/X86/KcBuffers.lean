module

public import VerifiedGarbage.Proof.Rsa.X86.KcResources

/-! # Readable input buffers and bounds supplied by the key-check signatures -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.KeyCheck

theorem input_index {full : Bool} {i : Nat} (hi : 2 * i < scratchArg full) : i < inputCount full := by
  cases full <;> simp only [scratchArg, inputCount, Bool.false_eq_true, ite_false, ite_true] at * <;> omega

theorem ABI.inputMember {full : Bool} {s : State} (a : ABI full s) {i : Nat}
    (hi : 2 * i < scratchArg full) : (caller full s).buffer (2 * i) ∈ s.rd := by
  rw [a.rd]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr (input_index hi), rfl⟩

theorem ABI.inputLength {full : Bool} {s : State} (a : ABI full s) {i : Nat}
    (hi : 2 * i < scratchArg full) :
    0 < ((caller full s).buffer (2 * i)).len ∧ ((caller full s).buffer (2 * i)).len ≤ 8 * (caller full s).n := by
  have h := a.inputLengths i (input_index hi)
  have width := a.width
  change 0 < (arg s (2 * i + 1)).toNat ∧ (arg s (2 * i + 1)).toNat ≤ _
  omega

theorem ABI.inputFit {full : Bool} {s : State} (a : ABI full s) {i : Nat}
    (hi : 2 * i < scratchArg full) :
    ((caller full s).args (2 * i)).toNat + ((caller full s).buffer (2 * i)).len ≤ 2 ^ 32 :=
  a.inputBounds i (input_index hi)
end VG.Proof.Rsa.X86.KeyCheck
