module

public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.DeriveSized
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.DerivingResources

/-! # Derivation reads the caller's parameters and explicit scalar -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem derivingInstalled_spec {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa (Generate.deriveSized (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      Keeps powerClob t sf ∧ StackOutputFrame (t.gpr .esp) (argumentPointer s 7)
        (argumentPointer s 0) usedBytes (arg s 1).toNat t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 7)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 7)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (2, .p) ∈ Generate.deriveArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨X, XBytes⟩ := I.input (by decide : (5, .nonce) ∈ Generate.deriveArguments) A.scalarBound
    (by rw [A.rd, A.wr]; simp) A.scalarScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowScalar.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  rw [A.outLength]
  apply deriveSized_spec (out := arg s 0) I.scr A.used A.lengths
    (by rw [← A.keyLength]; exact Params) P Q G X rfl rfl rfl rfl
    (by rw [← A.keyLength]; exact Bytes) XBytes (I.arguments (0, .out) (by decide))
    (by rw [← A.outLength]; exact A.outBound) ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by rw [I.arguments (2, .p) (by decide), ← A.keyLength, ← A.outLength]; exact A.keyOut)
    (by rw [I.arguments (5, .nonce) (by decide), ← A.outLength]; exact A.scalarOut) Value
  intro i hi
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

end VG.Proof.Dsa.X86
