module
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.VerifySized
import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
import VerifiedGarbage.Proof.Dsa.X86.ABIResources

/-! # Verification of original caller bytes after cdecl argument installation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem verifyingInstalled_spec {s t : State} (A : VerifyingABI s)
    (I : Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s t) :
    WP isa (Entry.sized false (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 8) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 8)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 8)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (0, .p) ∈ Entry.verifyArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Sig, SigBytes⟩ := I.input (by decide : (4, .signature) ∈ Entry.verifyArguments) A.signatureBound
    (by rw [A.rd, A.wr]; simp) A.signatureScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowSignature.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (6, .digest) ∈ Entry.verifyArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, KeyValue⟩ := publicKey_buffers Key L.1 L.2 (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr
  have qPtr := I.arguments (3, .qLen) (by decide)
  have Sptr : pointerValue (argumentPointer s 8) t .signatureS =
      pointerValue (argumentPointer s 8) t (.input .signature) + BitVec.ofNat 32 (arg s 3).toNat := by
    change pointerValue (argumentPointer s 8) t (.input .signature) + pointerValue (argumentPointer s 8) t (.input .qLen) = _
    rw [qPtr]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have S := Sig.slice L.2 (by have := A.signatureLength; omega) Sptr
  have R := Sig.prefix (by have := A.signatureLength; omega : (arg s 3).toNat ≤ (arg s 5).toNat)
  have Rbytes := Sig.slice_bytes (dest := .input .signature) (offset := 0) L.2
    (by have := A.signatureLength; omega) (by simp)
  have Sbytes := Sig.slice_bytes L.2 (by have := A.signatureLength; omega) Sptr
  rw [SigBytes, List.drop_zero] at Rbytes
  rw [SigBytes, List.take_of_length_le (by
    simp only [List.length_drop, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have := A.signatureLength; omega)] at Sbytes
  apply verifySized_spec I.scr A.used A.lengths P Q G Y R S D rfl rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (7, .digestLen) (by decide))) DigestBytes
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.signatureLength)
    KeyValue
  · exact congrArg Spec.Dsa.decodeBE Rbytes.symm
  · exact congrArg Spec.Dsa.decodeBE Sbytes.symm

end VG.Proof.Dsa.X86
