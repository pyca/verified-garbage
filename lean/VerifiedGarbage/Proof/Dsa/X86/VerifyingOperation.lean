module

public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Dsa.X86.WidthDispatch
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.X86.Sized
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.VerifyBodySpec
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
/-! # Complete functional and cdecl verification of the x86 verifier -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/VerifySized.lean`, which only this module imported.
section

/-! # The complete public-size verifier, including invalid domain rejection -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem verifySized_spec {base : Addr} {size pLen qLen p q g y total rv sv : Nat}
    {s : State} {key signature digest : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (R : CallerBuffer s base size (.input .signature) qLen)
    (S : CallerBuffer s base size .signatureS qLen)
    (D : CallerBuffer s base size (.input .digest) total)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (hr : operandValue s base (.input .signature) qLen = rv)
    (hs : operandValue s base .signatureS qLen = sv)
    (hd : (pointerValue base s (.input .digestLen)).toNat = total)
    (hD : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .digest)).setWidth 64) total = digest)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv) :
    WP isa (Entry.sized false pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes pLen qLen key signature digest then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  apply sized_ok false scr extent widths P Q hp hq
  · intro t invalid K O
    have rejected : Spec.Dsa.verifyBytes pLen qLen key signature digest = false :=
      verifyBytes_invalid_shape (by simpa only [keyValue] using invalid)
    refine WP.mono (verifyFailure_ok t) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨by rw [V, rejected]; rfl,
      (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · rw [Of]
      intro a ha _
      exact (shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega))
    · intro regs saved
      rw [Of]
      exact shapeFrame_saved O saved
  · intro t valid M Dp mask K O
    dsimp only [Bool.false_eq_true, ite_false]
    rw [hd] at Dp
    have Bw := shape_digest_width valid
    have hP : pointerValue base t (.input .digestPrefixLen) =
        BitVec.ofNat 32 (min total (Spec.Dsa.bitLength q / 8)) :=
      BitVec.eq_of_toNat_eq (by rw [Dp, BitVec.toNat_ofNat]; omega)
    have Dt := D.keep_shape O K (by decide) (by decide)
    have Db := D.bytes_keep_shape O K (by decide) (by decide) bound
    have digestValue : operandValue t base (.input .digest)
        (min total (Spec.Dsa.bitLength q / 8)) = Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength q / 8)) := by
      unfold operandValue
      rw [bytesAt_prefix, Db, hD]
    refine WP.mono (verifyBody_spec M
      (G.keep_shape O K (by decide) (by decide))
      (Y.keep_shape O K (by decide) (by decide))
      (R.keep_shape O K (by decide) (by decide))
      (S.keep_shape O K (by decide) (by decide))
      (Dt.prefix (Nat.min_le_left _ _))
      (by have B := shape_digest_width valid; omega) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy)
      ((R.value_keep_shape O K (by decide) (by decide) bound).trans hr)
      ((S.value_keep_shape O K (by decide) (by decide) bound).trans hs)
      digestValue mask valid keyLen sigLen keyValue rValue sValue (shape_digest_width valid).1)
      fun sf ⟨V, E⟩ => ?_
    exact ⟨V, (K.mono (by decide)).trans E.keeps,
      (fun a ha hstack => ((execution_outside E) a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega)))) ,
      fun regs saved => E.saved (shapeFrame_saved O saved)⟩

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/VerifyingInstalled.lean`, which only this module imported.
section

/-! # Verification of original caller bytes after cdecl argument installation -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem supportedWidths_member {pLen qLen : Nat} (H : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  unfold Spec.Dsa.lengthsValid at H
  omega

theorem verifyingOperation_spec {s : State} (A : VerifyingABI s) :
    WP isa (Entry.operation false) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 9).toNat * 8 := by have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega
  unfold Entry.operation Core.sequence
  dsimp only [List.foldr, Bool.false_eq_true, ite_false]
  refine WP.seq (WP.mono (verifyingEntry_ok A) fun t I => ?_)
  refine WP.seq (widthDispatch_ok false _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (verifyingInstalled_spec A J) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega)
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
