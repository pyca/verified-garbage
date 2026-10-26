module
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Spec.Dsa.SignVerify

import VerifiedGarbage.Proof.Dsa.X86.Sized
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.VerifyBodySpec
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # The complete public-size verifier, including invalid domain rejection -/

@[expose] public section
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
