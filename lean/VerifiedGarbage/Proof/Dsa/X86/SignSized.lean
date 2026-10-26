module
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Spec.Dsa.SignVerify

import VerifiedGarbage.Proof.Dsa.X86.Sized
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SignBodySpec
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # The complete public-size signer, including invalid-domain output clearing -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signSized_spec {base : Addr} {size pLen qLen p q g y x k total : Nat}
    {s : State} {out : BitVec 32} {key nonce digest : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (X : CallerBuffer s base size (.input .x) qLen)
    (N : CallerBuffer s base size (.input .nonce) qLen)
    (D : CallerBuffer s base size (.input .digest) total)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (hx : operandValue s base (.input .x) qLen = x)
    (hk : operandValue s base (.input .nonce) qLen = k)
    (hd : (pointerValue base s (.input .digestLen)).toNat = total)
    (hD : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .digest)).setWidth 64) total = digest)
    (ho : pointerValue base s (.input .out) = out)
    (hc : pointerValue base s (.input .qLen) = BitVec.ofNat 32 qLen)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) :
    WP isa (Entry.sized true pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  have sz : 8272 ≤ size := by have H : 15712 ≤ size := extent; omega
  have L : 20 ≤ qLen ∧ qLen ≤ 32 := by unfold Spec.Dsa.lengthsValid at widths; omega
  apply sized_ok true scr extent widths P Q hp hq
  · intro t invalid K O
    have rejected : Spec.Dsa.signBytes pLen qLen key nonce digest = none :=
      signBytes_invalid_shape (by simpa only [keyValue] using invalid)
    refine WP.mono (signFailure_ok (scr.of_keeps K (by decide)) (by change 8256 ≤ size; omega)
      (by omega) L.2 ((shapeFrame_field O (by decide)).trans ho)
      ((shapeFrame_field O (by decide)).trans hc) hf
      (by intro i hi; rw [K.2.2]; exact hw i 1 (by omega))) fun sf ⟨B, V, Of, Kf⟩ => ?_
    have F : OutputFrame base (out.setWidth 64) 0 (2 * qLen) t.mem sf.mem :=
      fun a _ hb => Of a (.inr (by omega))
    refine ⟨by rw [V, rejected]; rfl, by rw [rejected]; exact B,
      (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · intro a hbase hout hstack
      exact (F a (by omega) hout).trans (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega)))
    · intro regs saved
      exact F.saved ha (by decide) sz (by have := scr.nowrap; omega) (shapeFrame_saved O saved)
  · intro t valid M Dp mask K O
    dsimp only [ite_true]
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
    refine WP.mono (signBody_spec M
      (G.keep_shape O K (by decide) (by decide))
      (Y.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      (N.keep_shape O K (by decide) (by decide))
      (Dt.prefix (Nat.min_le_left _ _))
      (by have B := shape_digest_width valid; omega) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy)
      ((X.value_keep_shape O K (by decide) (by decide) bound).trans hx)
      ((N.value_keep_shape O K (by decide) (by decide) bound).trans hk)
      digestValue mask ((shapeFrame_field O (by decide)).trans ho) hf
      (by intro e k he; rw [K.2.2]; exact hw e k he) ha
      valid keyLen nonceLen keyValue nonceValue (shape_digest_width valid).1)
      fun sf ⟨V, B, Kf, F, Saved⟩ => ?_
    refine ⟨V, B, (K.mono (by decide)).trans Kf, ?_, fun regs saved => Saved regs (shapeFrame_saved O saved)⟩
    intro a hbase hout hstack
    exact (F a hbase hout (by rw [K.1 .esp (by decide)]; exact hstack)).trans (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega)))

end VG.Proof.Dsa.X86
