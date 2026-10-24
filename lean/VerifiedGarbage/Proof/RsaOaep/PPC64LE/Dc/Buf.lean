module

import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Label
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.PrivCall
public import VerifiedGarbage.TCB.Mem

/-!
# RSAES-OAEP decryption on PPC64LE: the buffer and its shift

Untrusted: everything here is checked by Lean. `clearBuf_ok`: the buffer's
2048 bytes at `oBuf` cleared; `copyT_ok`: `T` copied to its start;
`shift_ok`: its first `k` bytes shifted left by `idx + 1` in ten passes
(`shV`, `Proof/RsaPss/PPC64LE/ShiftV.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.Impl.RsaOaep.PPC64LE.Dec VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep wp_li wp_mov wp_addi wp_subi wp_add wp_sub wp_and wp_or wp_xor wp_lsr
  wp_lbz wp_stb wp_nil wp_countdown)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaPss.PPC64LE (passV shV)
open VG.Proof.Mgf1 (ifp ifn)

/-- `-(x ∧ 1)`: all ones if `x` is odd, zero if not. -/
theorem mask_odd (x : Nat) : BitVec.ofNat 64 0 - (BitVec.ofNat 64 x &&& BitVec.ofNat 64 1) =
    if x % 2 = 1 then BitVec.allOnes 64 else 0#64 := by
  have e : BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.and_one_is_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2 ^ 64)]
    have := Nat.mod_lt x (show 0 < 2 by decide)
    rw [Nat.mod_eq_of_lt (by omega : x % 2 < 2 ^ 64)]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

/-- The byte a pass writes: `a ⊕ ((b ⊕ a) ∧ m)`, for the mask `m`. -/
theorem sel_byte (a b : Byte) (bit : Bool) :
    ((a.setWidth 64 ^^^ ((b.setWidth 64 ^^^ a.setWidth 64) &&&
      (if bit then BitVec.allOnes 64 else 0#64))).setWidth 8) = if bit then b else a := by
  cases bit
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_comm (a.setWidth 64)]
    simp [BitVec.xor_assoc]

theorem offs' : oEm = 0 ∧ oSt = 1024 ∧ oDig = 1280 ∧ oW = 1352 ∧ oBuf = 2560 ∧ oRsa = 8192 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {s : State} (P : PreD s) {m : Mem} {rc : Nat}
include P

/-- The buffer cleared. -/
theorem clearBuf_ok {t : State} (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa clearBuf t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ [Reg.r24, .r25], t'.gpr r = t.gpr r) ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = if oBuf ≤ o ∧ o < oBuf + 2048 then 0 else view t.mem (Sd s) o := by
  obtain ⟨hE, hSt, hDg, hW, hB, hRs⟩ := offs'
  have PF := fitsM (m := m) P
  refine WP.seq (wp_addi fun t₁ o₁ e₁ => wp_li (by decide) fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_)
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (zero_ok (p := off (Sd s) oBuf) (n := 2048) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.r14]) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (sc_w PF (by rw [k₃.wr, h.wr]) (by omega))) fun t' ⟨hk, hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6] t t' := (k₃.keep.trans hk).mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf) (List.replicate 2048 0) := by rw [hm, k₃.mem]
  refine ⟨h.wb PF hK (by rw [List.length_replicate]; omega) hm', fun r hr => hK.gpr r (by revert r; decide),
    fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [List.length_replicate]; omega) ho, List.length_replicate]
  split
  · rename_i hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ifp (by omega)]; rfl
  · rfl

/-- `T` (`k - 2 D - 1` bytes at `1 + 2 D`) to the buffer. -/
theorem copyT_ok {H : Hash} {D : Nat} (hD : H.D = D) (hD64 : D ≤ 64) (hk : 2 * D + 2 ≤ kk s) {t : State}
    (h : Base (SD s) (VD s rc) (withMem s m) t) :
    WP isa (copyT H) t fun t' => Base (SD s) (VD s rc) (withMem s m) t' ∧
      (∀ r ∈ Reg.r14 :: fx ++ hiRegs ++ [Reg.r24, .r25], t'.gpr r = t.gpr r) ∧
      ∀ o < oRsa, view t'.mem (Sd s) o = if oBuf ≤ o ∧ o < oBuf + (kk s - (2 * D + 1)) then
        view t.mem (Sd s) (1 + 2 * D + (o - oBuf)) else view t.mem (Sd s) o := by
  obtain ⟨hE, hSt, hDg, hW, hB, hRs⟩ := offs'
  have hk2 := P.k2
  have ek : kk s = (s.gpr .r7).toNat := rfl
  have PF := fitsM (m := m) P
  subst hD
  refine WP.seq (wp_addi (h := by unfold oEm; omega) fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ =>
    wp_mov fun t₃ o₃ e₃ => wp_addi fun t₄ o₄ e₄ => wp_nil ?_)
  have k₄ : Only [.r4, .r5, .r6] t t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  have hn : t₄.gpr .r6 = BitVec.ofNat 64 (kk s - (2 * H.D + 1)) := by
    rw [o₄.get .r6, e₃, e₂, o₁.get .r15, Base.r15 h, sub_ofNat (by omega)]
  refine WP.mono (copy_ok (q := off (Sd s) (1 + 2 * H.D)) (p := off (Sd s) oBuf) (n := kk s - (2 * H.D + 1))
    (by omega) (by omega) (by rw [o₄.get .r4, o₃.get .r4, o₂.get .r4, e₁, h.r14, hE, Nat.zero_add])
    (by rw [e₄, o₃.get .r14, o₂.get .r14, o₁.get .r14, h.r14]) hn
    (fun j hj => by
      rw [k₄.rd, k₄.wr, h.wr]
      show InRegions _ (off (off (Sd s) (1 + 2 * H.D)) j) 1
      rw [off_off]; exact sc_inR PF (by omega) _)
    (sc_w PF (by rw [k₄.wr, h.wr]) (by omega))
    (fun j hj i hi => by
      show off (off (Sd s) (1 + 2 * H.D)) j ≠ off (off (Sd s) oBuf) i
      rw [off_off, off_off]
      exact Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))) fun t' ⟨hk', hm⟩ => ?_
  have hK : Keep [.r4, .r5, .r6, .r7] t t' := (k₄.keep.trans hk').mono
  have hm' : t'.mem = writeBytes t.mem (off (Sd s) oBuf)
      (Spec.Rsa.bytesAt t.mem (off (Sd s) (1 + 2 * H.D)) (kk s - (2 * H.D + 1))) := by rw [hm, k₄.mem]
  refine ⟨h.wb PF hK (by rw [bytesAt_length]; omega) hm', fun r hr => hK.gpr r (by revert r; decide),
    fun o ho => ?_⟩
  rw [hm', view_wb _ _ (by rw [bytesAt_length]; omega) ho, bytesAt_length]
  split
  · rename_i hc
    simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show o - oBuf < kk s - (2 * H.D + 1) by omega), Option.map_some, Option.getD_some]
    show t.mem (off (off (Sd s) (1 + 2 * H.D)) (o - oBuf)) = _
    rw [off_off]; rfl
  · rfl

end

end VG.Proof.RsaOaep.PPC64LE.Dec
