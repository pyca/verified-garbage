module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_recover_precomputed` on PPC64LE: the mask

Untrusted: everything here is checked by Lean. `maskLoop_ok`: the loop
masks each byte of `out` with the low byte of `r9`. `mask_eq`: `maskM`'s
arithmetic, all ones exactly when the comparison found the two encodings
equal and the call succeeded.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE.Rec

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)

/-- `maskLoop` masks the `n` bytes at `r11 = p`, counted down in `r8`, with
the low byte of `r9`. -/
theorem maskLoop_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h11 : s.gpr .r11 = p) (h8 : s.gpr .r8 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa maskLoop s fun t => Keep [.r10, .r11, .r8] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem p n).map (· &&& (s.gpr .r9).setWidth 8)) := by
  refine WP.mono (wp_countdown (cnt := .r8) hn' hn
    (fun i t => Keep [.r10, .r11, .r8] s t ∧
      t.mem = writeBytes s.mem p (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .r9).setWidth 8)) ∧
      t.gpr .r11 = p + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h11]⟩ h8) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h11'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [h11', hK.wr, BitVec.add_zero]
      obtain ⟨r, hr, hc⟩ := hw _ hi
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hlt : ((Spec.Rsa.bytesAt s.mem p n).take i).length = i := by
      simp [bytesAt_length]; omega_arith
    have hv : t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun i' hi' => Offset.add_ofNat_ne p (by omega_arith) (by omega_arith) (by omega_arith))
        (by simp only [List.length_map, hlt]; omega_arith)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => wp_and fun s₂ o₂ e₂ => ?_
    have hA : InRegions s₂.wr (s₂.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .r11, o₁.get .r11, h11', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₃ m₃ => wp_addi fun s₄ o₄ e₄ => wp_subi fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.r10, .r11, .r8] t s₅ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, m₃.mem, e₂, o₂.mem, e₁, o₁.mem, o₁.get .r9, hK.get .r9, o₂.get .r11, o₁.get .r11,
        h11']
      simp only [BitVec.add_zero]
      rw [hv, BitVec.setWidth_and, byte_setWidth64, hm, bytesAt_take_succ _ _ hi, List.map_append, List.map_cons,
        List.map_nil, writeBytes_snoc _ _ _ _ (by simp only [List.length_map, hlt]; omega_arith), List.length_map, hlt]
    · rw [o₅.get .r11, e₄, m₃.gpr, o₂.get .r11, o₁.get .r11, h11', ofNat_succ']
    · rw [e₅, o₄.get .r8, m₃.gpr, o₂.get .r8, o₁.get .r8]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

/-- The sign bit of `0 - x` for a 32-bit `x`: whether `x` is not 0. -/
theorem neg_bit (x : BitVec 64) :
    (BitVec.ofNat 64 0 - (x <<< 32) >>> 32) >>> 63 = if x.setWidth 32 = 0 then 0 else 1 := by
  have e : (x <<< 32) >>> 32 = (x.setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    have h₁ : x.toNat * 2 ^ 32 % 2 ^ 64 = x.toNat % 2 ^ 32 * 2 ^ 32 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mul_mod_mul_right]
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, h₁,
      Nat.mul_div_cancel _ (by decide), BitVec.toNat_setWidth, BitVec.toNat_setWidth]
    omega_arith
  rw [e]
  by_cases h : x.setWidth 32 = 0
  · rw [h]; decide
  · rw [ite_eq_right h]
    have h' : (x.setWidth 32).toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hl := (x.setWidth 32).isLt
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth]
    simp only [BitVec.toNat_setWidth] at h' hl
    simp; omega_arith

/-- The mask: all ones if `c`, else 0. -/
def maskOf (c : Prop) [Decidable c] : BitVec 64 := if c then BitVec.allOnes 64 else 0

theorem mask_eq (d : BitVec 64) (x : BitVec 64) (hd : d.toNat < 256) :
    BitVec.ofNat 64 0 - ((d - BitVec.ofNat 64 1) >>> 63 &&& (BitVec.ofNat 64 0 - (x <<< 32) >>> 32) >>> 63) =
      maskOf (d = 0 ∧ x.setWidth 32 ≠ 0) := by
  rw [borrow1 hd, neg_bit]
  unfold maskOf
  by_cases h₁ : d = 0 <;> by_cases h₂ : x.setWidth 32 = 0
  · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_right (fun h => h.2 h₂)]; decide
  · rw [ite_eq_left h₁, ite_eq_right h₂, ite_eq_left ⟨h₁, h₂⟩]; decide
  · rw [ite_eq_right h₁, ite_eq_left h₂, ite_eq_right (fun h => h₁ h.1)]; decide
  · rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right (fun h => h₁ h.1)]; decide

theorem maskOf_byte (c : Prop) [Decidable c] (b : Byte) :
    b &&& (maskOf c).setWidth 8 = if c then b else 0 := by
  unfold maskOf
  split
  · rw [show (BitVec.allOnes 64).setWidth 8 = BitVec.allOnes 8 by decide, BitVec.and_allOnes]
  · simp

theorem maskOf_fin (c : Prop) [Decidable c] :
    (BitVec.ofNat 64 1 &&& maskOf c).setWidth 32 = if c then 1 else 0 := by
  unfold maskOf; split <;> decide

/-- Bytes under the mask: themselves or zeros. -/
theorem maskOf_bytes (c : Prop) [Decidable c] (D : List Byte) :
    D.map (· &&& (maskOf c).setWidth 8) = if c then D else List.replicate D.length 0 := by
  simp only [maskOf_byte]
  by_cases hc : c
  · simp [hc]
  · simp [hc, List.map_const']

end VG.Proof.RsaPkcs1Sig.PPC64LE.Rec
