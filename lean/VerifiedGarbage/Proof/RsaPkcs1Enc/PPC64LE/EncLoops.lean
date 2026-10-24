module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: the loops

Untrusted: everything here is checked by Lean. `psLoop_ok`: `PS` is copied,
and the low bit of `r5` set if one of its bytes is zero (`zbit`).
`msgLoop_ok`: `M` is copied. `maskLoop_ok`: `out`'s bytes are masked with
`r5` and `EM`'s zeroed. As `encode`'s loops (`Proof/RsaPkcs1Sig/PPC64LE/Encode.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)

/-- 1 if one of the bytes is zero, 0 if not. -/
def zbit (l : List Byte) : BitVec 64 := if l.all (· != 0) then 0 else 1

theorem zbit_nil : zbit [] = 0 := rfl

theorem zbit_snoc (l : List Byte) (b : Byte) :
    zbit (l ++ [b]) = zbit l ||| (if b = 0 then 1 else 0) := by
  unfold zbit
  rw [List.all_append]
  cases hl : l.all (· != 0) <;> by_cases hb : b = 0 <;> simp [hb] <;> first | decide | (split <;> decide)

theorem zbit_le (l : List Byte) : zbit l = 0 ∨ zbit l = 1 := by
  unfold zbit; split <;> simp

theorem byte_toNat_lt (b : Byte) : (b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_setWidth]; have := b.isLt; omega

theorem setWidth_eq_zero {b : Byte} : (b.setWidth 64 = 0) ↔ b = 0 := by
  constructor
  · intro h; have := congrArg (BitVec.setWidth 8) h; simpa using this
  · intro h; rw [h]; rfl

/-- `psLoop` copies the `n` bytes at `r4 = q` to `r11 = p`, counted down in
`r12`, and ORs their zero test into `r5`. -/
theorem psLoop_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = q) (h11 : s.gpr .r11 = p) (h12 : s.gpr .r12 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa psLoop s fun t => Keep [.r0, .r3, .r4, .r5, .r11, .r12] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .r5 = s.gpr .r5 ||| zbit (Spec.Rsa.bytesAt s.mem q n) ∧
      t.gpr .r11 = p + BitVec.ofNat 64 n := by
  refine WP.mono (wp_countdown (cnt := .r12) hn' hn
    (fun i t => Keep [.r0, .r3, .r4, .r5, .r11, .r12] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .r4 = q + BitVec.ofNat 64 i ∧ t.gpr .r11 = p + BitVec.ofNat 64 i ∧
      t.gpr .r5 = s.gpr .r5 ||| zbit ((Spec.Rsa.bytesAt s.mem q n).take i)) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h4], by simp [h11], by simp [zbit_nil]⟩ h12)
    fun t h => ⟨h.1, ?_, ?_, h.2.2.2.1⟩
  · intro i hi t ⟨hK, hm, h4', h11', h5'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .r11 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .r11, h11', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₂ m₂ => wp_subi fun s₃ o₃ e₃ => wp_lsr fun s₄ o₄ e₄ => wp_or fun s₅ o₅ e₅ =>
      wp_addi fun s₆ o₆ e₆ => wp_addi fun s₇ o₇ e₇ => wp_subi fun s₈ o₈ e₈ => wp_nil ?_
    have hK' : Keep [.r0, .r3, .r4, .r5, .r11, .r12] t s₈ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
        (o₇.keep.trans o₈.keep))))))).mono
    have hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega
    have hb : s₂.gpr .r3 = (s.mem (q + BitVec.ofNat 64 i)).setWidth 64 := by
      rw [m₂.gpr, e₁, h4', BitVec.add_zero, hv]
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h4', o₁.get .r11, h11']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, hm, bytesAt_take_succ _ _ hi, writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₈.get .r4, o₇.get .r4, e₆, o₅.get .r4, o₄.get .r4, o₃.get .r4, m₂.gpr, o₁.get .r4, h4', ofNat_succ']
    · rw [o₈.get .r11, e₇, o₆.get .r11, o₅.get .r11, o₄.get .r11, o₃.get .r11, m₂.gpr, o₁.get .r11, h11',
        ofNat_succ']
    · rw [o₈.get .r5, o₇.get .r5, o₆.get .r5, e₅, o₄.get .r5, e₄, o₃.get .r5, e₃, hb, m₂.gpr, o₁.get .r5, h5',
        borrow1 (byte_toNat_lt _), bytesAt_take_succ _ _ hi, zbit_snoc, BitVec.or_assoc]
      congr 2
      by_cases h : s.mem (q + BitVec.ofNat 64 i) = 0
      · rw [ite_eq_left h, ite_eq_left (setWidth_eq_zero.mpr h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (setWidth_eq_zero.mp h'))]
    · rw [e₈, o₇.get .r12, o₆.get .r12, o₅.get .r12, o₄.get .r12, o₃.get .r12, m₂.gpr, o₁.get .r12]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.2.2.2

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
