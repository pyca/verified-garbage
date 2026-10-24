module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption on PPC64LE: the loops

Untrusted: everything here is checked by Lean. `zero_ok`: `zeroLoop` writes
`n` copies of a byte; `copy_ok`: `copyLoop` copies `n` bytes. As the loops of
RSASSA-PKCS1-v1_5 (`Proof/RsaPkcs1Sig/PPC64LE/Encode.lean`), at any address.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_stb wp_lbz wp_addi wp_subi wp_nil wp_countdown byte_setWidth64
  ofNat_succ')
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_take_succ writeBytes_out)

/-- `zeroLoop` writes `n` bytes `b` (the low byte of `r6`) from `r4 = p`,
counted down in `r5`, at any writable address. -/
theorem zero_ok {s : State} {p : Addr} {n : Nat} {b : Byte} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = p) (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : (s.gpr .r6).setWidth 8 = b)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa zeroLoop s fun t => Keep [.r4, .r5] s t ∧ t.mem = writeBytes s.mem p (List.replicate n b) := by
  refine WP.mono (wp_countdown (cnt := .r5) hn' hn
    (fun i t => Keep [.r4, .r5] s t ∧ t.mem = writeBytes s.mem p (List.replicate i b) ∧
      t.gpr .r4 = p + BitVec.ofNat 64 i) ?_ ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h4]⟩ h5)
    fun t h => ⟨h.1, h.2.1⟩
  intro i hi t ⟨hK, hm, h4'⟩ _
  have hA : InRegions t.wr (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
    rw [h4', hK.wr, BitVec.add_zero]; exact hw _ hi
  refine wp_stb rfl hA fun s₁ m₁ => ?_
  refine wp_addi fun s₂ o₂ e₂ => ?_
  refine wp_subi fun s₃ o₃ e₃ => wp_nil ?_
  have hK' : Keep [.r4, .r5] t s₃ := (m₁.keep.trans (o₂.keep.trans o₃.keep)).mono
  refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
  · rw [o₃.mem, o₂.mem, m₁.mem, hK.get .r6, h6, h4', BitVec.add_zero, hm, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp; omega)]
    simp
  · rw [o₃.get .r4, e₂, m₁.gpr, h4', ofNat_succ']
  · rw [e₃, o₂.get .r5, m₁.gpr]

/-- `copyLoop` copies `n` bytes from `r4 = q` to `r5 = p`, counted down in
`r6`, the source readable, the destination writable and apart from it. -/
theorem copy_ok {s : State} {p q : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h4 : s.gpr .r4 = q) (h5 : s.gpr .r5 = p) (h6 : s.gpr .r6 = BitVec.ofNat 64 n)
    (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ j < n, ∀ i < n, q + BitVec.ofNat 64 j ≠ p + BitVec.ofNat 64 i) :
    WP isa copyLoop s fun t => Keep [.r7, .r4, .r5, .r6] s t ∧
      t.mem = writeBytes s.mem p (Spec.Rsa.bytesAt s.mem q n) := by
  refine WP.mono (wp_countdown (cnt := .r6) hn' hn
    (fun i t => Keep [.r7, .r4, .r5, .r6] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem q n).take i) ∧
      t.gpr .r5 = p + BitVec.ofNat 64 i ∧ t.gpr .r4 = q + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h5], by simp [h4]⟩ h6) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h5', h4'⟩ _
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .r4 + BitVec.ofNat 64 0) 1 := by
      rw [h4', hK.rd, hK.wr, BitVec.add_zero]; exact hr _ hi
    have hv : t.mem (q + BitVec.ofNat 64 i) = s.mem (q + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ n (fun i' hi' => hd i hi i' hi')
        (by simp only [List.length_take, bytesAt_length]; omega)]
    refine wp_lbz rfl hR fun s₁ o₁ e₁ => ?_
    have hA : InRegions s₁.wr (s₁.gpr .r5 + BitVec.ofNat 64 0) 1 := by
      rw [o₁.wr, o₁.get .r5, h5', hK.wr, BitVec.add_zero]; exact hw _ hi
    refine wp_stb rfl hA fun s₂ m₂ => ?_
    refine wp_addi fun s₃ o₃ e₃ => ?_
    refine wp_addi fun s₄ o₄ e₄ => ?_
    refine wp_subi fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.r7, .r4, .r5, .r6] t s₅ :=
      (o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    have hlt : ((Spec.Rsa.bytesAt s.mem q n).take i).length = i := by
      simp [bytesAt_length]; omega
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, o₃.mem, m₂.mem, e₁, o₁.mem, h4']
      simp only [BitVec.add_zero]
      rw [hv, byte_setWidth64, o₁.get .r5, h5', hm, bytesAt_take_succ _ _ hi,
        writeBytes_snoc _ _ _ _ (by omega), hlt]
    · rw [o₅.get .r5, e₄, o₃.get .r5, m₂.gpr, o₁.get .r5, h5', ofNat_succ']
    · rw [o₅.get .r4, o₄.get .r4, e₃, m₂.gpr, o₁.get .r4, h4', ofNat_succ']
    · rw [e₅, o₄.get .r6, o₃.get .r6, m₂.gpr, o₁.get .r6]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

end VG.Proof.RsaOaep.PPC64LE
