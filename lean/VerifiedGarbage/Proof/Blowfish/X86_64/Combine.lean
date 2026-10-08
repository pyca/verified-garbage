import VerifiedGarbage.Proof.Blowfish.X86_64.Reduce
import VerifiedGarbage.Proof.Blowfish.X86_64.Row
import VerifiedGarbage.Proof.Blowfish.Schedule

/-! # An S-box entry from its byte planes; the index in every lane -/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish

/-- The entry's bytes, shifted into place and ORed. -/
theorem combine_entry (m : Mem) (S : Addr) {j : Nat} (hj : j < 4) (x : Byte) :
    (pl S j 0 m x.toNat).setWidth 32 ||| (pl S j 1 m x.toNat).setWidth 32 <<< 8 |||
        (pl S j 2 m x.toNat).setWidth 32 <<< 16 ||| (pl S j 3 m x.toNat).setWidth 32 <<< 24 =
      sEntry (scheduleAt m S) j x := by
  refine word_ext fun b hb => ?_
  rw [byte_of_le4 _ _ _ _ hb, sEntry_byte _ _ hj hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `punpcklwd` of a value with itself, then `pshufd 0`: its low word in every word. -/
theorem bcast_low (v : BitVec 128) (b : Byte) (h : dword v 0 = b.setWidth 32) :
    shufDwords (XBinOp.eval .punpcklwd v v) 0 = bcast b := by
  refine ext_word fun i hi => ?_
  rw [word_eq_dword _ hi, show shufDwords (XBinOp.eval .punpcklwd v v) 0 =
      ofDwords (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0)
        (dword (XBinOp.eval .punpcklwd v v) 0) (dword (XBinOp.eval .punpcklwd v v) 0) from rfl]
  have d0 : dword (XBinOp.eval .punpcklwd v v) 0 = word v 0 ++ word v 0 := by
    rw [dword_words]
    simp only [XBinOp.eval, word_ofWords _ (show 2 * 0 + 1 < 8 by decide), word_ofWords _ (show 2 * 0 < 8 by decide)]
    rfl
  have w0 : word v 0 = b.setWidth 16 := by
    rw [word_eq_dword _ (by decide), show 0 / 2 = 0 from rfl, h]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]; omega
  have hd : ∀ k < 4, dword (ofDwords (word v 0 ++ word v 0) (word v 0 ++ word v 0) (word v 0 ++ word v 0)
      (word v 0 ++ word v 0)) k = word v 0 ++ word v 0 := by
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp
  rw [d0, hd _ (by omega), bcast, word_ofWords _ hi, w0]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  split <;> rename_i h <;> rcases (by omega : i % 2 = 0 ∨ i % 2 = 1) with e | e <;> simp [e] at h ⊢ <;>
    omega

end VG.Proof.Blowfish.X86_64
