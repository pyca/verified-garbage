import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer
import VerifiedGarbage.Proof.Aes.X86_64.Ctr32
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32

/-!
# Counter templates and 32-bit wraparound

Only the final four bytes of each copied counter are rewritten. Their
arithmetic is modulo 2^32, including batches that cross the wrap boundary.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Spec.Gcm (blockAt inc32)

def advanceCounter (m : Mem) (p : Addr) (n : Nat) : Mem :=
  m.writeW (p + BitVec.ofNat 64 12)
    (bswap32 (bswap32 (m.readW (p + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n))

theorem advanceCounter_ok (m : Mem) (p : Addr) (n : Nat) :
    blockAt (advanceCounter m p n) p = Nat.repeat inc32 n (blockAt m p) := by
  apply VG.Proof.Aes.X86_64.ctr_after
  intro k hk
  simp only [advanceCounter, VG.Proof.Aes.X86_64.writeW_apply,
    VG.Proof.Aes.X86_64.off_toNat p (i := k) (j := 12) (by omega) (by omega)]
  by_cases h : k < 12
  · simp only [ite_eq_right (show ¬ 12 ≤ k by omega),
      ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega), ite_eq_left h]
  · simp only [ite_eq_left (show 12 ≤ k by omega),
      ite_eq_left (show k - 12 < 32 / 8 by omega), ite_eq_right h, BitVec.setWidth_eq]
    rw [BitVec.setWidth_ofNat_of_le (by decide)]

/-- Copying all sixteen bytes keeps the counter's big-endian value. -/
theorem copyCounter_ok (m : Mem) (src dst : Addr) :
    blockAt (m.writeW dst (m.readW src 128)) dst = blockAt m src := by
  rw [VG.Proof.Gcm.X86_64.blockAt_eq, Mem.readW_writeW_self m dst 16 _ (by decide),
    VG.Proof.Gcm.X86_64.blockAt_eq]

/-- The native low-counter word can be read from a copied template. -/
theorem copyCounter_low (m : Mem) (src dst : Addr) :
    (m.writeW dst (m.readW src 128)).readW (dst + BitVec.ofNat 64 12) 32 =
      m.readW (src + BitVec.ofNat 64 12) 32 := by
  rw [readW_writeW_inside m dst (m.readW src 128) (k := 12) (n := 4) (by decide) (by decide),
    readW_extract m src (k := 12) (n := 4) (by decide)]

/-- One template, filled directly from the original numeric counter. -/
theorem counterTemplate_ok (m : Mem) (src dst : Addr) (n : Nat) :
    blockAt ((m.writeW dst (m.readW src 128)).writeW (dst + BitVec.ofNat 64 12)
      (bswap32 (bswap32 (m.readW (src + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 n))) dst =
        Nat.repeat inc32 n (blockAt m src) := by
  have h := advanceCounter_ok (m.writeW dst (m.readW src 128)) dst n
  simpa only [advanceCounter, copyCounter_low, copyCounter_ok] using h

theorem inc32_add (C : Spec.Gcm.Block) (n d : Nat) :
    Nat.repeat inc32 d (Nat.repeat inc32 n C) = Nat.repeat inc32 (n + d) C := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change inc32 (Nat.repeat inc32 d (Nat.repeat inc32 n C)) = inc32 (Nat.repeat inc32 (n + d) C)
    exact congrArg inc32 ih

/-- Refresh a template from the numeric counter while retaining its prefix. -/
theorem refreshCounter_ok (m : Mem) (p : Addr) (C : Spec.Gcm.Block) (n d : Nat)
    (h : blockAt m p = Nat.repeat inc32 n C) :
    blockAt (m.writeW (p + BitVec.ofNat 64 12)
      (bswap32 (C.extractLsb' 0 32 + BitVec.ofNat 32 (n + d)))) p =
        Nat.repeat inc32 (n + d) C := by
  have hc := advanceCounter_ok m p d
  rw [advanceCounter, VG.Proof.Aes.X86_64.icb_lo, h,
    VG.Proof.Aes.repeat_inc32_lo, BitVec.add_assoc, ← BitVec.ofNat_add] at hc
  exact hc.trans (inc32_add C n d)

end VG.Proof.Gcm.X86_64.StitchAvx8
