module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH domain validation: subtract one from an odd multiword integer -/

@[expose] public section

namespace VG.Proof.Ffdh

open VG VG.Proof.Bignum

/-- An odd number's low word less one. -/
theorem wv_dec (m : Mem) (G : Addr) {d n : Nat} (hn : 1 ≤ n) (hodd : wv m G d n % 2 = 1)
    (hd : d + 8 * n ≤ 2 ^ 64) :
    wv (m.writeW (off G d) (word m G d - 1)) G d n = wv m G d n - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega_arith⟩
  have o := writeW_outside m G (d := d) (word m G d - 1) (by omega_arith)
  have hw : (word m G d).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hn, Nat.mod_mod_of_dvd _ (by decide)]; exact hodd
  rw [wv_add, wv_add, o.wv (d := d + 8 * 1) (k := k) (Or.inr (by omega_arith)) (by omega_arith)]
  have e : ∀ mm : Mem, wv mm G d 1 = (word mm G d).toNat := fun mm => by simp [wv]
  rw [e, e, word_writeW_self, BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl]
  have := (word m G d).isLt
  omega_arith

end VG.Proof.Ffdh
