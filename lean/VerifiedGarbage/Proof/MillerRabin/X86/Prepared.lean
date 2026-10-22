module

public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts

/-! # Extract the operational facts directly from the shared preparation contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt wOf)

theorem width_low_word {m : Mem} {base : Addr} {w : Nat}
    (width : wOf m base = w) (small : w ≤ 128) :
    m.readW (off base 48) 32 = BitVec.ofNat 32 w := by
  have pair := word_eq_w32 m base 48
  change wOf m base = w32 m base 48 + 2 ^ 32 * w32 m base 52 at pair
  rw [width] at pair
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change w32 m base 48 = w
  omega

theorem round_facts_of {σ : State} {base : Addr} {bytes w : Nat} {len : BitVec 32}
    (size : bytes = len.toNat * 8) (width : wOf σ.mem base = w)
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact σ.mem base len.toNat)
    (prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact σ.mem base)
    (length : σ.mem.readW (off (byteAddr (σ.gpr .esp)) VG.Impl.MillerRabin.X86.savedLength) 32 = len) :
    RoundFacts σ base bytes w := by
  rcases layout with ⟨_, _, lower, upper, fit, _⟩
  rw [width] at lower upper fit
  have fits : arrAt w 28 ≤ bytes := by
    change arrAt w 28 ≤ 8 * len.toNat at fit
    simpa only [size, Nat.mul_comm] using fit
  unfold Spec.MillerRabin.Prepared at prepared
  rw [width] at prepared
  rcases prepared with ⟨c3, odd, inverse, witness, one, _, _, _⟩
  simp only [Spec.MillerRabin.compact, candidate_value] at c3 odd witness one
  have positive : 0 < val32 σ.mem base 256 (2 * w) := by omega
  exact ⟨lower, upper, fits, width_low_word width upper, ⟨len, size, length⟩,
    inverse32 (by omega) inverse, odd, by rw [one]; exact Nat.mod_lt _ positive, witness⟩

theorem prepared_tail {m : Mem} {base : Addr} {w : Nat}
    (width : wOf m base = w)
    (prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact m base) :
    m.readW (off base (arrAt w 27 + 8 * w)) 64 =
      BitVec.twoPow 64 ((Spec.Rsa.splitTwos (val32 m base 256 (2 * w) - 1)).1 % 64) := by
  unfold Spec.MillerRabin.Prepared at prepared
  rw [width] at prepared
  rcases prepared with ⟨_, _, _, _, _, _, _, tail⟩
  simpa only [Spec.MillerRabin.compact, candidate_value] using tail

end VG.Proof.MillerRabin.X86
