module

public import VerifiedGarbage.Proof.MillerRabin.X86.Inverse
public import VerifiedGarbage.Proof.MillerRabin.X86.StageMemory
public import VerifiedGarbage.Proof.MillerRabin.Words
public import VerifiedGarbage.Proof.MillerRabin.Math

/-! # Reuse the shared correspondence between word digits and exponent windows -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)

abbrev exponentWord (σ : State) (base : Addr) (w i : Nat) : BitVec 32 :=
  σ.mem.readW (off base (arrAt w 27 + 4 * i)) 32

abbrev shiftedWord (σ : State) (base : Addr) (w i j : Nat) : BitVec 32 :=
  exponentWord σ base w i <<< (4 * j)

theorem word_digit {σ : State} {base : Addr} {w i j : Nat} (hi : i < 2 * w) (hj : j < 8) :
    shiftedWord σ base w i j >>> 28 = BitVec.ofNat 32
      (numAt σ.mem base w 27 / 16 ^ (8 * i + 7 - j) % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.MillerRabin.Math.shl_shr28 _ hj]
  have word := VG.Proof.MillerRabin.val32_word' σ.mem base hi (d := arrAt w 27)
  change (exponentWord σ base w i).toNat = _ at word
  rw [word, ← candidate_words, show 28 - 4 * j = 4 * (7 - j) by omega,
    VG.Proof.MillerRabin.Math.digit_word _ _ _ (by omega), BitVec.toNat_ofNat]
  rw [show 8 * i + (7 - j) = 8 * i + 7 - j by omega]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 16))
    (by decide : 16 < 2 ^ 32))).symm

theorem shifted_word_next (σ : State) (base : Addr) (w i j : Nat) :
    shiftedWord σ base w i j <<< 4 = shiftedWord σ base w i (j + 1) := by
  unfold shiftedWord
  rw [← BitVec.shiftLeft_add]
  congr 1

end VG.Proof.MillerRabin.X86
