module

public import VerifiedGarbage.Proof.Sm4.Rounds
public import VerifiedGarbage.TCB.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Sm4.SboxTable
meta import VerifiedGarbage.Proof.Sm4.Rounds
meta import VerifiedGarbage.TCB.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Sm4.SboxTable

-- separate module: SM4E's and SM4EKEY's rounds, for each function that uses the instructions

/-!
# SM4E and SM4EKEY are four rounds of the specification

`sm4E_eq`, `sm4EKey_eq`: on a state of four words and four round keys (or
constants), FEAT_SM4's instructions compute a `quad` (`Proof/Sm4/Rounds.lean`)
of the specification's rounds, of encryption and of the key schedule.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Sm4e

open VG VG.AArch64 VG.Spec.Sm4 VG.Proof.Sm4
open VG.Impl.Sm4 (Lin)

/-- Arm's `Sbox` is the specification's S-box, on every byte: against the
specification's as a literal table (`Proof/Sm4/SboxTable.lean`). -/
theorem sbox_lt : ∀ n < 256, (sm4Sbox (BitVec.ofNat 8 n)).toNat = sboxN n := by lit_decide

theorem sbox_eq (x : BitVec 8) : sm4Sbox x = sbox.getD x.toNat 0 := by
  have h := sbox_lt x.toNat x.isLt
  rw [sboxN_eq x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact BitVec.eq_of_toNat_eq h

/-- The S-boxes of a word are `tau`. -/
theorem sboxWord_eq (x : Word) : sm4SboxWord x = tau x := by
  simp only [sm4SboxWord, tau, sbox_eq]
  rfl

/-- One iteration of the instructions' loop is a round of the specification:
the words move down, and the last is the new one. -/
theorem step_eq (lin : Word → Word) (a b c d k : Word) :
    sm4Step lin (ofVWords a b c d) k = ofVWords b c d (a ^^^ lin (tau (b ^^^ c ^^^ d ^^^ k))) := by
  simp only [sm4Step, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3, sboxWord_eq]
  rw [BitVec.xor_comm _ a, show d ^^^ c ^^^ b ^^^ k = b ^^^ c ^^^ d ^^^ k by ac_rfl]

/-- The vector of the words `x 0 … x 3`. -/
def vec (x : Nat → Word) : BitVec 128 := ofVWords (x 0) (x 1) (x 2) (x 3)

/-- The four iterations are a `quad`: with the linear transformation of `l`,
from the words `x`, with the round keys (or constants) `K (4 m) … K (4 m + 3)`. -/
theorem steps_eq (l : Lin) (K : Nat → Word) (m : Nat) (x : Nat → Word) :
    sm4Steps l.fn (vec x) (ofVWords (K (4 * m)) (K (4 * m + 1)) (K (4 * m + 2)) (K (4 * m + 3))) =
      vec (quad l K m x) := by
  simp only [sm4Steps, vec, step_eq, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3,
    quad, sround, Lin.t]
  simp

/-- SM4E is four rounds of encryption. -/
theorem sm4E_eq (K : Nat → Word) (m : Nat) (x : Nat → Word) :
    sm4E (vec x) (ofVWords (K (4 * m)) (K (4 * m + 1)) (K (4 * m + 2)) (K (4 * m + 3))) =
      vec (quad .enc K m x) := steps_eq .enc K m x

/-- SM4EKEY is four rounds of the key schedule. -/
theorem sm4EKey_eq (K : Nat → Word) (m : Nat) (x : Nat → Word) :
    sm4EKey (vec x) (ofVWords (K (4 * m)) (K (4 * m + 1)) (K (4 * m + 2)) (K (4 * m + 3))) =
      vec (quad .key K m x) := steps_eq .key K m x

end VG.Proof.Sm4.AArch64.Sm4e
