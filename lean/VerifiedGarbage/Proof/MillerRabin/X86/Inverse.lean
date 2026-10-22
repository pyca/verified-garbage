module

public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Mont.X86.Loop
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # Reuse the shared 64-bit Montgomery inverse on the 32-bit target -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt wordAt)

theorem candidate_words (m : Mem) (base : Addr) (w j : Nat) :
    numAt m base w j = val32 m base (arrAt w j) (2 * w) := by
  unfold numAt
  rw [read_eq_wordsVal, wordsVal_eq_val32]

theorem candidate_value (m : Mem) (base : Addr) (w : Nat) :
    numAt m base w 0 = val32 m base 256 (2 * w) := by
  simpa only [arrAt, VG.Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero] using candidate_words m base w 0

/-- No second inverse computation is needed: the existing kernel consumes
the low word of the inverse already prepared by the caller. -/
theorem inverse32 {m : Mem} {base : Addr} {w : Nat} (hw : 0 < w)
    (h : ((m.readW (base + BitVec.ofNat 64 (arrAt w 0)) 64).toNat *
      (wordAt m base VG.Spec.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0) :
    (val32 m base 256 (2 * w) * w32 m base 56 + 1) % 2 ^ 32 = 0 := by
  let M : VG.Impl.Mont.Mod :=
    { n := w, mo := 256, tmp := 0, minv := wordAt m base VG.Spec.Rsa.Mont.minvWord }
  have low := VG.Proof.Mont.X86.minv32_inv (M := M) h
  have lo : (VG.Impl.Mont.X86.minv32 M).toNat = w32 m base 56 := by
    change ((m.readW (base + BitVec.ofNat 64 56) 64).setWidth 32).toNat = _
    rw [VG.Proof.Rc2.Word32.read64_pair, BitVec.setWidth_append_eq_right]
  rw [lo] at low
  have low' : ((word m base 256).toNat * w32 m base 56 + 1) % 2 ^ 32 = 0 := by
    simpa only [arrAt, VG.Spec.Rsa.Mont.hdrBytes, Nat.zero_mul, Nat.add_zero, word] using low
  have lowWord : (word m base 256).toNat % 2 ^ 32 = w32 m base 256 := by
    rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base 256) 32).isLt]
  obtain ⟨k, hk⟩ : ∃ k, 2 * w = k + 1 := ⟨2 * w - 1, by omega⟩
  have wholeWord : val32 m base 256 (2 * w) % 2 ^ 32 = w32 m base 256 := by
    rw [hk, val32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base 256) 32).isLt]
  rw [Nat.add_mod, Nat.mul_mod, wholeWord]
  rw [Nat.add_mod, Nat.mul_mod, lowWord] at low'
  exact low'

end VG.Proof.MillerRabin.X86
