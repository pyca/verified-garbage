import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Tiled Montgomery squaring preserves the reduced-input contract. -/
theorem montSquare_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co ca o a : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.montSquare co ca) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.montSquare
  refine WP.seq (WP.mono (rawSquare_ok hs hdi hH hZ hwN hnN hw hv pa ha ha1 ha2) fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  exact AdxTiledProduct.redcFinish_ok hs hdi hH hZ hwN hnN hw hv po ho ho1 ho2 hinv
    (AdxTiledProduct.mul_lt_mont (wv_lt _ _ _ _) hB) hv₁ ho₁ k₁

end VG.Proof.Bignum.X86_64.AdxTiledSquare
