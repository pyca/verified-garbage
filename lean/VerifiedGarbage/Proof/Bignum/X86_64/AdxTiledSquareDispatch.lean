import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareMont
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareFinish
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledSquareDispatch
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareCT

/-! ## AdxTiledSquareMont -/
section

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

end

/-! ## AdxTiledSquareDispatch -/
section

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem alignedChoice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.alignedChoice o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.alignedChoice
  refine WP.seq (WP.mono (AdxSquare.redcTest_ok hs hdi hH hZ (by omega)) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : w%8=0
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (montSquare_ok hs₁ hdi₁ hH hZ (by omega : w=8*(w/8)) (by omega) hw' (hH.ops3 ho ha ha) (.head _) (.tail _ (.head _)) ho ha ho1 ho2 ha1 ha2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (AdxSquare.montSquare_ok hs₁ hdi₁ hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB) post)

theorem choice_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledSquare.choice o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledSquare.choice
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w a) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h8 : SizeOk w
  · refine WP.ite true (by simp [eval,hz,h8]) (fun _ => WP.mono
      (alignedChoice_ok hs₁ hdi₁ hH hZ hw hw' ho ha ho1 ho2 ha1 ha2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval,hz,h8]) (by simp) (fun _ =>
      WP.mono (montMulAdx_ok hs₁ hdi₁ hH hZ hw hw' ho ha ha ho1 ho2 ha1 ha2 ha1 ha2 hinv hB) post)

end VG.Proof.Bignum.X86_64.AdxTiledSquare

end
