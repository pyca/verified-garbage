module
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy

import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnVerified
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
meta import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT

/-! # `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx` meet `mulLazyContract` -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Proof.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)
open VG.Proof.MlKem.X86_64

/-- `mulBase_ok` without `[b] < m`: the baseline is lazy too. -/
theorem mulBaseLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 b)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa mulBase s fun t =>
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  unfold mulBase
  refine WP.seq (WP.mono (fnHead_ok hs hdi hH hZ ho ha hb hdx hcx h8)
    fun s₁ ⟨hbx, h11, h9, h10, h8₁, h12, h15, hsi₁, hm₁, k₁, sv⟩ => ?_)
  rw [← hm₁] at hinv
  have hs₁ := hs.congr k₁.2.2
  refine WP.seq (WP.mono (BaseSquare.tail_ok hs₁ hZ hw hw' ho ha hb ho1 ho2 ha1 ha2 hb1 hb2 hbx h11 h9 h10 h8₁ h12
    h15 hsi₁ hinv) fun s₂ ⟨_, _, heq, har, k₂, hx₂⟩ => ?_)
  refine WP.mono (unsaves_ok (sv.of_stashed hx₂)) fun t ⟨rs, mt, _, k₃⟩ => ?_
  rw [hm₁] at heq har
  rw [← mt] at heq har
  exact ⟨heq, har, ((k₁.trans k₂).trans k₃).mono (by decide), rs⟩

end VG.Proof.Bignum.X86_64.MontFn
