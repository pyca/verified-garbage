module
public import VerifiedGarbage.Proof.Bignum.X86.WideLoop

import VerifiedGarbage.Proof.Bignum.X86.WideProduct
import VerifiedGarbage.Proof.Bignum.WideProductValue
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Full products in the RSA API's 64-bit word representation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem wideProductWords_ok {s : State} {base : Addr} {bytes n out a b mult : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (L : WideLayout (2 * n) bytes out a b mult) :
    WP isa (wideProduct (2 * n) out a b mult) s fun t =>
      wordsVal t.mem base out (2 * n) = wordsVal s.mem base a n * wordsVal s.mem base b n ∧
      Outs base [(out, 4 * (2 * (2 * n) + 1)), (mult, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (wideProduct_ok hs (by omega) L) fun t ⟨V, O, K⟩ => ?_
  refine ⟨?_, O, K⟩
  simpa only [wordsVal_eq_val32] using wide_product_value V

end VG.Proof.Bignum.X86
