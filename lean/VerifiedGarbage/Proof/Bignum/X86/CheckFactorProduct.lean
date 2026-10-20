module

public import VerifiedGarbage.Impl.Bignum.X86.CheckFactorProduct
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Proof.Bignum.X86.WideLoop
import VerifiedGarbage.Proof.Bignum.X86.WideProductWords
import VerifiedGarbage.Proof.Dsa.X86.Checks

/-! # Factor multiplication is checked without truncation or secret branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 VG.Proof.Ecdsa.X86

theorem checkFactorProduct_ok {s : State} {base : Addr} {bytes n product p q modulus mult : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (L : WideLayout (2 * n) bytes product p q mult)
    (hm : modulus + 16 * n ≤ bytes)
    (mp : modulus + 16 * n ≤ product ∨ product + 4 * (4 * n + 1) ≤ modulus)
    (mm : modulus + 16 * n ≤ mult ∨ mult + 4 ≤ modulus) :
    WP isa (checkFactorProduct n product p q modulus mult) s fun t =>
      t.gpr .edx = mask32 (wordsVal s.mem base p n * wordsVal s.mem base q n = wordsVal s.mem base modulus (2 * n)) ∧
      Outs base [(product, 4 * (2 * (2 * n) + 1)), (mult, 4)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold checkFactorProduct
  refine WP.seq (WP.mono (wideProductWords_ok hs hn L) fun u ⟨V, O, K⟩ => ?_)
  have N : wordsVal u.mem base modulus (2 * n) = wordsVal s.mem base modulus (2 * n) := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · have := hs.nowrap; omega
  refine WP.mono (equal_ok (2 * n) (hs.of_keeps K (by decide)) (by omega)
    (by have := L.outBound; omega) (by omega)) fun t ⟨E, Kt, Mt⟩ => ?_
  exact ⟨by rw [E, V, N], by rw [Mt]; exact O, K.trans Kt⟩

end VG.Proof.Bignum.X86
