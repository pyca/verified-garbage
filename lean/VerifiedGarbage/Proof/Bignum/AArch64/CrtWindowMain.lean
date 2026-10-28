module
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.CrtResult

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBack

/-!
# RSA with the CRT on AArch64: the computation for a valid modulus

`main`, from the header `entry` leaves, for a valid modulus: `privateCrt`'s
result (zeros if it is `none`) to `out` and whether it is `some` returned
(`crtMain_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

theorem crtMain_eq (window : Prog isa) (select : Prog isa) (mul : Nat → Nat → Nat → Prog isa) :
    VG.Impl.Rsa.AArch64.WindowFive.main window select mul = seqs ((nSetup mul ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ checks) ++ (VG.Impl.Rsa.AArch64.WindowFive.qPhase window mul select ++ VG.Impl.Rsa.AArch64.WindowFive.pPhase window select mul ++ finish)) := by
  simp only [VG.Impl.Rsa.AArch64.WindowFive.main, List.append_assoc]

/-- `main`, for a valid modulus: the result `r`, `some` exactly if the mask
is set. -/
theorem crtMain_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hk : 128 ≤ k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.main W.code S.code M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  have hwide : CrtWindowFive.offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + CrtWindowFive.tabBytes32 (wsWords ql) ≤ Z :=
    (CrtWindowFive.prime_scratch32_fits hk h.pl2 h.ql2).trans (by have := h.zk; omega)
  rw [crtMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (WP.mono (front_ok M h hwide hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ => WP.mono (back_ok W M S h hwide hv hr rfl) fun t ht => ⟨_, ht, ?_⟩)
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.AArch64.WindowFive
