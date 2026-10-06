import VerifiedGarbage.Proof.Bignum.AArch64.CrtBack

/-!
# RSA with the CRT on AArch64: the computation for a valid modulus

`main`, from the header `entry` leaves, for a valid modulus: `privateCrt`'s
result (zeros if it is `none`) to `out` and whether it is `some` returned
(`crtMain_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

theorem crtMain_eq (mul : Nat → Nat → Nat → Prog isa) :
    Crt.main mul = seqs ((nSetup mul ++ primesSetup ++ checks) ++ (qPhase mul ++ pPhase mul ++ finish)) := by
  simp only [Crt.main, List.append_assoc]

/-- `main`, for a valid modulus: the result `r`, `some` exactly if the mask
is set. -/
theorem crtMain_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (Crt.main M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  rw [crtMain_eq]
  refine wp_seqs_append (by simp [nSetup]) (by simp [qPhase]) (WP.mono (front_ok M h hv)
    fun t₀ ⟨minv, mp, mq, hr⟩ => WP.mono (back_ok M h hv hr rfl) fun t ht => ⟨_, ht, ?_⟩)
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.AArch64
