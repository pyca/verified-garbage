module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtMain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtBackPc
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: the computation for a valid modulus

`main` with `pc`, from the header `entry` leaves, for a valid modulus:
`privateCrt`'s result to `out` if `pre` holds `R² mod n`, `R_p mod p` and
`R_q mod q` (`PreVals`), and whether the mask is set returned whatever it
holds (`crtMainPc_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- `pre` at `P` holds `R² mod N` at word `w`, then `R_p mod p` and `R_q mod q`
(`w_p` and `w_q` words). -/
def PreVals (m : Mem) (P : Addr) (w wp wq N p q : Nat) : Prop :=
  wv m P (8 * w) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧ wv m P (8 * (2 * w)) wp = 2 ^ (64 * wp) % p ∧
    wv m P (8 * (2 * w + wp)) wq = 2 ^ (64 * wq) % q

theorem NReady.weak {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N C : Nat} {ok ok' : Prop}
    (h : NReady s t B Z w minv N C ok) (f : ok' → ok) : NReady s t B Z w minv N C ok' :=
  ⟨h.good, h.nv.weak f, fun h' => h.xm (f h'), h.msk, h.hfix, h.iscr, h.keep⟩

theorem crtMain_pc (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) :
    Crt.main mul ex true = seqs ((nSetup mul true ++ primesSetup ++ checks) ++
      (qPhase mul ex true ++ pPhase mul ex true ++ finish)) := by
  simp only [Crt.main, List.append_assoc]

/-- `main` with `pc`, for a valid modulus: the result `r` if `pre` holds its
values, `some` exactly if the mask is set. -/
theorem crtMainPc_ok (M : Mont) (E : CrtExpL M) {s : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {Pr : Addr} {W : Nat}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) (hpre : PreSrc s B Z Pr W)
    (hW : 2 * ((k + 7) / 8) + wsWords pl + wsWords ql ≤ W) :
    WP isa (Crt.main M.mm E.code true) s fun t => ∃ Mk : Bool, CrtPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk
      (PreVals s.mem Pr ((k + 7) / 8) (wsWords pl) (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
        (Spec.Rsa.os2ip qb)) ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  rw [crtMain_pc]
  refine wp_seqs_append (by simp [nSetup]) (by simp [qPhase]) (wp_seqs_append (by simp [nSetup])
    (by simp [checks]) (wp_seqs_append (by simp [nSetup]) (by simp [primesSetup])
      (WP.mono (nPartPc_ok M h hv hpre (by omega)) fun _ ⟨minv, hr⟩ =>
        WP.mono (setupPart_ok h (hr.weak (ok' := PreVals s.mem Pr ((k + 7) / 8) (wsWords pl)
          (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) fun hp' => hp'.1))
          fun _ ⟨_, _, hr'⟩ =>
          WP.mono (checksPart_ok h hv hr') fun t₀ ⟨mp, mq, hr''⟩ => ?_)))
  rw [List.append_assoc]
  refine wp_seqs_append (by simp [qPhase]) (by simp [pPhase]) (WP.mono (qPartPc_ok M E h hv hr'' rfl hpre hW
    fun hp' => hp'.2.2) fun _ hq => wp_seqs_append (by simp [pPhase]) (by simp [finish])
      (WP.mono (pPartPc_ok M E h hv hq rfl hpre (by omega) fun hp' => hp'.2.1) fun _ hp =>
        WP.mono (finPart_ok h hv hp rfl) fun t ht => ⟨_, ht, ?_⟩))
  simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

end VG.Proof.Bignum.X86_64
