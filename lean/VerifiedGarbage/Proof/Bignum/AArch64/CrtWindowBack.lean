module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtBack
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFront
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
public import VerifiedGarbage.Proof.Bignum.CrtResult
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBody
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.CrtWindowPRanges

/-!
# RSA with the CRT on AArch64: from the checks to the result

`q`'s phase, `p`'s, and `m = m_q + q h` written out masked (`back_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32 xRange32 px_hdr px_above)
open VG.Proof.MlKem.AArch64 (Keep)

/-- After `q`'s phase: as after the checks, and `m_q` in `q`'s `aY`. -/
structure QReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (dqb : List Byte) (Mk : Bool) : Prop extends CrtReady s t B Z w pl ql minv mp mq N C P Q Mk where
  qlt : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q

/-- `q`'s phase, from the checks. -/
theorem qPart_ok (W : Window) (M : Mont) (S : Selector) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code)) t₀ fun t => QReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb)
      (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk := by
  -- `qPart_gen` with this exponentiation, on the same states (`offQ32` is `offQ`).
  rw [qPhase_eq]
  exact WP.mono (VG.Proof.Bignum.AArch64.qPart_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) h hv ⟨hr.good, hr.nv, hr.xm, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.pxv, hr.pmask, hr.qws, hr.qxv, hr.hfix, hr.iscr,
      hr.keep⟩ hMk)
    fun _ r => ⟨⟨r.good, r.nv, r.xm, r.msk, r.wsP, r.wsQ, r.pws, r.pxv, r.pmask, r.qws, r.qxv, r.hfix, r.iscr, r.keep⟩, r.qlt, r.qval⟩


/-- After `p`'s phase: `h` in `p`'s `aY`, `m_q` in `q`'s. -/
structure PDone (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (C P Q QI : Nat)
    (dpb dqb : List Byte) (Mk : Bool) : Prop where
  good : Good t B Z w minv
  msk : word t.mem B (8 * Public.sMask) = mask Mk
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  qn : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = if Mk then Q else 3
  qlt : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) < if Mk then Q else 3
  qval : Mk = true →
    wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aY) (wsWords ql) = C ^ Spec.Rsa.os2ip dqb % Q
  plt : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) < if Mk then P else 3
  pval : Mk = true → ∃ a b, a % P = C ^ Spec.Rsa.os2ip dpb * 2 ^ (64 * wsWords pl) % P ∧
    b % P = C ^ Spec.Rsa.os2ip dqb % Q * 2 ^ (64 * wsWords pl) % P ∧ b < P ∧
    wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aY) (wsWords pl) * 2 ^ (64 * wsWords pl) % P =
      (a + P - b) % P * QI % P
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- `p`'s phase, from `q`'s. -/
theorem pPart_ok (W : Window) (M : Mont) (S : Selector) {s t₁ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : QReady s t₁ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) t₁ fun t => PDone s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk := by
  -- `pPart_gen` with this exponentiation, on the same states (`offQ32` is `offQ`).
  rw [pPhase_eq]
  exact WP.mono (VG.Proof.Bignum.AArch64.pPart_gen M (fun sd slen => [VG.Impl.Rsa.AArch64.WindowFive.expLoop W.code M.mm S.code sd slen])
    (@powPhase_ok W M S) h hv ⟨⟨hr.good, hr.nv, hr.xm, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.pxv, hr.pmask, hr.qws, hr.qxv, hr.hfix, hr.iscr,
      hr.keep⟩, hr.qlt, hr.qval⟩ hMk)
    fun _ r => ⟨r.good, r.msk, r.wsP, r.wsQ, r.pws, r.qws, r.qn, r.qlt, r.qval, r.plt, r.pval, r.hfix, r.iscr, r.keep⟩


/-- `m = m_q + q h` written out masked, from `p`'s phase. -/
theorem finPart_ok {s t₂ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (_hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PDone s t₂ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) dpb dqb Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs finish) t₂ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk :=
  -- `finish` and its proof are the same (`offQ32` is `offQ`).
  VG.Proof.Bignum.AArch64.finPart_ok h hv ⟨hr.good, hr.msk, hr.wsP, hr.wsQ, hr.pws, hr.qws, hr.qn, hr.qlt, hr.qval,
    hr.plt, hr.pval, hr.hfix, hr.iscr, hr.keep⟩ hMk


/-- From the checks: both phases, and `m = m_q + q h` written out masked. -/
theorem back_ok (W : Window) (M : Mont) (S : Selector) {s t₀ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64} {Mk : Bool}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : CrtReady s t₀ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) Mk)
    (hMk : Mk = keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
      (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs (VG.Impl.Rsa.AArch64.WindowFive.qPhase W.code M.mm S.code ++ VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm ++ finish)) t₀ fun t => MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk := by
  rw [List.append_assoc]
  exact wp_seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.qPhase]) (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (WP.mono (qPart_ok W M S h hwide hv hr hMk) fun _ hq =>
    wp_seqs_append (by simp [VG.Impl.Rsa.AArch64.WindowFive.pPhase]) (by simp [finish]) (WP.mono (pPart_ok W M S h hwide hv hq hMk) fun _ hp =>
      finPart_ok h hwide hv hp hMk))

end VG.Proof.Bignum.AArch64.WindowFive
