module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMain
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCode
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowDispatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem pre_keep {s t : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hm : t.mem = s.mem) (hk : Keep [.x9] s t) :
    CrtPre t B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib := by
  have im : InScr B Z s.mem t.mem := by rw [hm]; exact InScr.refl _ _ _
  exact {
    scr := h.scr.congr hk.wr
    x0 := (hk.gpr .x0 (by decide)).trans h.x0
    z := h.z
    zk := h.zk
    k1 := h.k1
    k2 := h.k2
    hO := by simpa only [hm] using h.hO
    hN := by simpa only [hm] using h.hN
    hK := by simpa only [hm] using h.hK
    hIn := by simpa only [hm] using h.hIn
    hP := by simpa only [hm] using h.hP
    hPl := by simpa only [hm] using h.hPl
    hQ := by simpa only [hm] using h.hQ
    hQl := by simpa only [hm] using h.hQl
    hDp := by simpa only [hm] using h.hDp
    hDq := by simpa only [hm] using h.hDq
    hQi := by simpa only [hm] using h.hQi
    n := h.n.congrK im hk
    x := h.x.congrK im hk
    p := h.p.congrK im hk
    q := h.q.congrK im hk
    dp := h.dp.congrK im hk
    dq := h.dq.congrK im hk
    qi := h.qi.congrK im hk
    nl := h.nl
    xl := h.xl
    pbl := h.pbl
    qbl := h.qbl
    dpl := h.dpl
    dql := h.dql
    qil := h.qil
    pl1 := h.pl1
    pl2 := h.pl2
    ql1 := h.ql1
    ql2 := h.ql2
    out := by simpa only [hk.wr] using h.out
    outSep := h.outSep
  }

theorem lengthGuard_ok {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.lengthGuard) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 k >>> 7 ∧ t.mem = s.mem ∧ Keep [.x9] s t := by
  have hz := h.zk
  have hk := h.k1
  exact WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 k >>> 7 ∧ t.mem = s.mem)
    (by brun [VG.Impl.Rsa.AArch64.WindowFive.lengthGuard,h.x0,hdr_enc (show Public.sK < 32 by decide),
      h.scr.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega),h.hK])
    (by decide) (by decide) (by decide +kernel)) fun _ ⟨⟨hv,hm⟩,kk⟩ => ⟨hv,hm,kk⟩

theorem lengthGuard_zero {k : Nat} (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 k >>> 7 == (0 : BitVec 64)) = decide (k < 128) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hk,
    Nat.shiftRight_eq_div_pow]
  change k / 128 = 0 ↔ k < 128
  omega

theorem dispatch_ok (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr}
    {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (VG.Impl.Rsa.AArch64.WindowFive.dispatch W.code S.code M.mm) s fun t => ∃ Mk : Bool, MainPost s t B Z k op
      (if Mk then crtResult (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip dpb) (Spec.Rsa.os2ip dqb)
        (Spec.Rsa.os2ip qib) (Spec.Rsa.os2ip xb) else 0) Mk ∧
      (Mk = true ↔ Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb =
        Spec.Rsa.os2ip nb ∧ Spec.Rsa.os2ip qib < Spec.Rsa.os2ip pb) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.dispatch
  refine WP.seq (WP.mono (lengthGuard_ok h) fun t ⟨h9,hm,kk⟩ => ?_)
  have ht := pre_keep h hm kk
  have hk64 : k < 2 ^ 64 := by have := h.k2; omega
  have finish : ∀ u r c, MainPost t u B Z k op r c → MainPost s u B Z k op r c := by
    intro u r c hp
    exact ⟨hp.bytes,hp.x0,fun x hx ho => by rw [hp.frame x hx ho,hm],
      (kk.trans hp.keep).mono (by decide)⟩
  refine WP.ite (decide (k < 128)) (by rw [eval_zero,h9,lengthGuard_zero hk64]) ?_ ?_
  · intro _
    exact WP.mono (VG.Proof.Bignum.AArch64.crtMain_ok M ht hv)
      fun u ⟨c,hp,hi⟩ => ⟨c,finish u _ _ hp,hi⟩
  · intro hk
    have h128 : 128 ≤ k := by simpa using hk
    exact WP.mono (crtMain_ok W M S ht h128 hv)
      fun u ⟨c,hp,hi⟩ => ⟨c,finish u _ _ hp,hi⟩

end VG.Proof.Bignum.AArch64.WindowFive
