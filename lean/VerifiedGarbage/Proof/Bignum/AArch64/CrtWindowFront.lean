module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtFront
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowSetup
public import VerifiedGarbage.Proof.Bignum.CrtHdr
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSA with the CRT on AArch64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : word t.mem (off B (offP w)) (8 * sMaskX) = mask M
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  qxv : XVals t B (offQ32 w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : NReady s t B Z w minv N C
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ32 w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ32 w pl) (wsWords ql) mq
  pv : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (off B (offQ32 w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hr : NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs VG.Impl.Rsa.AArch64.WindowFive.primesSetup) t₃ fun t => ∃ mp mq, PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := hwide
  have htp : tabBytes (wsWords pl) ≤ tabBytes32 (wsWords pl) := by unfold tabBytes tabBytes32; omega
  have htq : tabBytes (wsWords ql) ≤ tabBytes32 (wsWords ql) := by unfold tabBytes tabBytes32; omega
  have ewp : wsTab (wsWords pl) = tabBytes32 (wsWords pl) := rfl
  have ewq : wsTab (wsWords ql) = tabBytes32 (wsWords ql) := rfl
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ32 at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega_arith) (by omega_arith) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega_arith) h.ql1 (by have := h.ql2; omega_arith))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  have kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), slot (wsWords pl) 8 + tabBytes32 (wsWords pl) + slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega_arith,
        Or.inr (by simp only [sWsP, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega_arith,
        Or.inr (by simp only [sWsQ, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ32 at hZq; omega_arith,
        Or.inl (by simp only [offP]; omega_arith)⟩
  have hnv₄ : ∀ j < 8, wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₃.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj =>
    f₄.wv_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) hj
      have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) hj; omega)
  have hnw₄ : word t₄.mem B (slot ((k + 7) / 8) Public.aN) = word t₃.mem B (slot ((k + 7) / 8) Public.aN) :=
    f₄.word_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
      have := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide); omega)
  have hM₄ : word t₄.mem B (8 * Public.sMask) = word t₃.mem B (8 * Public.sMask) := by
    refine f₄.word_eq (fun r hr => ?_) (by unfold Public.sMask sFn; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (by simp only [Public.sMask, sWsP, sFn]; omega_arith)
    · exact Or.inl (by simp only [Public.sMask, sWsQ, sFn]; omega_arith)
    · exact Or.inl (by simp only [offP, Public.sMask, sFn]; omega_arith)
  refine ⟨mp, mq, ⟨hg₄, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hsP₄, hsQ₄, hwp₄, hwq₄, hp₄, hc₄, hq₄⟩
  · rw [hnv₄ _ (by decide)]; exact hr.nv.n
  · rw [hnw₄]; exact hr.nv.inv
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2lt
  · rw [hnv₄ _ (by decide)]; exact hr.nv.one
  · rw [hnv₄ _ (by decide)]; exact hr.xm
  · rw [hM₄]; exact hr.msk
  · exact hr.hfix.trans (HFix.of_frm f₄ fun r hr => (kf₄ r hr).1)
  · exact hr.iscr.trans (InScr.of_frm f₄ fun r hr => (kf₄ r hr).2.1)
  · exact (hr.keep.trans k₄).mono (by decide)

/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs checks) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := hwide
  have htp : tabBytes (wsWords pl) ≤ tabBytes32 (wsWords pl) := by unfold tabBytes tabBytes32; omega
  have htq : tabBytes (wsWords ql) ≤ tabBytes32 (wsWords ql) := by unfold tabBytes tabBytes32; omega
  have ewp : wsTab (wsWords pl) = tabBytes32 (wsWords pl) := rfl
  have ewq : wsTab (wsWords ql) = tabBytes32 (wsWords ql) := rfl
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ32 at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_arith
  refine WP.mono (checks_ok hr.n.good (by omega_arith) (by omega_arith) (le_refl _) (by unfold offQ32 tabBytes32 wsTab tabBytes at *; omega_arith)
    (by unfold offQ32 tabBytes32 wsTab tabBytes at *; omega_arith) hwp2 (wsWords_le (by have := h.pl2; omega_arith) (by omega_arith)) hwq2
    (wsWords_le (by have := h.ql2; omega_arith) (by omega_arith)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd)
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  have kf₅ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), slot (wsWords pl) 8), (offQ32 ((k + 7) / 8) pl, slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ32 at hZq; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ32]; omega_arith), by simp only; omega_arith⟩
  have hnv₅ : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj h1 h2 => by
    have := slot_le (w := (k + 7) / 8) hj
    have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
    have := accs_le ((k + 7) / 8)
    have : slot ((k + 7) / 8) j + 8 * ((k + 7) / 8) ≤ slot ((k + 7) / 8) Public.aAcc ∨
        slot ((k + 7) / 8) Public.aAcc + 8 * (2 * ((k + 7) / 8) + 2) ≤ slot ((k + 7) / 8) j := by
      unfold slot Public.aAcc
      rw [show Public.aAcc = 2 from rfl] at h1
      rw [show Public.aTmp = 3 from rfl] at h2
      rcases (show j < 2 ∨ 4 ≤ j by omega_arith) with hj' | hj'
      · left; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show j + 1 ≤ 2 by omega_arith)
        rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
      · right; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show 4 ≤ j by omega_arith); omega_arith
    refine f₅.wv_eq (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only; omega_arith
    · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
    · exact Or.inl (by simp only; omega_arith)
    · exact Or.inl (by simp only [offQ32]; omega_arith)
  refine ⟨mp', mq', hg, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hMt, hsPt, hsQt, hwpt, hxpt, hmpt, hwqt, hxqt, ?_, ?_,
    (hr.n.keep.trans k₅).mono (by decide)⟩
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.n
  · have := accs_le ((k + 7) / 8)
    have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
    have hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have : slot ((k + 7) / 8) Public.aN + 8 ≤ slot ((k + 7) / 8) Public.aAcc := by
        unfold slot Public.aN Public.aAcc; omega_arith
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inl (by simp only [offQ32]; omega_arith)) (by omega_arith)]
    exact hr.n.nv.inv
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2lt
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.one
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.xm
  · exact hr.n.hfix.trans (HFix.of_frm f₅ fun r hr => (kf₅ r hr).1)
  · exact hr.n.iscr.trans (InScr.of_frm f₅ fun r hr => (kf₅ r hr).2)

/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hwide : offQ32 ((k + 7) / 8) pl + slot (wsWords ql) 8 + tabBytes32 (wsWords ql) ≤ Z)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm ++ VG.Impl.Rsa.AArch64.WindowFive.primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup])
    (by simp [VG.Impl.Rsa.AArch64.WindowFive.primesSetup]) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hwide hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hwide hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.AArch64.WindowFive
