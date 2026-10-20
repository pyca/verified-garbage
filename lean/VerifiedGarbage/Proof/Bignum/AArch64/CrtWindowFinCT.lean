module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# RSA with the CRT on AArch64: the result in constant time

`finish` sums `m_q + q h` into the modulus' accumulators (`finishSum`), whose
parts keep the header and the primes' workspaces (`FA`), and stores it masked
(`outArr_ct`): `crtFinish_ct`.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.Bignum.CrtWindowFive (offQ32 tabBytes32)

/-- `finishSum`'s hypotheses after `p`'s phase. -/
theorem stage5_fa {p : CrtPub} {t : State} (h : Stage R5 p t) :
    FA ⟨p.B, p.Z, p.w, offP p.w, offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ t := by
  unfold CrtPub.w
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hql2 := h.ql2
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hP8 : 256 ≤ slot (wsWords p.pl) 8 := by unfold slot hdrBytes; omega
  have hQ8 : 256 ≤ slot (wsWords p.ql) 8 := by unfold slot hdrBytes; omega
  have hwq2 : 2 ≤ wsWords p.ql := by unfold wsWords; omega
  have hwq := wsWords_le (len := p.ql) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ32 at hZq; omega
  unfold FA RowsPre
  dsimp only
  exact ⟨⟨minv, hr.good, hZ⟩, ⟨hr.good.scr, hr.good.x0, hr.good.hdr.harr aAcc (by decide), hr.wsP, hr.wsQ,
      by rw [← word_off]; exact hr.pws.hdr.hw, by rw [← word_off]; exact hr.qws.hdr.hw,
      by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off],
      by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by decide, Nat.le_refl _,
      by unfold offQ32 offP; omega, by omega⟩,
    by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off], by omega, hwq, by omega⟩

/-- `finishSum` leaves what the store needs. -/
theorem finSum_out {p : CrtPub} {t₂ : State} (h : Stage R5 p t₂) :
    WP isa (seqs finishSum) t₂ (OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩) := by
  have hfa := stage5_fa h
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, h, hv, minv, mp, mq, hr⟩ := h
  obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, hlo, hop, hoq⟩, -, hwq, hwq', hw⟩ := hfa
  have hk1 := h.k1
  have hk2 := h.k2
  have hpl2 := h.pl2
  have hpl1 := h.pl1
  have hZq := h.wide
  have htp : tabBytes (wsWords p.pl) ≤ tabBytes32 (wsWords p.pl) := by unfold tabBytes tabBytes32; omega
  have htq : tabBytes (wsWords p.ql) ≤ tabBytes32 (wsWords p.ql) := by unfold tabBytes tabBytes32; omega
  have ewp : wsTab (wsWords p.pl) = tabBytes32 (wsWords p.pl) := rfl
  have ewq : wsTab (wsWords p.ql) = tabBytes32 (wsWords p.ql) := rfl
  have hn := hr.good.scr.nowrap
  have hwp2 : 2 ≤ wsWords p.pl := by unfold wsWords; omega
  have hwp := wsWords_le (len := p.pl) (w := (p.k + 7) / 8) (by omega) (by omega)
  have hZ : slot ((p.k + 7) / 8) 8 ≤ p.Z := by unfold offQ32 at hZq; omega
  refine WP.mono (finishSum_ok hr.good (by unfold CrtPub.w at hw; omega) hr.wsP hr.wsQ
    (by rw [← word_off]; exact hr.pws.hdr.hw) (by rw [← word_off]; exact hr.qws.hdr.hw)
    (by rw [← word_off, hr.pws.hdr.harr _ (by decide), off_off]) (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off])
    (by rw [← word_off, hr.qws.hdr.harr _ (by decide), off_off]) (Nat.le_refl _) (by unfold offQ32 offP; omega) (by dsimp only [CrtPub.w]; omega)
    (by omega) hwp (by omega) hwq') fun t₃ ⟨_, ho₃, k₃⟩ => ?_
  have hacc := accs_le ((p.k + 7) / 8)
  have hb₃ : ∀ i < 32, word t₃.mem p.B (8 * i) = word t₂.mem p.B (8 * i) := fun i hi =>
    ho₃.word (Or.inl (by have := hdr_lt_slot ((p.k + 7) / 8) Public.aAcc hi; omega)) (by omega)
  have hfx : ∀ i < 32, hFixed i = true → word t₃.mem p.B (8 * i) = word σ.mem p.B (8 * i) := fun i hi hf => by
    rw [hb₃ i hi]; exact hr.hfix i hi hf
  have k03 := hr.keep.trans k₃
  unfold OPreW
  dsimp only
  exact ⟨minv, p.mask xb pb qb qib, ⟨hr.good.scr.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans hr.good.x0,
      ⟨(hb₃ _ (by decide)).trans hr.good.hdr.hw, (hb₃ _ (by decide)).trans hr.good.hdr.hminv,
        fun j hj => (hb₃ _ (by unfold sArr; omega)).trans (hr.good.hdr.harr j hj)⟩⟩, rfl, hZ, by omega,
    by omega, by rw [hfx _ (by decide) (by decide)]; exact h.hO, by rw [hfx _ (by decide) (by decide)]; exact h.hK,
    by rw [hb₃ _ (by decide)]; exact hr.msk, fun j hj => by rw [k03.wr]; exact h.out j hj, h.outSep⟩

/-- `finish` leaks the same in runs that agree on the public data. -/
theorem crtFinish_ct : RelCT isa (Two (Stage R5)) (seqs finish) fun _ _ => True := by
  rw [finish_out]
  refine RelCT.seqs_append (by simp [finishSum, zeroAccs]) (by simp [outStepsArr])
    (RelCT.seq (R := Two OPreW) ?_ (outArr_ct (j := Public.aAcc) (by decide) (by taint_decide)))
  refine (two_post (Ψ := fun (p : CrtPub) t => OPreW ⟨p.B, p.Z, p.w, p.k, p.op⟩ t)
    (two_map (fun p : CrtPub => (⟨p.B, p.Z, p.w, offP p.w, offQ32 p.w p.pl, wsWords p.pl, wsWords p.ql⟩ : RowsPub))
      (fun _ _ h => stage5_fa h) finSum_ct) fun p t h => finSum_out h).mono (fun _ _ h => h)
    fun _ _ h => two_bind (fun (p : CrtPub) _ _ h₁ h₂ => ⟨(⟨p.B, p.Z, p.w, p.k, p.op⟩ : OPubW), h₁, h₂⟩) h

end VG.Proof.Bignum.AArch64.WindowFive
