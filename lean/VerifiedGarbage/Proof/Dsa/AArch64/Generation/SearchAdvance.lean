module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus
import VerifiedGarbage.Proof.Framework.Omega

/-! # The p search advances exactly one counter and one hash stride -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem searchAdvance_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (Impl.Dsa.AArch64.Generation.pSearchAdvance limit stride) s fun t =>
      SearchControl B (counter + 1) stride t ∧
      word t.mem B 16 = BitVec.ofNat 64 (if counter + 1 < limit then 3 else 2) ∧
      Outside B 0 24 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x7] s t := by
  unfold Impl.Dsa.AArch64.Generation.pSearchAdvance
  refine WP.seq (WP.mono (searchAdvanceHead_ok h hc hl hs) fun u ⟨hu, hflag, ho, hk⟩ => ?_)
  refine WP.ite (decide (counter + 1 < limit)) (by
    by_cases he : counter + 1 < limit
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_right (show ¬ limit ≤ counter + 1 by omega), decide_eq_true he]; rfl
    · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hflag,
        ite_eq_left (show limit ≤ counter + 1 by omega), decide_eq_false he]; rfl) (fun hyes => ?_) (fun hno => ?_)
  · have hlt : counter + 1 < limit := of_decide_eq_true hyes
    refine WP.mono (searchStatus_ok hu (by decide : 3 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hlt, ite_true] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩
  · have hge : ¬ counter + 1 < limit := of_decide_eq_false hno
    refine WP.mono (searchStatus_ok hu (by decide : 2 ≤ 3)) fun t ⟨ht, hstat, hot, kt⟩ => ?_
    exact ⟨ht, by simpa only [hge, ite_false] using hstat,
      (ho.mono (by decide) (by decide)).trans (hot.mono (by decide) (by decide)),
      (hk.trans kt).mono (by decide)⟩

theorem searchInit_ok {s : State} {B : Addr} (h : Scr s B 24) (hdi : s.gpr .x0 = B) (stride : Nat) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pSearchInit) s fun t =>
      SearchControl B 0 stride t ∧ Outside B 0 16 s.mem t.mem ∧ Keep [.x3] s t := by
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 0)).writeW (off B 8) (BitVec.ofNat 64 1)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = m) (by
    brun [Impl.Dsa.AArch64.Generation.pSearchInit, hdi,
      hdr_enc (by decide : 0 < 32), hdr_enc (by decide : 1 < 32),
      h.st (d := 0) (by decide), h.st (d := 8) (by decide)]; rfl) rfl rfl rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.congr hk.wr, (hk.gpr _ (by decide)).trans hdi, ?_, ?_⟩, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm, Nat.zero_mul, Nat.add_zero]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.AArch64.Generation
