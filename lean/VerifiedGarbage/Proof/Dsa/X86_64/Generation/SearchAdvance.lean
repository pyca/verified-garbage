module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
import VerifiedGarbage.Proof.Framework.Omega

/-! # The p search advances exactly one counter and one hash stride -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem searchAdvance_ok {s : State} {B : Addr} {counter stride limit : Nat}
    (h : SearchControl B counter stride s) (hc : counter < limit) (hl : limit ≤ 12288)
    (hs : stride ≤ 12) :
    WP isa (Impl.Dsa.X86_64.Generation.pSearchAdvance limit stride) s fun t =>
      SearchControl B (counter + 1) stride t ∧
      word t.mem B 16 = BitVec.ofNat 64 (if counter + 1 < limit then 3 else 2) ∧
      Outside B 0 24 s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  unfold Impl.Dsa.X86_64.Generation.pSearchAdvance
  refine WP.seq (WP.mono (searchAdvanceHead_ok h hc hl hs) fun u ⟨hu, hcf, ho, hk⟩ => ?_)
  refine WP.ite (decide (counter + 1 < limit)) (by simp [eval, hcf]) (fun hyes => ?_) (fun hno => ?_)
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

theorem searchInit_ok {s : State} {B : Addr} (h : Scr s B 24) (hdi : s.gpr .rdi = B) (stride : Nat) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pSearchInit) s fun t =>
      SearchControl B 0 stride t ∧ Outside B 0 16 s.mem t.mem ∧ Keep [.rax] s t := by
  let m := (s.mem.writeW (off B 0) (BitVec.ofNat 64 0)).writeW (off B 8) (BitVec.ofNat 64 1)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m) (by
    xrun [Impl.Dsa.X86_64.Generation.pSearchInit, State.ea, hdr, hdrOff, hdi,
      h.st (d := 0) (by decide), h.st (d := 8) (by decide)]; rfl) rfl) fun t ⟨hm, hk⟩ => ?_
  have ho : Outside B 0 16 s.mem t.mem := by
    rw [hm]
    exact ((writeW_outside _ B _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (d := 8) (by decide)).mono (by decide) (by decide))
  refine ⟨⟨h.congr hk.2.2, (hk.gpr (by decide)).trans hdi, ?_, ?_⟩, ho, hk⟩
  · rw [hm]
    dsimp only [m]
    rw [(writeW_outside _ B _ (d := 8) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  · rw [hm, Nat.zero_mul, Nat.add_zero]; exact word_writeW_self _ _ _ _

end VG.Proof.Dsa.X86_64.Generation
