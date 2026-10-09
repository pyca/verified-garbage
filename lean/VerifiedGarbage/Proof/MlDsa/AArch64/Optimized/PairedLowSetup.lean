import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowSetup (g : Nat) (s t : State) : Prop where
  ready : LowReady g t
  flags : t.v .v30=0
  scale : ∀e<4,vword (t.v .v15) e=BitVec.ofNat 32 (2*g)
  lower : ∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1
  width : ∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)

theorem lowMiddle_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (middleMoves++constants .r0 g)) s fun t =>
      CallFrame middleRegs constantRegs s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      LowSetup g s t := by
  rw [WP.block_append_iff]
  refine WP.mono (middleMoves_ok s) fun a ⟨⟨⟨h0,h2,h12,hm⟩,hk⟩,hv⟩ => ?_
  refine WP.mono (r0Constants_ok g hg a (by rw [hv]; exact hq)) fun t ⟨ht,hc,hflag,hs,hl,hw⟩ => ?_
  refine ⟨((CallFrame.ofKeep hk hv).trans (setup_callFrame ht)).mono (by decide) (by simp),
    ht.mem.trans hm,(ht.gpr .x0 (by decide)).trans h0,(ht.gpr .x2 (by decide)).trans h2,
    (ht.gpr .x12 (by decide)).trans h12,?_⟩
  refine ⟨hc,hflag,hs,?_,?_⟩
  · simpa only [hk.get .x8 (by decide)] using hl
  · simpa only [hk.get .x8 (by decide)] using hw

end VG.Proof.MlDsa.AArch64.Optimized.Paired
