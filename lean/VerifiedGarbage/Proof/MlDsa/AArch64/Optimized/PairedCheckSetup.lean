import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSetupFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_mono)

structure CheckSetup (hint : Bool) (s t : State) : Prop where
  ready : CheckReady hint t
  flags : t.v .v30=0
  count : hint=true → t.v .v14=0
  gamma : hint=true → ∀e<4,vword (t.v .v11) e=(s.gpr .x17).setWidth 32
  lower : ∀e<4,vword (t.v .v9) e=(s.gpr .x8).setWidth 32-1
  width : ∀e<4,vword (t.v .v10) e=(s.gpr .x8).setWidth 32+((s.gpr .x8).setWidth 32-1)

theorem checkConstants_ok (hint : Bool) (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (constants (if hint then .h else .z) g)) s fun t =>
      SetupKeep constantRegs s t ∧ CheckSetup hint s t := by
  cases hint
  · refine WP.mono (zConstants_ok g s hq) fun t ⟨hf,hc,hf0,hl,hw⟩ => ?_
    exact ⟨setup_mono hf (by decide),⟨hc,hf0,by simp,by simp,hl,hw⟩⟩
  · refine WP.mono (hConstants_ok g s hq) fun t ⟨hf,hc,hf0,hn,hg,hl,hw⟩ => ?_
    exact ⟨hf,⟨hc,hf0,fun _ => hn,fun _ => hg,hl,hw⟩⟩

def middleRegs : List Reg := [.x0,.x2,.x9,.x12]

theorem checkMiddle_ok (hint : Bool) (g : Nat) (s : State)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32) :
    WP isa (.block (middleMoves++constants (if hint then .h else .z) g)) s fun t =>
      CallFrame middleRegs constantRegs s t ∧ t.mem=s.mem ∧
      t.gpr .x0=s.gpr .x0-1024 ∧ t.gpr .x2=s.gpr .x0-1024 ∧ t.gpr .x12=8 ∧
      CheckSetup hint s t := by
  rw [WP.block_append_iff]
  refine WP.mono (middleMoves_ok s) fun a ⟨⟨⟨h0,h2,h12,hm⟩,hk⟩,hv⟩ => ?_
  refine WP.mono (checkConstants_ok hint g a (by rw [hv]; exact hq)) fun t ⟨ht,hc⟩ => ?_
  refine ⟨((CallFrame.ofKeep hk hv).trans (setup_callFrame ht)).mono (by decide) (by simp),
    ht.mem.trans hm,(ht.gpr .x0 (by decide)).trans h0,(ht.gpr .x2 (by decide)).trans h2,
    (ht.gpr .x12 (by decide)).trans h12,?_⟩
  refine ⟨hc.ready,hc.flags,hc.count,?_,?_,?_⟩
  · simpa only [hk.get .x17 (by decide)] using hc.gamma
  · simpa only [hk.get .x8 (by decide)] using hc.lower
  · simpa only [hk.get .x8 (by decide)] using hc.width

end VG.Proof.MlDsa.AArch64.Optimized.Paired
