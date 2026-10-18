module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryState
import VerifiedGarbage.Proof.Framework.Omega

/-! # ABI initialization establishes every invariant of the complete native generator -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem entryReady_ok {p : GenerationContext} {s : State} (h : EntryState p s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryIncoming ++
      Impl.Dsa.AArch64.Generation.entryDerived)) s fun t =>
      ∃ W, GenerationMemory p W t ∧ W 16 = 0 ∧
        Frame p.changed s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  let V := fun i => s.mem (VG.Proof.Bignum.off p.geo.hash i)
  let W := fun k => VG.Proof.Bignum.word s.mem p.geo.F (8 * k)
  refine WP.mono (entrySetup_ok h.geometry (initialRep s.mem p.geo.F p.geo.hash)
    h.sp h.frame h.incomingRead) fun t ⟨Rt, ft, kt⟩ => ?_
  have ff := p.frame_single ft
  let Wt := entryWords s.gpr (VG.Proof.Bignum.word s.mem p.geo.F) W
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have Lt : Lay t p.geo.F p.geo.hash := {
    sp := kt.sp.trans h.sp
    fr := by
      intro a n hc
      obtain ⟨r, hr, hrc⟩ := hc
      rcases List.mem_singleton.mp hr with rfl
      exact ⟨_, by rw [kt.wr]; exact h.frame, hrc⟩
    sc := Covers.one ((h.scratch.congr kt.wr).region hh (by decide))
    slot := (Rt.fr 12 (by decide)).trans (h.hashWord W)
    geo := h.geometry }
  refine ⟨Wt, ⟨Lt, ⟨V, Rt⟩, h.words W, h.scratch.congr kt.wr,
    h.seeds.frame ff kt.rd kt.wr, h.hs.frame ff kt.rd kt.wr, h.rand.frame ff kt.rd kt.wr⟩,
    ?_, ff, kt⟩
  rfl

end VG.Proof.Dsa.AArch64.Generation
