module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Framework.Omega

/-! # ABI initialization establishes every invariant of the complete native generator -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem entryReady_ok {p : GenerationContext} {s : State} (h : EntryState p s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.entryHeader ++ Impl.Dsa.X86_64.Generation.entryIncoming ++
      Impl.Dsa.X86_64.Generation.entryDerived)) s fun t =>
      ∃ W, GenerationMemory p W t ∧ W 16 = 0 ∧
        Frame p.changed s.mem t.mem ∧ Keep [.rax] s t := by
  let V := fun i => s.mem (off p.geo.hash i)
  let W := fun k => word s.mem p.geo.F (8 * k)
  refine WP.mono (entrySetup_ok h.geometry (initialRep s.mem p.geo.F p.geo.hash)
    h.rsp h.frame h.incomingRead) fun t ⟨Rt, ft, kt⟩ => ?_
  have ff := p.frame_single ft
  let Wt := entryWords s.gpr (word s.mem p.geo.F) W
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have Lt : Lay t p.geo.F p.geo.hash := {
    rsp := (kt.gpr (by decide)).trans h.rsp
    fr := by rw [kt.2.2]; exact h.frame
    F8 := by have := p.geo.stackSize; omega
    Fw := h.frameTop
    sc := (h.scratch.congr kt.2.2).sub (n := oRsa) hh (by decide)
    slot := (Rt.fr 14 (by decide)).trans (h.hashWord W)
    dFS := h.geometry.dFS
    dRS := h.geometry.dRS }
  refine ⟨Wt, ⟨Lt, ⟨V, Rt⟩, h.words W, h.scratch.congr kt.2.2,
    h.seeds.frame ff kt.2.1 kt.2.2, h.hs.frame ff kt.2.1 kt.2.2, h.rand.frame ff kt.2.1 kt.2.2⟩,
    ?_, ff, kt⟩
  rfl

end VG.Proof.Dsa.X86_64.Generation
