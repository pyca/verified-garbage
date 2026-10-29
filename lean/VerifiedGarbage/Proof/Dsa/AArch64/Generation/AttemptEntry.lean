module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PAttemptArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Enter a p attempt from the persistent frame and controller offset -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure AttemptEntry (p : PConstructPlan) (H : Spec.Mgf1.Hash) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.hash.F p.hash.S
  rep : ∃ V, Rep s.mem p.hash.F p.hash.S V W
  words : p.hash.W = upd (upd (upd W 0 (VG.Proof.Bignum.off (W 5) shaped)) 2 (BitVec.ofNat 64 p.hash.offset)) 25 (W 3)
  hashArgs : LabAt s p.hash.F p.hash.S p.hash.W p.hash.wrapped p.hash.len
  seedRead : ∀ i < p.hash.len, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off p.hash.seedPtr i) 1
  wrappedWrite : ∀ i < p.hash.len, InRegions s.wr (VG.Proof.Bignum.off p.hash.wrapped i) 1
  outputWrite : ∀ i < (p.hash.count + 1) * p.hash.len, InRegions s.wr (VG.Proof.Bignum.off p.hash.output i) 1
  seed : Spec.Rsa.bytesAt s.mem p.hash.seedPtr p.hash.len = p.hash.seed
  seedFrame : (⟨p.hash.seedPtr, p.hash.len⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  scratch : Scr s p.B p.Z
  qSource : Src s p.B p.Z (VG.Proof.Bignum.off (p.hash.W 5) q) p.qb
  qFrame : (⟨VG.Proof.Bignum.off (p.hash.W 5) q, p.qb.length⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  shapedWrite : ∀ i < p.len, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.hash.W 5) shaped) i) 1
  pWrite : ∀ i < p.len, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.hash.W 5) Impl.Dsa.Generation.Layout.p) i) 1
  exponentWrite : ∀ i < p.len, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.hash.W 5) exponent) i) 1

theorem attemptEntry_ok {p : PConstructPlan} {H : Spec.Mgf1.Hash} {W : Nat → BitVec 64}
    {s : State} {C : Addr} (h : AttemptEntry p H W s)
    (hdi : s.gpr .x0 = C) (hread : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off C 8) 8)
    (hoff : VG.Proof.Bignum.word s.mem C 8 = BitVec.ofNat 64 p.hash.offset) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pAttemptArgs) s fun t =>
      PConstructState p H t ∧ Frame [⟨p.hash.F, frameBytes⟩] s.mem t.mem ∧
      Keep [.x3, .x4, .x5] s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (pAttemptArgs_ok h.layout R hdi hread hoff rfl)
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame [⟨p.hash.F, frameBytes⟩] s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.hash.F, frameBytes⟩ (by simp)
    change ¬ ofs p.hash.F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  have hqmax : p.qb.length < 2 ^ 64 := by
    rw [p.qLength]; rcases p.hash.width with hh | hh <;> omega
  refine ⟨⟨⟨Lt, ⟨V, ?_⟩, h.hashArgs.congr kt.rd kt.wr rfl rfl,
      (fun i hi => by rw [kt.rd, kt.wr]; exact h.seedRead i hi),
      (fun i hi => by rw [kt.wr]; exact h.wrappedWrite i hi),
      (fun i hi => by rw [kt.wr]; exact h.outputWrite i hi), ?_, fun j hj => by omega⟩,
      h.scratch.congr kt.wr,
      source_of_frame h.qSource ff (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.qFrame)
        hqmax kt.rd kt.wr,
      (fun i hi => by rw [kt.wr]; exact h.shapedWrite i hi),
      (fun i hi => by rw [kt.wr]; exact h.pWrite i hi),
      (fun i hi => by rw [kt.wr]; exact h.exponentWrite i hi)⟩, ff, kt⟩
  · rw [h.words]; exact Rt
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.seedFrame)
      (by rcases p.hash.width with hh | hh <;> omega), h.seed]

end VG.Proof.Dsa.AArch64.Generation
