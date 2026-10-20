module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructPlan
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PAttemptArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Enter a p attempt from the persistent frame and controller offset -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure AttemptEntry (p : PConstructPlan) (H : Spec.Mgf1.Hash) (W : Nat → BitVec 64) (s : State) : Prop where
  layout : Lay s p.hash.F p.hash.S
  rep : ∃ V, Rep s.mem p.hash.F p.hash.S V W
  words : p.hash.W = upd (upd (upd W 0 (off (W 5) shaped)) 2 (BitVec.ofNat 64 p.hash.offset)) 27 (W 3)
  hashArgs : LabAt s p.hash.F p.hash.S p.hash.W p.hash.wrapped p.hash.len
  seedRead : ∀ i < p.hash.len, InRegions (s.rd ++ s.wr) (off p.hash.seedPtr i) 1
  wrappedWrite : ∀ i < p.hash.len, InRegions s.wr (off p.hash.wrapped i) 1
  outputWrite : ∀ i < (p.hash.count + 1) * p.hash.len, InRegions s.wr (off p.hash.output i) 1
  seed : Spec.Rsa.bytesAt s.mem p.hash.seedPtr p.hash.len = p.hash.seed
  seedFrame : (⟨p.hash.seedPtr, p.hash.len⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  scratch : Scr s p.B p.Z
  qSource : Src s p.B p.Z (off (p.hash.W 5) q) p.qb
  qFrame : (⟨off (p.hash.W 5) q, p.qb.length⟩ : Region).Disjoint ⟨p.hash.F, frameBytes⟩
  shapedWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) shaped) i) 1
  pWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) Impl.Dsa.Generation.Layout.p) i) 1
  exponentWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) exponent) i) 1

theorem attemptEntry_ok {p : PConstructPlan} {H : Spec.Mgf1.Hash} {W : Nat → BitVec 64}
    {s : State} {C : Addr} (h : AttemptEntry p H W s)
    (hdi : s.gpr .rdi = C) (hread : InRegions (s.rd ++ s.wr) (off C 8) 8)
    (hoff : word s.mem C 8 = BitVec.ofNat 64 p.hash.offset) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s fun t =>
      PConstructState p H t ∧ Frame [⟨p.hash.F, frameBytes⟩] s.mem t.mem ∧
      Keep [.rax, .rcx, .rdx] s t := by
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
  refine ⟨⟨⟨Lt, ⟨V, ?_⟩, h.hashArgs.congr kt.2.1 kt.2.2 rfl rfl,
      (fun i hi => by rw [kt.2.1, kt.2.2]; exact h.seedRead i hi),
      (fun i hi => by rw [kt.2.2]; exact h.wrappedWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.outputWrite i hi), ?_, fun j hj => by omega⟩,
      h.scratch.congr kt.2.2,
      source_of_frame h.qSource ff (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.qFrame)
        hqmax kt.2.1 kt.2.2,
      (fun i hi => by rw [kt.2.2]; exact h.shapedWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.pWrite i hi),
      (fun i hi => by rw [kt.2.2]; exact h.exponentWrite i hi)⟩, ff, kt⟩
  · rw [h.words]; exact Rt
  · rw [VG.Proof.Dsa.Generation.frame_bytesAt ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl; exact h.seedFrame)
      (by rcases p.hash.width with hh | hh <;> omega), h.seed]

end VG.Proof.Dsa.X86_64.Generation
