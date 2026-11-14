module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Dsa.AArch64.Generation.PAttemptArgs`, which only this module used -/

section

/-! # Frame arguments for a complete p-candidate attempt -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Proof.RsaOaep.AArch64

theorem pAttemptArgs_ok {s : State} {B F S op : Addr} {V : Nat → Byte}
    {W : Nat → BitVec 64} {offset : BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hdi : s.gpr .x0 = B)
    (hread : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off B 8) 8)
    (hoff : VG.Proof.Bignum.word s.mem B 8 = offset)
    (hop : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped = op) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pAttemptArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 25 (W 3)) ∧
      Outside F 0 208 s.mem t.mem ∧ Keep [.x3, .x4, .x5] s t := by
  have hst0 : InRegions s.wr F 8 := by simpa [VG.Proof.Bignum.off] using L.st (d := 0) (n := 8) (by decide)
  have hw5 : s.mem.readW (F + BitVec.ofNat 64 40) 64 = W 5 := R.fr 5 (by decide)
  have hi : (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.shaped).setWidth 64 =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped := by decide
  have hw3 : VG.Proof.Bignum.word ((s.mem.writeW (VG.Proof.Bignum.off F 0) op).writeW (VG.Proof.Bignum.off F 16) offset) F 24 = W 3 := by
    rw [(writeW_outside _ F _ (d := 16) (by decide)).word (Or.inr (by decide)) (by decide),
      (writeW_outside _ F _ (d := 0) (by decide)).word (Or.inr (by decide)) (by decide)]
    exact R.fr 3 (by decide)
  simp only [VG.Proof.Bignum.word, VG.Proof.Bignum.off, BitVec.add_zero] at hw3
  refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t =>
      t.mem = ((s.mem.writeW (VG.Proof.Bignum.off F 0) op).writeW (VG.Proof.Bignum.off F 16) offset).writeW
        (VG.Proof.Bignum.off F 200) (W 3)) (by
    brun [State.write, VG.Impl.RsaOaep.AArch64.sLab,
      VG.Proof.RsaOaep.AArch64.off, VG.Proof.Bignum.off, Impl.Dsa.AArch64.Generation.pAttemptArgs, L.sp, hdi, hread, hoff,
      exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 24) (by decide),
      exec_storeSp (off := 0) (by decide), exec_storeSp (off := 16) (by decide),
      exec_storeSp (off := 200) (by decide), hdr_enc (by decide : 1 < 32),
      L.ld (d := 40) (n := 8) (by decide), L.ld (d := 24) (n := 8) (by decide),
      hst0, L.st (d := 16) (n := 8) (by decide), L.st (d := 200) (n := 8) (by decide),
      hw5, hi, hop, hw3, BitVec.add_zero]) rfl rfl rfl)
    fun t ⟨hm, hk⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd (upd W 0 op) 2 offset) 25 (W 3)) := by
    rw [hm]
    exact ((R.wf L.geo (by decide : 0 < nW) op).wf L.geo
      (by decide : 2 < nW) offset).wf L.geo (by decide : 25 < nW) (W 3)
  refine ⟨lay_of_rep L R Rt (by simp [upd]) hk.sp hk.wr, Rt, ?_, hk⟩
  rw [hm]
  exact (((writeW_outside _ F _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
    ((writeW_outside _ F _ (d := 16) (by decide)).mono (by decide) (by decide))).trans
    ((writeW_outside _ F _ (d := 200) (by decide)).mono (by decide) (by decide))

end VG.Proof.Dsa.AArch64.Generation

end

end


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
    omega_using [hn]
  have hqmax : p.qb.length < 2 ^ 64 := by
    rw [p.qLength]; rcases p.hash.width with hh | hh <;> omega_using [hh]
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
      (by rcases p.hash.width with hh | hh <;> omega_using [hh]), h.seed]

end VG.Proof.Dsa.AArch64.Generation
