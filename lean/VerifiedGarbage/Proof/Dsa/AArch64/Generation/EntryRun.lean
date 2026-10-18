module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySavedLink
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega

/-! Functional results at the complete AAPCS64 generation boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Impl.RsaOaep.AArch64

def abiResult (s : State) : Option (List Byte) :=
  Spec.Dsa.generateParametersBytes (s.gpr .x2).toNat (s.gpr .x3).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

structure EntryResult (s t : State) : Prop where
  status : t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus (abiResult s))
  bytes : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    (abiResult s).getD (List.replicate (s.gpr .x1).toNat 0)

theorem entryInner_ok (H : GenerationHashes) (M : Mont) (K : Kernel)
    {s : State} (h : GenerationABI s) :
    WP isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 M.mm K.run) (allocState 320 s) fun t =>
      EntryResult s t ∧ t.gpr .x30 = s.gpr .x30 ∧ t.sp = (allocState 320 s).sp ∧
      t.rd = s.rd ∧ t.wr = (allocState 320 s).wr := by
  unfold Impl.Dsa.AArch64.Generation.entryBody
  refine WP.seq (WP.mono (entrySave_ok s) fun u hu => ?_)
  subst u
  apply WP.assoc
  have output : (⟨(contextOf h).saved 6, 2 * (contextOf h).geo.pLen + (contextOf h).geo.qLen⟩ : Region)
      ∈ (linkState s).wr := by
    change (⟨s.gpr .x0, 2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat⟩ : Region) ∈ _
    rw [← h.outLength]
    change _ ∈ _ :: s.wr
    apply List.mem_cons_of_mem
    rw [h.wr]; simp
  have seeds : (contextOf h).seeds.bytes.length % (contextOf h).geo.qLen = 0 := by
    simpa only [contextOf, tapeOf, geometryOf, bytesAt_length] using h.seedsLength
  have hs : (contextOf h).hs.bytes.length % (contextOf h).geo.pLen = 0 := by
    simpa only [contextOf, tapeOf, geometryOf, bytesAt_length] using h.hsLength
  refine WP.seq (WP.mono (entryBody_ok H M K (entryInitial_link h) (outputPlanOf h) output seeds hs)
    fun t ⟨status, bytes, ft, sp, rd, wr⟩ => ?_)
  have outlen : 2 * (contextOf h).geo.pLen + (contextOf h).geo.qLen = (s.gpr .x1).toNat := h.outLength.symm
  rw [outlen] at bytes ft
  have saved := link_saved h ft
  have perm : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 296) 8 := by
    rw [rd, wr, sp]
    exact ⟨⟨generationBase s, 320⟩, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ (by decide) (by decide)⟩
  have load : t.mem.readW (t.sp + BitVec.ofNat 64 296) 64 = s.gpr .x30 := by
    rw [sp]
    exact saved
  refine WP.mono (WP.keep [.x30] (Q := fun v => v.gpr .x30 = s.gpr .x30 ∧ v.mem = t.mem)
    (by brun [exec_ldrSp (off := 296) (by decide), perm, load]) rfl rfl rfl)
    fun v ⟨⟨lr, hm⟩, kv⟩ => ?_
  refine ⟨⟨?_, ?_⟩, lr, kv.sp.trans sp, kv.rd.trans rd, kv.wr.trans wr⟩
  · exact (kv.gpr .x0 (by decide)).trans status
  · rw [hm]
    exact bytes

theorem entryRun_ok (H : GenerationHashes) (M : Mont) (K : Kernel)
    {s : State} (h : GenerationABI s) :
    WP isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 M.mm K.run) s fun t =>
      EntryResult s t ∧ t.gpr .x30 = s.gpr .x30 ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.code
  apply alloc_frame_ok (by decide : 0 < 320 ∧ 320 < 4096 ∧ 320 % 16 = 0) (by omega_using [h.stackLower])
  refine WP.mono (entryInner_ok H M K h) fun t ⟨result, lr, sp, rd, wr⟩ => ?_
  refine ⟨sp, wr, ⟨result.status, result.bytes⟩, lr, ?_, rd, ?_⟩
  · change t.sp + BitVec.ofNat 64 320 = s.sp
    rw [sp]
    exact BitVec.sub_add_cancel ..
  · change t.wr.tail = s.wr
    rw [wr]
    rfl

end VG.Proof.Dsa.AArch64.Generation
