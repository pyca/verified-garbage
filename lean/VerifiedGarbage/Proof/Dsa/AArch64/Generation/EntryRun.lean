module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntryRestore
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
    WP isa (Impl.Dsa.AArch64.Generation.entryBody H.sha1 H.sha256 M.mm K.run) (allocState 448 s) fun t =>
      EntryResult s t ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      t.sp = (allocState 448 s).sp ∧
      t.rd = s.rd ∧ t.wr = (allocState 448 s).wr := by
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
  have abis := entryAbi_saved h ft
  have perm (d : Nat) (hd : d + 8 ≤ 448) :
      InRegions (t.rd ++ t.wr) (generationBase s + BitVec.ofNat 64 d) 8 := by
    rw [rd, wr]
    exact ⟨⟨generationBase s, 448⟩, List.mem_append_right _ (List.mem_cons_self ..),
      Offset.contains_base _ hd (by omega)⟩
  refine WP.mono (entryRestore_ok sp perm abis.1 abis.2 saved) fun v hv => ?_
  exact ⟨⟨hv.result.trans status, hv.memory ▸ bytes⟩, hv.gprs, hv.vectors,
    hv.stack.trans sp, hv.read.trans rd, hv.write.trans wr⟩

theorem entryRun_ok (H : GenerationHashes) (M : Mont) (K : Kernel)
    {s : State} (h : GenerationABI s) :
    WP isa (Impl.Dsa.AArch64.Generation.code H.sha1 H.sha256 M.mm K.run) s fun t =>
      EntryResult s t ∧ abiPreserved s t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.AArch64.Generation.code
  apply alloc_frame_ok (by decide : 0 < 448 ∧ 448 < 4096 ∧ 448 % 16 = 0) (by omega_using [h.stackLower])
  refine WP.mono (entryInner_ok H M K h) fun t ⟨result, cs, vs, sp, rd, wr⟩ => ?_
  refine ⟨sp, wr, ⟨result.status, result.bytes⟩, ⟨cs, ?_, vs⟩, rd, ?_⟩
  · change t.sp + BitVec.ofNat 64 448 = s.sp
    rw [sp]
    exact BitVec.sub_add_cancel ..
  · change t.wr.tail = s.wr
    rw [wr]
    rfl

end VG.Proof.Dsa.AArch64.Generation
