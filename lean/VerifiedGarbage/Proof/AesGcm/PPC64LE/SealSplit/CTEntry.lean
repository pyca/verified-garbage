module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Entry
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTSeal
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Entry
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

-- separate module: the shared seal entry on the split caller's additional permissions.
/-! # Constant time of the shared seal entry with extended permissions -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.CTEntry
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Aes (bytesAt)


theorem entry_ready {s₀ s₁ : State} (h : SealAccess s₀)
    (h1 : SO1 (stackArg s₀ 1) (stackArg s₀ 0) s₀ s₁) :

      OneI (s₀.gpr .r3) (stackArg s₀ 1) s₀.sp (s₀.gpr .r4).toNat (s₀.gpr .r5) (s₀.gpr .r6).toNat (s₀.gpr .r7)
        (s₀.gpr .r8) (s₀.gpr .r9) (s₀.gpr .r10) s₁ ∧
      s₁.gpr .r24 = s₀.gpr .r5 ∧ s₁.gpr .r25 = BitVec.ofNat 64 (s₀.gpr .r6).toNat ∧
      s₁.gpr .r20 = stackArg s₀ 0 ∧ Covers [⟨stackArg s₀ 0, 16⟩] s₁.wr := by
  obtain ⟨_,_,dcd,dcW,dnd,dnW,dad,daW,ddt,ddW,ddA,dtW,dWA,fc,fn,fa,fd,fW,fsp,hR⟩ := h.pre
  have hC : Covers [⟨s₀.gpr .r3,256⟩] (s₀.rd++s₀.wr) :=
    Covers.trans (Covers.of_mem (by simp [sealReads])) h.reads
  have hW : Covers [⟨stackArg s₀ 1,2560⟩] s₀.wr :=
    Covers.trans (Covers.of_mem (by simp [sealWrites])) h.writes
  have hNr : Covers [⟨s₀.gpr .r5,(s₀.gpr .r6).toNat⟩] (s₀.rd++s₀.wr) :=
    Covers.trans (Covers.of_mem (by simp [sealReads])) h.reads
  have hAr : Covers [⟨s₀.gpr .r7,(s₀.gpr .r8).toNat⟩] (s₀.rd++s₀.wr) :=
    Covers.trans (Covers.of_mem (by simp [sealReads])) h.reads
  have hDw₀ : Covers [⟨s₀.gpr .r9,(s₀.gpr .r10).toNat⟩] s₀.wr :=
    Covers.trans (Covers.of_mem (by simp [sealWrites])) h.writes
  have hTag : Covers [⟨stackArg s₀ 0,16⟩] s₀.wr :=
    Covers.trans (Covers.of_mem (by simp [sealWrites])) h.writes
  have hk₁ := h1.en.keeps
  have toN : ∀ {x : BitVec 64}, x = BitVec.ofNat 64 x.toNat := fun {x} => by simp
  have hDw : Covers [⟨s₀.gpr .r9, (s₀.gpr .r10).toNat⟩] s₁.wr := by
    rw [hk₁.wr]; exact hDw₀
  refine ⟨⟨s₁.gpr, h1.r29, h1.r30, h1.r31, by rw [h1.r28]; exact toN, by rw [h1.r18]; exact toN, h1.r21,
    h1.r22, h1.r27, h1.r23, one_env h1 hC hW, ?_, ?_, ⟨⟨covers_left hDw, (s₀.gpr .r10).isLt, fd,
      ddW.sub_right (Lay.wSub (by decide)), ddW⟩, hDw, dcd⟩⟩, h1.r24, by rw [h1.r25]; exact toN, h1.r20, ?_⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hNr,
      (s₀.gpr .r6).isLt, fn, dnW.sub_right (Lay.wSub (by decide)), dnW⟩
  · exact ⟨by rw [hk₁.rd, hk₁.wr]; exact hAr,
      (s₀.gpr .r8).isLt, fa, daW.sub_right (Lay.wSub (by decide)), daW⟩
  · rw [hk₁.wr]; exact hTag


def entryRegs : List Reg := [.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10]


theorem entry_ct {I : State → Prop} {v : Reg → BitVec 64} {sp W : Addr}
    (haccess : ∀ s, I s → SealAccess s)
    (hpub : ∀ s, I s → s.sp=sp ∧ (∀ r ∈ entryRegs, s.gpr r=v r) ∧ stackArg s 1=W) :
    CT I (.block (oneEntry 104)) := by
  let v' : Reg → BitVec 64 := fun r => if r=.r12 then W else v r
  have hl : oneEntry 104 = [.addSp .r12 0,.load .d .r12 .r12 104] ++ (save .r12 ++
      ([mov .r29 .r3,mov .r28 .r4,.addi .r30 .r31 16,mov .r24 .r5,mov .r25 .r6,
        mov .r18 .r6,mov .r21 .r7,mov .r22 .r8,mov .r27 .r9,mov .r23 .r10,.addSp .r12 0,
        .load .d .r20 .r12 96] : List Instr)) := by
    rw [oneEntry,List.append_assoc]
  rw [hl]
  refine RelCT.block_append (CT.seq (J := fun s => s.sp=sp ∧
    ∀ r ∈ entryRegs++[.r12], s.gpr r=v' r) ?_ ?_ ?_)
  · obtain ⟨_,hc⟩ := oneHead_taint
    exact CT.taintEq [] v sp (fun s hs => ⟨(hpub s hs).1,by simp⟩) hc
  · intro s hs
    have hA : Covers [args s 2] (s.rd++s.wr) :=
      Covers.trans (Covers.of_mem (by simp [sealReads])) (haccess s hs).reads
    refine WP.mono (oneA_ok (.inl rfl) (args_in hA (by decide) (i := 1) (by decide))
      (show s.mem.readW (s.sp+BitVec.ofNat 64 104) 64=W from (hpub s hs).2.2)) fun t ⟨h12,hg,hk⟩ => ?_
    refine ⟨hk.sp.trans (hpub s hs).1,fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · have hn : r≠.r12 := by
        simp only [entryRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [v',hn,ite_false]
      exact (hg r hn).trans ((hpub s hs).2.1 r hr)
    · simp only [List.mem_singleton] at hr
      subst r
      simp only [v',ite_true]
      exact h12
  · obtain ⟨_,hc⟩ := oneRest_taint
    exact CT.taintEq (entryRegs++[.r12]) v' sp (fun _ hs => hs) hc


end VG.Proof.AesGcm.PPC64LE.SealSplit.CTEntry
