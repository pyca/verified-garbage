import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowKernel
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlKem.AArch64 (Keep)

theorem selected_low_ok {s : State} (hg : IsG (arg32 s .x5))
    (ha : EntryAccess s) (ht : PairedTable.Words s.mem (s.syms "VG_MLDSA_INV_PAIR"))
    (hdw : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4,2048⟩)
    (hds : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩)
    (hdd : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hsd : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hda : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩)
    (hsa : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩)
    (haw : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 off) 16) :
    WP isa (selected .r0) s fun t =>
      ∃a b u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Keep [.x17,.x7] a b ∧ b.mem=a.mem ∧ Prepared b u ∧ LowSetup (arg32 s .x5) b u ∧
        Keep entryRegs s t ∧
        let d := lowPassData (arg32 s .x5) (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  change WP isa (.seq (.block pro) (VG.Impl.MlDsa.AArch64.Round.zext .x17
    (VG.Impl.MlDsa.AArch64.Round.onGamma .x17 .x7 kernelPaired))) s _
  refine WP.seq (WP.mono (prolog_ok s ha.save) fun a ⟨hk,args,hta,_,hs,hframe⟩ => ?_)
  have hga : arg32 a .x17=arg32 s .x5 := by unfold arg32; rw [args.gamma]
  apply zext_ok
  have hz := zextS_keep .x17 a
  refine onGamma_ok (by decide) (by rw [zextS_toNat,hga]; exact hg) fun g hge b hkb hmb => ?_
  have he : g=arg32 s .x5 := by rw [zextS_toNat,hga] at hge; exact hge.symm
  rw [he]
  have hb : Keep [.x17,.x7] a b := (hz.trans hkb).mono
  have hbm : b.mem=a.mem := hmb.trans (zextS_mem _ _)
  have ht' : PairedTable.Words b.mem (b.gpr .x1) := by
    rw [hbm,hb.get .x1 (by decide),hta]
    exact tableWords_frame ht hframe (by simpa only [List.mem_singleton,forall_eq] using hds)
  have hs' : Saved b.mem (b.gpr .x0) s.v := by
    rw [hbm,hb.get .x0 (by decide),args.work]; exact hs
  refine WP.mono (pairedLowKernel_ok _ hg (CallFrame.ofKeepWide (hk.trans hb)) hs'
    ((ha.kernel hk args hta).gamma hb) ht' ?_ ?_ ?_ ?_ ?_ ?_)
    fun t ⟨u,hu,hc,hkt,hm,hv⟩ => ?_
  · simpa only [hb.get .x1 (by decide),hb.get .x0 (by decide),hta,args.work] using hdw
  · simpa only [hb.get .x1 (by decide),hb.get .x15 (by decide),hta,args.data] using hdd
  · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),args.work,args.data] using hsd
  · simpa only [hb.get .x1 (by decide),hb.get .x16 (by decide),hta,args.aux] using hda
  · simpa only [hb.get .x0 (by decide),hb.get .x16 (by decide),args.work,args.aux] using hsa
  · simpa only [hb.wr,hk.wr,hb.get .x16 (by decide),args.aux] using haw
  · refine ⟨a,b,u,args,hframe,hb,hbm,hu,hc,hkt.mono (by decide),?_,?_⟩
    · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),hb.get .x16 (by decide),args.work,args.data,args.aux] using hm
    · simpa only [hb.get .x0 (by decide),hb.get .x15 (by decide),hb.get .x16 (by decide),args.work,args.data,args.aux] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
