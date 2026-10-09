import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntryAccess
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernel

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

def entryRegs : List Reg := [.x0,.x1,.x2,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

theorem selected_check_eq (hint : Bool) :
    selected (if hint then .h else .z)=.seq (.block pro) (kernel (if hint then .h else .z) 0) := by
  cases hint <;> rfl

/-- Whole z/h entry, including argument remapping, saved vectors, all inverse
and response iterations, combined result, and ABI restoration. -/
theorem selected_check_ok (hint : Bool) {s : State}
    (ha : EntryAccess s) (ht : PairedTable.Words s.mem (s.syms "VG_MLDSA_INV_PAIR"))
    (hdw : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4,2048⟩)
    (hds : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩)
    (hdd : (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (hsd : (⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩)
    (haux : hint=true → ∀off,off+16≤2048 → InRegions (s.rd++s.wr) (s.gpr .x3+BitVec.ofNat 64 off) 16) :
    WP isa (selected (if hint then .h else .z)) s fun t =>
      ∃a u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Prepared a u ∧ CheckSetup hint a u ∧ Keep entryRegs s t ∧
        let d := finalPassData hint (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (constantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn (if hint then .h else .z) d := by
  rw [selected_check_eq]
  refine WP.seq (WP.mono (prolog_ok s ha.save) fun a ⟨hk,args,hta,_,hs,hframe⟩ => ?_)
  have ht' : PairedTable.Words a.mem (a.gpr .x1) := by
    rw [hta]
    exact tableWords_frame ht hframe (by simpa only [List.mem_singleton,forall_eq] using hds)
  have hs' : Saved a.mem (a.gpr .x0) s.v := by rw [args.work]; exact hs
  refine WP.mono (checkKernel_ok hint 0 (CallFrame.ofKeepWide hk) hs' (ha.kernel hk args hta)
    ht' ?_ ?_ ?_ ?_) fun t ⟨u,hu,hc,hkt,hm,hv⟩ => ?_
  · simpa only [hta,args.work] using hdw
  · simpa only [hta,args.data] using hdd
  · simpa only [args.work,args.data] using hsd
  · simpa only [hk.rd,hk.wr,args.aux] using haux
  · refine ⟨a,u,args,hframe,hu,hc,hkt.mono (by decide),?_,?_⟩
    · simpa only [args.work,args.data,args.aux] using hm
    · simpa only [args.work,args.data,args.aux] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
