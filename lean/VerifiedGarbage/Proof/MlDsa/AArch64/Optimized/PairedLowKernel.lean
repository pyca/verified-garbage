import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedKernel
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField
import VerifiedGarbage.Spec.MlDsa.PairedResponse

/-! ## `PairedLowKernel` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlKem.AArch64 (Keep)

theorem pairedLowKernel_ok (g : Nat) (hg : VG.Proof.MlDsa.AArch64.Round.IsG g) {s₀ s : State}
    {gr : List Reg} {vr : List VReg}
    (hf : CallFrame gr vr s₀ s) (hs : Saved s.mem (s.gpr .x0) s₀.v)
    (ha : KernelAccess s) (ht : PairedTable.Words s.mem (s.gpr .x1))
    (hdw : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x0,2048⟩)
    (hdd : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hsd : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x15,2048⟩)
    (hda : (⟨s.gpr .x1,4096⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (hsa : (⟨s.gpr .x0+BitVec.ofNat 64 2048,128⟩:Region).Disjoint ⟨s.gpr .x16,2048⟩)
    (haw : ∀off,off+16≤2048 → InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16) :
    WP isa (kernelPaired g) s fun t =>
      ∃u,Prepared s u ∧ LowSetup g s u ∧
        Keep (gr++kernelRegs) s₀ t ∧
        let d := lowPassData g (s.gpr .x0) (s.gpr .x15) (s.gpr .x16) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  apply lowKernel_wp
  refine WP.seq (WP.mono (firstKernel_access_ok ha ht hdw) fun b ⟨hb,hq,h0,h1,_,_,hm⟩ => ?_)
  have hq' : ∀e<4,vword (b.v .v31) e=8380417#32 := by
    intro e he
    rw [hq.qv]
    exact HighPack.repeatedWord_lane 8380417 he
  refine WP.seq (WP.mono (lowMiddle_ok g hg b hq') fun u ⟨hu,hum,hu0,hu2,hu12,hc⟩ => ?_)
  have huf := ((hf.trans (CallFrame.ofKeepWide hb)).trans hu)
  have hu2' : u.gpr .x2=s.gpr .x0 := by rw [hu2,h0]; bv_omega
  have hu1 : u.gpr .x1=s.gpr .x1+BitVec.ofNat 64 3840 := by
    rw [hu.gpr .x1 (by decide),h1]
    rfl
  have hu15 : u.gpr .x15=s.gpr .x15 :=
    (hu.gpr .x15 (by decide)).trans (hb.get .x15 (by decide))
  have hu16 : u.gpr .x16=s.gpr .x16 :=
    (hu.gpr .x16 (by decide)).trans (hb.get .x16 (by decide))
  have huframe : Frame [⟨s.gpr .x0,2048⟩] s.mem u.mem := by
    rw [hum,hm]; exact firstPass_frame (by decide)
  have htu : PairedTable.Words u.mem (s.gpr .x1) :=
    tableWords_frame ht huframe (by simpa only [List.mem_singleton,forall_eq] using hdw)
  have hsu : Saved u.mem (s.gpr .x0) s₀.v := hs.workFrame huframe
  have hac : LowSetup g s u := by
    refine ⟨hc.ready,hc.flags,hc.scale,?_,?_⟩
    · simpa only [hb.get .x8 (by decide)] using hc.lower
    · simpa only [hb.get .x8 (by decide)] using hc.width
  refine WP.mono (lowKernel_ok g hg huf hsu hu2' ?_ ?_ ?_ htu ?_ ?_ hu1 hu12 hc.ready ?_ ?_ ?_)
    fun t ⟨hkeep,htm,htv⟩ => ?_
  · simpa only [hu15] using hsd
  · intro p hp
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,BitVec.add_assoc,←BitVec.ofNat_add]
    apply ha.workRead
    obtain ⟨i,rfl⟩ := (extraSlots_mem _ _).mp hp
    omega
  · simpa only [hu16] using hsa
  · simpa only [hu15] using hdd
  · simpa only [hu16] using hda
  · simpa only [hu.rd,hu.wr,hb.rd,hb.wr] using ha.table
  · intro i hi p j
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu2',BitVec.add_assoc,←BitVec.ofNat_add]
    exact ha.workRead _ (by omega)
  · intro v hv i
    simp only [hu.rd,hu.wr,hb.rd,hb.wr,hu15,hu16,BitVec.add_assoc,←BitVec.ofNat_add]
    have hi0 : lowOff i≤1792 := by unfold lowOff; omega
    refine ⟨ha.dataRead _ (by omega),ha.dataRead _ (by omega),ha.dataWrite _ (by omega),
      ha.dataWrite _ (by omega),haw _ (by omega),haw _ (by omega)⟩
  · refine ⟨u,⟨hum.trans hm,hu2',hu15,hu16⟩,hac,?_,?_,?_⟩
    · refine hkeep.mono ?_
      intro r hr
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,middleRegs,finalGprs,
        kernelRegs] at hr ⊢
      grind
    · simpa only [hu15,hu16] using htm
    · simpa only [hu15,hu16] using htv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowEntry` -/

section

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

end

/-! ## `PairedLowSpecPre` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Optimized.Paired

structure LowSpecPre (s : State) : Prop where
  rd : s.rd=[⟨s.gpr .x0,1024⟩,⟨s.gpr .x1,2048⟩,⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩]
  wr : s.wr=[⟨s.gpr .x2,2048⟩,⟨s.gpr .x3,2048⟩,⟨s.gpr .x4,2176⟩]
  table : PairedTable.Artifact s.mem (s.syms "VG_MLDSA_INV_PAIR")
  tableSep : ∀r∈s.wr,(⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r
  commonData : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  commonAux : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  commonWork : (⟨s.gpr .x0,1024⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  secretData : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x2,2048⟩
  secretAux : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  secretWork : (⟨s.gpr .x1,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  dataAux : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x3,2048⟩
  dataWork : (⟨s.gpr .x2,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  auxWork : (⟨s.gpr .x3,2048⟩:Region).Disjoint ⟨s.gpr .x4,2176⟩
  products : pairedProductsReduced s.mem (s.gpr .x0) (s.gpr .x1)
  data : ∀j<2,Reduced s.mem (pairPolyPtr (s.gpr .x2) j)
  gamma : ((s.gpr .x5).setWidth 32).toNat∈gamma2s
  boundLow : 1≤((s.gpr .x6).setWidth 32).toNat
  boundHigh : ((s.gpr .x6).setWidth 32).toNat≤524288

theorem pairedLow_pre {s : State}
    (h : (pairedLowContract (abi.withConsts pairedConsts)).pre s) : LowSpecPre s := by
  sig_pre [pairedLowContract,pairedLowSig,abi,argRegs,pairedConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,PairedTable.expandedWords_length,stackBelow] at h
  obtain ⟨hdrop,hheld,_,hsep,htake,hwr,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,_,_,_,_,_,hprod,hdata,hgamma,hbl,hbh⟩ := h
  refine ⟨?_,hwr,?_,hsep,hcd,hca,hcw,hsd,hsa,hsw,hda,hdw,haw,hprod,hdata,hgamma,hbl,hbh⟩
  · rw [←List.take_append_drop (s.rd.length-1) s.rd,htake,hdrop]
    rfl
  · intro i hi
    refine (hheld i hi).trans ?_
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [PairedTable.expandedWords_length]; exact hi),
      Option.getD_some,getElem!_pos _ _ (by rw [PairedTable.expandedWords_length]; exact hi)]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowAccess` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

private theorem accessRegion {p : Addr} {len : Nat} {rs : List Region}
    (h : (⟨p,len⟩:Region)∈rs) {off : Nat} (ho : off+16≤len) (hl : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) 16 :=
  ⟨_,h,Offset.contains_base p ho (by omega)⟩

theorem LowSpecPre.access {s : State} (h : LowSpecPre s) : EntryAccess s := by
  constructor
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.rd]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

theorem pairedLow_machine {s : State} (h : LowSpecPre s) :
    WP isa (selected .r0) s fun t =>
      ∃a b u,Arguments s a ∧ Frame [⟨s.gpr .x4+BitVec.ofNat 64 2048,128⟩] s.mem a.mem ∧
        Keep [.x17,.x7] a b ∧ b.mem=a.mem ∧ Prepared b u ∧ LowSetup (Round.arg32 s .x5) b u ∧
        Keep entryRegs s t ∧
        let d := lowPassData (Round.arg32 s .x5) (s.gpr .x4) (s.gpr .x2) (s.gpr .x3) (lowConstantsAt u) (dataAt u) 8
        t.mem=d.mem ∧ t.gpr .x0=dataReturn .r0 d := by
  have htw := h.tableSep (⟨s.gpr .x4,2176⟩:Region) (by rw [h.wr]; simp)
  have htd := h.tableSep (⟨s.gpr .x2,2048⟩:Region) (by rw [h.wr]; simp)
  have hta := h.tableSep (⟨s.gpr .x3,2048⟩:Region) (by rw [h.wr]; simp)
  refine selected_low_ok ?_ h.access h.table.words
    (htw.sub_right (Region.sub_prefix (by decide)))
    (htw.sub_right (Offset.sub_base _ (by decide))) htd
    (h.dataWork.symm.sub_left (Offset.sub_base _ (by decide))) hta
    (h.auxWork.symm.sub_left (Offset.sub_base _ (by decide))) ?_
  · simpa [or_comm,VG.Spec.MlDsa.gamma2s,Round.IsG,VG.Impl.MlDsa.AArch64.Round.g32,VG.Impl.MlDsa.AArch64.Round.g88,Round.arg32] using h.gamma
  · intro off ho
    exact accessRegion (by rw [h.wr]; simp) ho (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunHigh` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowHighOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128)
    (hm : m'.read out 16=m.read out 16) : lowHighOutput g m' out raw=lowHighOutput g m out raw := by
  simp only [lowHighOutput,lowInputValues,hm]

/-- Every pair's high output uses its original input, regardless of its position. -/
theorem lowRun_read_high (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr out i h) 16=
      lowHighOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_slot_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_high _ _ _ _ _ _ _ _ hd
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowHighOutput_read_eq _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowRunLow` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem lowRun_read_aux_other (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hn : i∉is) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=d.mem.read (lowAddr aux i h) 16 := by
  apply lowRun_read_other
  intro j hj
  have hnij : i≠j := by intro he; subst j; exact hn hj
  have h0 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 0)
  have h1 := hd.symm.sep (lowAddr_contains_base aux i h) (lowAddr_contains_base out j 1)
  have h2 := lowAddr_sep (h:=h) (k:=0) aux (Or.inl hnij)
  have h3 := lowAddr_sep (h:=h) (k:=1) aux (Or.inl hnij)
  simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
    And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem lowLowOutput_read_eq (g : Nat) {m m' : Mem} (out : Addr) (raw : BitVec 128) (c : LowConstants)
    (hm : m'.read out 16=m.read out 16) : lowLowOutput g m' out raw c=lowLowOutput g m out raw c := by
  simp only [lowLowOutput,lowInputValues,hm]

/-- Every pair's signed low output uses its original input, including rejection. -/
theorem lowRun_read_low (g : Nat) (v : Values) (out aux : Addr) (c : LowConstants)
    (d : CheckData) (is : List LowIndex) (i : LowIndex) (h : Fin 2)
    (hi : i∈is) (hn : is.Nodup) (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowRun g v out aux c d is).mem.read (lowAddr aux i h) 16=
      lowLowOutput g d.mem (lowAddr out i h) (lowHalfValue v i h) c := by
  induction is generalizing d with
  | nil => simp at hi
  | cons j is ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : j=i
    · subst j
      rw [lowRun,lowRun_read_aux_other _ _ _ _ _ _ _ _ _ hn'.1 hd]
      exact lowPair_read_low _ _ _ _ _ _ _ _
    · have hit : i∈is := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      rw [lowRun,ih _ hit hn'.2]
      exact lowLowOutput_read_eq _ _ _ _ (lowPair_other_input g v out aux c d (Ne.symm he) h hd)

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassHigh` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem shifted_disjoint (out aux : Addr) (d : Addr)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (⟨out+d,2048⟩ : Region).Disjoint ⟨aux+d,2048⟩ := by
  intro a hx hy
  exact hd (a-d)
    (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hx)
    (by simpa only [Region.Contains,BitVec.sub_sub,BitVec.add_comm] using hy)

/-- The complete r0 pass writes the original-input high result at every slot. -/
theorem lowPass_read_high (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : LowIndex) (h : Fin 2)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d n).mem.read (lowAddr (out+BitVec.ofNat 64 (16*k)) i h) 16=
      lowHighOutput g d.mem (lowAddr (out+BitVec.ofNat 64 (16*k)) i h)
        (lowHalfValue (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 p)) i h) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [lowPass_step g work out aux c d (by omega) ho ha,
        lowRun_read_high _ _ _ _ _ _ _ _ _ (allLow_mem i) allLow_nodup (shifted_disjoint out aux _ hd)]
      exact lowHighOutput_read_eq _ _ _
        (lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega) i h hd)
    · rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_]
      · exact ih (by omega) (by omega)
      · intro j _
        have h0 := lowSlice_sep out (by omega : n<8) (by omega : k<8) he i j h 0
        have h1 := lowSlice_sep out (by omega : n<8) (by omega : k<8) he i j h 1
        have h2 := hd.sep (lowAddr_contains out (by omega : k<8) i h) (lowAddr_contains aux (by omega : n<8) j 0)
        have h3 := hd.sep (lowAddr_contains out (by omega : k<8) i h) (lowAddr_contains aux (by omega : n<8) j 1)
        simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
          And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowPassLow` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- The complete r0 pass writes the original-input signed low result at every slot. -/
theorem lowPass_read_low (g : Nat) (work out aux : Addr) (c : LowConstants)
    (d : CheckData) {n k : Nat} (hn : n≤8) (hk : k<n) (i : LowIndex) (h : Fin 2)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩) :
    (lowPassData g work out aux c d n).mem.read (lowAddr (aux+BitVec.ofNat 64 (16*k)) i h) 16=
      lowLowOutput g d.mem (lowAddr (out+BitVec.ofNat 64 (16*k)) i h)
        (lowHalfValue (fun p => Inverse.rawFinalValues (readPair d.mem (work+BitVec.ofNat 64 (16*k)) 128 p)) i h) c := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k
      rw [lowPass_step g work out aux c d (by omega) ho ha,
        lowRun_read_low _ _ _ _ _ _ _ _ _ (allLow_mem i) allLow_nodup (shifted_disjoint out aux _ hd)]
      exact lowLowOutput_read_eq _ _ _ _
        (lowPass_read_future g work out aux c d (Nat.le_refl n) (by omega) i h hd)
    · rw [lowPassData,lowRun_read_other _ _ _ _ _ _ _ _ ?_]
      · exact ih (by omega) (by omega)
      · intro j _
        have h0 := hd.symm.sep (lowAddr_contains aux (by omega : k<8) i h) (lowAddr_contains out (by omega : n<8) j 0)
        have h1 := hd.symm.sep (lowAddr_contains aux (by omega : k<8) i h) (lowAddr_contains out (by omega : n<8) j 1)
        have h2 := lowSlice_sep aux (by omega : n<8) (by omega : k<8) he i j h 0
        have h3 := lowSlice_sep aux (by omega : n<8) (by omega : k<8) he i j h 1
        simpa only [lowAddr,Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.add_zero,Nat.mul_one] using
          And.intro h0 (And.intro h1 (And.intro h2 h3))

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowCoordinates` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

def lowCoeff (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) : Nat :=
  4*u+64*i.2.val+32*h.val+e

theorem lowCoeff_lt {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) :
    lowCoeff u i h e<n := by unfold lowCoeff n; omega

/-- The paired strided vector lane names exactly its contiguous polynomial coefficient. -/
theorem lowAddr_coeff (m : Mem) (base : Addr) (u : Nat) (i : LowIndex) (h : Fin 2)
    {e : Nat} (he : e<4) :
    vword (m.read (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16) e=
      coeffAt m (base+BitVec.ofNat 64 (1024*i.1.val)) (lowCoeff u i h e) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [lowAddr,lowOff,lowCoeff,coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*u+(1024*i.1.val+256*i.2.val+128*h.val)+4*e=
    1024*i.1.val+4*(4*u+64*i.2.val+32*h.val+e) by omega]

theorem lowCoeff_rawIndex (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) :
    4*u+32*(2*i.2.val+h.val)+e=lowCoeff u i h e := by unfold lowCoeff; omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowSemantics` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high part for signed raw inverse outputs, before any memory framing. -/
theorem subHighReduced_spec {g : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417) :
    (lowHighWord g (Inverse.signCorrected (Response.reduceWord (a-b)))).toNat=
      (highBits g (ofInt ((a.toNat:Int)-b.toInt))).toNat := by
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowHighWord_eq hg cb]
  exact Response.subHigh_word hg ha bl bh

/-- The paired rejection flag uses the same strict norm bound as the specification. -/
theorem subLowReduced_norm {g B : Nat} (hg : IsG g) {a b : BitVec 32}
    (ha : a.toNat<Spec.MlDsa.q) (bl : -8380417<b.toInt) (bh : b.toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let c := Inverse.signCorrected (Response.reduceWord (a-b))
    Response.normMask (Response.reduceWord (c-lowHighWord g c*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (ofInt ((a.toNat:Int)-b.toInt))))<B then 0 else -1 := by
  dsimp only
  have hc := Response.subInput_word ha bl bh
  have cb : (Inverse.signCorrected (Response.reduceWord (a-b))).toNat<Spec.MlDsa.q := by
    rw [hc]; exact (ofInt ((a.toNat:Int)-b.toInt)).isLt
  rw [lowReduced_eq hg cb]
  exact Response.subLow_norm hg ha bl bh hB hB'

def lowInputField (m : Mem) (addr : Addr) (raw : BitVec 128) (e : Nat) : Zq :=
 ofInt (((vword (m.read addr 16) e).toNat:Int)-(vword raw e).toInt)

theorem lowInputValues_spec {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    (lowInputValues m addr raw e).toNat=(lowInputField m addr raw e).toNat :=
  Response.subInput_word ha bl bh

theorem lowInputValues_high {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    (lowHighWord g (lowInputValues m addr raw e)).toNat=(highBits g (lowInputField m addr raw e)).toNat :=
  subHighReduced_spec hg ha bl bh

theorem lowInputValues_low {g : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417) :
    let a := lowInputValues m addr raw e
    (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g))).toInt=
      lowBits g (lowInputField m addr raw e) :=
  subLowReduced_spec hg ha bl bh

theorem lowInputValues_norm {g B : Nat} (hg : IsG g) {m : Mem} {addr : Addr} {raw : BitVec 128} {e : Nat}
    (ha : (vword (m.read addr 16) e).toNat<Spec.MlDsa.q)
    (bl : -8380417<(vword raw e).toInt) (bh : (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    let a := lowInputValues m addr raw e
    Response.normMask (Response.reduceWord (a-lowHighWord g a*BitVec.ofNat 32 (2*g)))
      (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=
      if normZq (ofInt (lowBits g (lowInputField m addr raw e)))<B then 0 else -1 :=
  subLowReduced_norm hg ha bl bh hB hB'
end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFieldValues` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- Each high output is the specification's decomposition of the difference. -/
theorem lowHighOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {e : Nat} (he : e<4) (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowHighOutput g m out raw) e).toNat=(highBits g (lowInputField m out raw e)).toNat := by
  rw [lowHighOutput,laneVector_word _ he]
  exact lowInputValues_high hg ha hb.1 hb.2

/-- Each low output has the exact signed low-bits representative, on all paths. -/
theorem lowLowOutput_field {g : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat} (he : e<4) (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    (vword (lowLowOutput g m out raw c) e).toInt=lowBits g (lowInputField m out raw e) := by
  rw [lowLowOutput,laneVector_word _ he,hs]
  exact lowInputValues_low hg ha hb.1 hb.2

/-- The r0 machine mask is zero exactly when the strict low-bits norm passes. -/
theorem lowMask_zero {g B : Nat} (hg : IsG g) {m : Mem} {out : Addr} {raw : BitVec 128}
    {c : LowConstants} {e : Nat}
    (hs : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hl : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hw : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (ha : (vword (m.read out 16) e).toNat<q)
    (hb : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417)
    (hB : 1≤B) (hB' : B≤524288) :
    lowMask g m out raw c e=0 ↔ normZq (ofInt (lowBits g (lowInputField m out raw e)))<B := by
  rw [lowMask,hs,hl,hw,lowInputValues_norm hg ha hb.1 hb.2 hB hB']
  split
  · rename_i h
    exact ⟨fun _ => h,fun _ => rfl⟩
  · rename_i h
    exact ⟨fun hz => False.elim ((by decide : (-1 : BitVec 32)≠0) hz),fun hx => False.elim (h hx)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowDifference` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A raw inverse lane subtracts to exactly the shared paired difference. -/
theorem lowInputField_difference (m : Mem) (challenge secret out : Addr)
    {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) (raw : BitVec 128)
    (hr : ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]!) :
    lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  have hk := lowCoeff_lt hu he i h
  rw [lowInputField,lowAddr_coeff _ _ _ _ _ he,ofInt_sub,ofInt_nat_eq,
    ←polyAt_get _ _ hk,hr,pairedDifference,sub_get _ _ hk]
  rfl

/-- The raw paired inverse lane has the shared product value and strict range. -/
theorem lowHalf_raw_field {m : Mem} {work challenge secret : Addr} {u e : Nat}
    (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues
      (readPair (firstPassMem m work challenge secret 8) (work+BitVec.ofNat 64 (16*u)) 128 p)) i h;
    -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417 ∧
      ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]! := by
  have hv := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt))
    ⟨2*i.2.val+h.val,by omega⟩ he
  simpa only [lowHalfValue,pairedProduct,pairPolyPtr,lowCoeff_rawIndex] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowFirstFrame` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

theorem firstPass_lowInput_read {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    (firstPassMem m work challenge secret 8).read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16=
      m.read (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16 := by
  exact (firstPass_frame (m:=m) (a:=challenge) (b:=secret) (by decide : 8≤8)).read
    (lowAddr_contains out hu i h)
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

theorem firstPass_lowInputField {m : Mem} {work challenge secret out : Addr} {u : Nat}
    (hu : u<8) (i : LowIndex) (h : Fin 2) (raw : BitVec 128) (e : Nat)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩) :
    lowInputField (firstPassMem m work challenge secret 8) (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e := by
  rw [lowInputField,firstPass_lowInput_read hu i h hd]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowLaneField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high and low field values after the initial inverse pass. -/
theorem lowLane_field {m : Mem} {work challenge secret out : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    (vword (lowHighOutput g mem addr raw) e).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (vword (lowLowOutput g mem addr raw c) e).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  constructor
  · rw [lowHighOutput_field hg he hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]
  · rw [lowLowOutput_field hg he hscale hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## `PairedLowStoredField` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowPass_stored_field {m : Mem} {work challenge secret out aux : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨work,2048⟩ : Region).Disjoint ⟨out,2048⟩)
    (ha : (⟨work,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hd : (⟨out,2048⟩ : Region).Disjoint ⟨aux,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) (flags count : BitVec 128) :
    let d : CheckData := ⟨firstPassMem m work challenge secret 8,flags,count⟩
    let result := (lowPassData g work out aux c d 8).mem
    (coeffAt result (pairPolyPtr out i.1.val) (lowCoeff u i h e)).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (coeffAt result (pairPolyPtr aux i.1.val) (lowCoeff u i h e)).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hv := lowLane_field hu he hg i h c hscale hc hs ho.symm hp hy
  constructor
  · rw [pairPolyPtr,←lowAddr_coeff _ out u i h he,
      lowPass_read_high g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.1
  · rw [pairPolyPtr,←lowAddr_coeff _ aux u i h he,
      lowPass_read_low g work out aux c _ (by decide : 8≤8) hu i h ho ha hd]
    exact hv.2

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end
