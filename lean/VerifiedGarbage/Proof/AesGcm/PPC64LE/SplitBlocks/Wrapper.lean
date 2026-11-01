module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Copy
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Gcm.Split
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: callable wrapper composition for the source-prefix core.
/-! # Argument setup and preservation for the POWER8 GCM source-prefix helper -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks.Wrapper
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.SplitBlocks (extraSaved)


def headState (s : State) : State :=
  (s.write .r12 s.sp).write .r11 (s.mem.readW (s.sp+96) 64)

theorem head_ok (s : State) (hr : InRegions (s.rd++s.wr) (s.sp+96) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.argsHead) s (· = headState s) := by
  have ha : exec (.addSp .r12 0) s=some (s.write .r12 s.sp) := by
    simp only [exec,Nat.reducePow,Nat.reduceLT,ite_true,BitVec.add_zero]
  have hr' : InRegions ((s.write .r12 s.sp).rd++(s.write .r12 s.sp).wr)
      ((s.write .r12 s.sp).gpr .r12+BitVec.ofNat 64 96) 8 := by
    exact hr
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SplitBlocks.argsHead,runBlock_cons,runStep_some,runBlock_nil,ha,
    exec_load_d (n := .r12) (off := 96) (by decide) ⟨by decide,by decide⟩ hr',
    RegUpd.gpr_write_self,RegUpd.mem_write,Option.some.injEq,exists_eq_left']
  rfl



def configState (s : State) : State :=
  ((((s.write .r17 (s.gpr .r7)).write .r19 (s.gpr .r8)).write .r7 (s.gpr .r9)).write
    .r8 (s.gpr .r10)).write .r9 (s.gpr .r11)

theorem config_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.argsConfig) s (· = configState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SplitBlocks.argsConfig,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


def restState (s : State) : State :=
  configState {s with mem := Spill.saveMem s.mem (s.gpr .r11) s.gpr extraSaved}

theorem rest_ok (s : State)
    (hw : ∀ p ∈ extraSaved, InRegions s.wr (s.gpr .r11+BitVec.ofNat 64 p.2) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.argsRest) s (· = restState s) := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.argsRest,WP.block_append_iff]
  have hs : WP isa (.block (Spill.saveCode .r11 extraSaved)) s
      (· = {s with mem := Spill.saveMem s.mem (s.gpr .r11) s.gpr extraSaved}) := by
    rw [← List.append_nil (Spill.saveCode .r11 extraSaved)]
    exact Spill.save_ok (by decide) (by decide) hw (WP.block_nil rfl)
  refine WP.mono hs fun t ht => ?_
  subst t
  exact config_ok _


theorem rest_saved (s : State) :
    Spill.Saved (s.gpr .r11) s.gpr extraSaved (restState s).mem :=
  Spill.saveMem_saved (by decide) _ _ _


theorem rest_frame (s : State) :
    Frame [⟨s.gpr .r11+152,16⟩] s.mem (restState s).mem :=
  Spill.saveMem_frame (lo := 152) (n := 16) (by decide) (by decide) _ _ _


theorem restore_ok (base : State) (g : Reg → BitVec 64)
    (hs : Spill.Saved (base.gpr .r31) g extraSaved base.mem)
    (hr : ∀ p ∈ extraSaved, InRegions (base.rd++base.wr) (base.gpr .r31+BitVec.ofNat 64 p.2) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.restoreExtra) base
      (Spill.Restored g extraSaved base) :=
  Spill.restore_wp (by decide) rfl (by decide) (by decide) hr hs


structure Layout (base : State) (n count : Nat) : Prop where
  wrapper : Blocks.WrapperLayout base n
  bound : count≤n
  left : base.gpr .r19=BitVec.ofNat 64 count
  reads : InRegions (base.rd++base.wr) (base.gpr .r17) (16*count)
  disjoint : ∀ r ∈ Blocks.wrapperFullWrites base n, (sourceRegion base count).Disjoint r


def plain (base : State) (count i : Nat) : Spec.Gcm.Block :=
  if i<count then Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))
  else Spec.Gcm.blockAt base.mem (base.gpr .r7+BitVec.ofNat 64 (16*i))


def blocks (base : State) (count start len : Nat) : List Spec.Gcm.Block :=
  (List.range len).map (fun i => plain base count (start+i))


def ciphertext (base : State) (nr count len : Nat) : List Spec.Gcm.Block :=
  Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr)
    (Spec.Gcm.blockAt base.mem (base.gpr .r5)) (blocks base count 0 len)


def kernelBase (base : State) : State := Blocks.bulkArgsState (Blocks.wrapperEntryState base)


theorem kernel_source (base : State) :
    (kernelBase base).gpr .r17=base.gpr .r17 ∧ (kernelBase base).gpr .r19=base.gpr .r19 := by
  constructor <;> simp only [kernelBase,Blocks.bulkArgsState,Blocks.wrapperEntryState,
    Blocks.wrapperConfigState,RegUpd.gpr_write,reduceCtorEq,ite_false]


theorem Layout.kernel {base : State} {n count : Nat} (lay : Layout base n count) :
    SourceLayout (kernelBase base) (n-n%8) count := by
  refine ⟨(kernel_source base).2.trans lay.left,?_,by have := lay.bound; have := lay.wrapper.core.size; omega,?_,?_⟩
  · simpa only [kernelBase,Blocks.bulkArgsState,Blocks.wrapperEntryState,Blocks.wrapperConfigState,
      RegUpd.rd_write,RegUpd.wr_write,RegUpd.gpr_write,reduceCtorEq,ite_false] using lay.reads
  · have hd := lay.disjoint ⟨base.gpr .r9,2112⟩ (by simp [Blocks.wrapperFullWrites])
    have hs : Region.Sub (Blocks.coreWork (kernelBase base)) ⟨base.gpr .r9,2112⟩ := by
      change Region.Sub ⟨base.gpr .r9+64,2048⟩ ⟨base.gpr .r9,2112⟩
      exact Offset.sub_base _ (by decide)
    simpa only [sourceRegion,(kernel_source base).1] using hd.sub_right hs
  · have hd := lay.disjoint (Blocks.coreData (Blocks.wrapperView base) n) (by simp [Blocks.wrapperFullWrites])
    have hs : Region.Sub (Blocks.coreData (kernelBase base) (n-n%8))
        (Blocks.coreData (Blocks.wrapperView base) n) := Region.sub_prefix (by change 16*(n-n%8)≤16*n; omega)
    simpa only [sourceRegion,(kernel_source base).1] using hd.sub_right hs


theorem header_source {base : State} {n count i : Nat} (lay : Layout base n count) (hi : i<count) :
    Spec.Gcm.blockAt (Blocks.wrapperHeaderMem base) (base.gpr .r17+BitVec.ofNat 64 (16*i))=
      Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i)) := by
  apply Blocks.block_frame (Blocks.wrapperHeader_frame base)
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  exact ((lay.disjoint ⟨base.gpr .r9,2112⟩ (by simp [Blocks.wrapperFullWrites])).sub_left
    (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega))).sub_right
      (Region.sub_prefix (by decide))


theorem kernel_plain {base : State} {n count i : Nat} (lay : Layout base n count) (hi : i<n) :
    plaintext (kernelBase base) count i=plain base count i := by
  simp only [plaintext,plain,Blocks.defaultPlaintext,kernelBase,Blocks.bulkArgsState,
    Blocks.wrapperEntryState,Blocks.wrapperConfigState,RegUpd.mem_write,RegUpd.gpr_write,
    reduceCtorEq,ite_true,ite_false]
  by_cases hc : i<count
  · simp only [ite_eq_left hc]; exact header_source lay hc
  · simp only [ite_eq_right hc]
    apply Blocks.block_frame (Blocks.wrapperHeader_frame base)
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact (lay.wrapper.header_disjoint (r := Blocks.coreData (Blocks.wrapperView base) n) (by simp)).sub_left
      (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*n) (by omega))


abbrev Mid (base : State) (n nr count k : Nat) (s : State) :=
  Blocks.WrapperMidWith base n nr k (ciphertext base nr count)
    (fun j => Spec.Gcm.blocksAt base.mem (base.gpr .r7+BitVec.ofNat 64 (16*j)) (n-j)) s [.r17,.r19]


theorem bulk_output {base u : State} {n nr count : Nat} (lay : Layout base n count) (hnr : nr<15)
    (hc : Blocks.CoreResultWith (kernelBase base) (n-n%8) nr
      (plaintext (kernelBase base) count) (input (kernelBase base) count) u) :
    Spec.Gcm.blocksAt u.mem (base.gpr .r7) (n-n%8)=ciphertext base nr count (n-n%8) ∧
    Spec.Gcm.blockAt u.mem (base.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (n-n%8) (Spec.Gcm.blockAt base.mem (base.gpr .r5)) ∧
    Spec.Gcm.blockAt u.mem (base.gpr .r6)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH base.mem (base.gpr .r3))
      (Spec.Gcm.blockAt base.mem (base.gpr .r6)) (ciphertext base nr count (n-n%8)) := by
  have hp : (List.range (n-n%8)).map (plaintext (kernelBase base) count)=blocks base count 0 (n-n%8) := by
    apply List.map_congr_left
    intro i hi
    simpa only [Nat.zero_add] using kernel_plain lay (by have := List.mem_range.mp hi; omega)
  have hd : Spec.Gcm.blocksAt u.mem (base.gpr .r7) (n-n%8)=Spec.Gcm.ctr32
      (Spec.Gcm.ctxCiph (Blocks.wrapperHeaderMem base) (base.gpr .r3) nr)
      (Spec.Gcm.blockAt (Blocks.wrapperHeaderMem base) (base.gpr .r5))
      ((List.range (n-n%8)).map (plaintext (kernelBase base) count)) := hc.ciphertext
  rw [Blocks.header_ctxCipher lay.wrapper hnr,Blocks.header_counter lay.wrapper,hp] at hd
  have hctr : Spec.Gcm.blockAt u.mem (base.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (n-n%8)
      (Spec.Gcm.blockAt (Blocks.wrapperHeaderMem base) (base.gpr .r5)) := hc.counter
  rw [Blocks.header_counter lay.wrapper] at hctr
  have hy : Spec.Gcm.blockAt u.mem (base.gpr .r6)=Spec.Gcm.ghashFrom
      (Spec.Gcm.ctxH (Blocks.wrapperHeaderMem base) (base.gpr .r3))
      (Spec.Gcm.blockAt (Blocks.wrapperHeaderMem base) (base.gpr .r6))
      (Spec.Gcm.blocksAt u.mem (base.gpr .r7) (n-n%8)) := hc.y
  rw [Blocks.header_h lay.wrapper,Blocks.header_y lay.wrapper,hd] at hy
  exact ⟨hd,hctr,hy⟩


theorem fixed_keep {base s t : State} (hf : Blocks.WrapperFixed base s) (hk : Keep coreVolatile s t) :
    Blocks.WrapperFixed base t :=
  ⟨hk.2.1.trans hf.rd,hk.2.2.trans hf.wr,
    (hk.gpr (by decide)).trans hf.ctx,(hk.gpr (by decide)).trans hf.rounds,
    (hk.gpr (by decide)).trans hf.counter,(hk.gpr (by decide)).trans hf.y,(hk.gpr (by decide)).trans hf.work⟩


theorem saved_header (base : State) (g : Reg → BitVec 64)
    (hs : Spill.Saved (base.gpr .r9) g extraSaved base.mem) :
    Spill.Saved (base.gpr .r9) g extraSaved (Blocks.wrapperHeaderMem base) :=
  hs.frame_in (lo := 152) (n := 16) (by decide) (Blocks.wrapperHeader_frame base) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint_base _ (by decide) (by decide))


theorem saved_core {base u : State} {n nr count : Nat} (lay : Layout base n count) (g : Reg → BitVec 64)
    (hs : Spill.Saved (base.gpr .r9) g extraSaved base.mem)
    (hc : Blocks.CoreResultWith (kernelBase base) (n-n%8) nr
      (plaintext (kernelBase base) count) (input (kernelBase base) count) u) :
    Spill.Saved (base.gpr .r9) g extraSaved u.mem := by
  refine (saved_header base g hs).frame_in (lo := 152) (n := 16) (by decide) hc.narrow ?_
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change Region.Disjoint ⟨base.gpr .r9+152,16⟩ ⟨base.gpr .r9+64,88⟩
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · change Region.Disjoint ⟨base.gpr .r9+152,16⟩ ⟨base.gpr .r9+64+128,1920⟩
    have h : base.gpr .r9+64+128=base.gpr .r9+BitVec.ofNat 64 192 := by
      change base.gpr .r9+BitVec.ofNat 64 64+BitVec.ofNat 64 128=_
      exact Offset.add_add ..
    rw [h]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  · exact ((lay.wrapper.scratch (Blocks.coreData (Blocks.wrapperView base) n) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))).sub_right
        (Region.sub_prefix (by change 16*(n-n%8)≤16*n; omega))
  · exact (lay.wrapper.scratch (Blocks.coreCounter (Blocks.wrapperView base)) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))
  · exact (lay.wrapper.scratch (Blocks.coreY (Blocks.wrapperView base)) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))


theorem bulk_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (n nr count : Nat) (lay : Layout base n count) (hn : base.gpr .r8=BitVec.ofNat 64 n)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hmin : 9<nr) (hmax : nr<15) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.bulk (Blocks.wrapperEntryState base) fun t =>
      Mid base n nr count (n-n%8) t ∧ input base count (n-n%8) (t.gpr .r17) (t.gpr .r19) ∧
      ∀ g, Spill.Saved (base.gpr .r9) g extraSaved base.mem → Spill.Saved (base.gpr .r9) g extraSaved t.mem := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.bulk]
  apply WP.seq
  refine WP.mono (Blocks.bulkArgs_ok (Blocks.wrapperEntryState base)) fun args hargs => ?_
  subst args
  have ha := Blocks.bulkArgs_result (Blocks.wrapperEntry_fixed base) ((Blocks.wrapperEntry_count base).trans hn)
  have hH : (kernelBase base).gpr .r8=(kernelBase base).gpr .r3+240#64 := by
    change (Blocks.bulkArgsState (Blocks.wrapperEntryState base)).gpr .r8=
      (Blocks.bulkArgsState (Blocks.wrapperEntryState base)).gpr .r3+240#64
    rw [ha.h,ha.ctx]; rfl
  apply WP.seq
  refine WP.mono (core_ok _ (n-n%8) nr count (Blocks.bulkEntry_layout lay.wrapper) lay.kernel
    ha.left (by omega) hmin hmax (ha.rounds.trans hr) hH) fun u ⟨hu,hku⟩ => ?_
  refine WP.mono (Blocks.bulkRest_ok u) fun t ht => ?_
  subst t
  have h25 : u.gpr .r25=BitVec.ofNat 64 n :=
    (hku.gpr (by decide)).trans (((Blocks.bulkArgs_keep _).gpr (by decide)).trans ((Blocks.wrapperEntry_count base).trans hn))
  have h30 : u.gpr .r30=base.gpr .r7 :=
    (hku.gpr (by decide)).trans (((Blocks.bulkArgs_keep _).gpr (by decide)).trans (Blocks.wrapperEntry_data base))
  have hp := Blocks.bulkRest_pointer u n h25
  have hout := bulk_output lay hmax hu
  have hkeep := ((((Blocks.wrapperEntry_keep base lay.wrapper).trans (Blocks.bulkArgs_keep _)).trans hku).trans (Blocks.bulkRest_keep u))
  refine ⟨⟨by omega,Blocks.bulkRest_fixed (fixed_keep ha.fixed hku),?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · exact hp.1.trans (congrArg (fun p => p+BitVec.ofNat 64 (16*(n-n%8))) h30)
  · simpa only [show n-(n-n%8)=n%8 by omega] using hp.2
  · intro r hr hs
    have hpres : ∀ r ∈ preserved, r ∉ Blocks.coreVolatile := by decide
    have hv := hpres r hr
    have hs' : r ∉ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst := fun he => hs (List.mem_append_left _ he)
    have h17 : r≠.r17 := fun he => hs (List.mem_append_right _ (by simp [he]))
    have h19 : r≠.r19 := fun he => hs (List.mem_append_right _ (by simp [he]))
    have h25 : r≠.r25 := fun he => hs' (by simp [Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,he])
    have h30 : r≠.r30 := fun he => hs' (by simp [Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,he])
    apply hkeep.gpr
    simpa only [coreVolatile,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using
      And.intro (And.intro (And.intro (And.intro hv hs') hv) ⟨hv,h17,h19⟩) ⟨hv,h25,h30⟩
  · simpa only [Blocks.bulkRest_mem] using Blocks.bulk_frame hu
  · simpa only [Blocks.bulkRest_mem] using hout.1
  · simpa only [Blocks.bulkRest_mem] using Blocks.bulk_pending lay.wrapper hu
  · simpa only [Blocks.bulkRest_mem] using hout.2.1
  · simpa only [Blocks.bulkRest_mem] using hout.2.2
  · have hh := hu.input
    change input (kernelBase base) count (n-n%8) (u.gpr .r17) (u.gpr .r19) at hh
    simpa only [input,(kernel_source base).1,Blocks.bulkRestState,RegUpd.gpr_write,reduceCtorEq,ite_false] using hh
  · intro g hg
    exact saved_core (u := u) lay g hg hu



theorem source_frame {base s : State} {n count i : Nat} (lay : Layout base n count)
    (hf : Frame (Blocks.wrapperWrites base n) (Blocks.wrapperHeaderMem base) s.mem) (hi : i<count) :
    Spec.Gcm.blockAt s.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))=
      Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i)) := by
  apply Blocks.block_frame (Blocks.wrapper_final_frame hf)
  intro r hr
  exact (lay.disjoint r hr).sub_left (Offset.sub_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega))


theorem copy_config {base s : State} {n nr count k : Nat} (lay : Layout base n count)
    (hs : Mid base n nr count k s) (hin : input base count k (s.gpr .r17) (s.gpr .r19)) :
    Copy.Config s (n-k) (count-k) := by
  refine ⟨by have := lay.bound; omega,by have := lay.wrapper.core.size; omega,hin.2,?_,?_,?_⟩
  · intro i hi
    rw [hs.fixed.rd,hs.fixed.wr,source_addr hi hin]
    exact Covers.one lay.reads _ _ ⟨_,List.mem_singleton_self _,
      Offset.contains_base _ (d := 16*(k+i)) (n := 16) (k := 16*count) (by omega)
        (by have := lay.bound; have := lay.wrapper.core.size; omega)⟩
  · intro i hi
    rw [hs.fixed.wr,hs.ptr,Offset.add_add]
    exact lay.wrapper.core.writes _ _ ⟨Blocks.coreData (Blocks.wrapperView base) n,by simp,
      Offset.contains_base _ (d := 16*k+16*i) (n := 16) (k := 16*n)
        (by have := lay.bound; omega) (by have := lay.bound; have := lay.wrapper.core.size; omega)⟩
  · have hd := lay.disjoint (Blocks.coreData (Blocks.wrapperView base) n) (by simp [Blocks.wrapperFullWrites])
    rw [hs.ptr,hin.1]
    exact (hd.sub_left (Offset.sub_base _ (d := 16*min k count) (n := 16*(count-k)) (k := 16*count)
      (by omega))).sub_right (Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n)
        (by have := hs.bound; omega))



theorem ciphertext_zero (base : State) (nr count : Nat) : ciphertext base nr count 0=[] := by
  simp only [ciphertext,blocks,List.range_zero,List.map_nil,Spec.Gcm.ctr32,Spec.Gcm.keystream,
    List.length_nil,List.zipWith_nil_left]


theorem mid_initial (base : State) (n nr count : Nat) (lay : Layout base n count)
    (hn : base.gpr .r8=BitVec.ofNat 64 n) : Mid base n nr count 0 (Blocks.wrapperEntryState base) := by
  have hs := Blocks.wrapperMid_initial base n nr lay.wrapper hn
  refine ⟨hs.bound,hs.fixed,hs.ptr,hs.count,?_,hs.frame,?_,hs.pending,hs.counter,?_⟩
  · intro r hr hn
    exact hs.keep r hr (fun he => hn (List.mem_append_left _ he))
  · simp only [ciphertext_zero,Spec.Gcm.blocksAt,List.range_zero,List.map_nil]
  · simpa only [ciphertext_zero,Blocks.wrapperCiphertext,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,
      Spec.Gcm.ctr32,Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left] using hs.y


theorem optional_bulk_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (n nr count : Nat) (lay : Layout base n count) (hn : base.gpr .r8=BitVec.ofNat 64 n)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hmin : 9<nr) (hmax : nr<15) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.maybeBulk (Blocks.wrapperEntryState base) fun t =>
      ∃ k, k≤n ∧ n-k<32 ∧ Mid base n nr count k t ∧ input base count k (t.gpr .r17) (t.gpr .r19) ∧
        ∀ g, Spill.Saved (base.gpr .r9) g extraSaved base.mem → Spill.Saved (base.gpr .r9) g extraSaved t.mem := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.maybeBulk]
  have ht := Blocks.wrapper_bulk_test base hn (by have := lay.wrapper.core.size; omega)
  by_cases hsmall : n<32
  · refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,ht.mpr hsmall]; rfl)
      (fun _ => WP.block_nil ⟨0,by omega,by omega,mid_initial base n nr count lay hn,?_,?_⟩) (by simp)
    · change input base count 0 (base.gpr .r17) (base.gpr .r19)
      simp only [input,Nat.zero_min,Nat.mul_zero,BitVec.add_zero,Nat.sub_zero,lay.left,and_self]
    · exact saved_header base
  · have hne : (Blocks.wrapperEntryState base).gpr .r12≠0 := fun he => hsmall (ht.mp he)
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    exact WP.mono (bulk_ok base n nr count lay hn hr hmin hmax) fun t hh =>
      ⟨n-n%8,by omega,by omega,hh⟩



theorem copy_pending {base s t : State} {n nr count k : Nat} (lay : Layout base n count)
    (hs : Mid base n nr count k s) (hin : input base count k (s.gpr .r17) (s.gpr .r19))
    (ht : Copy.Result s (n-k) (count-k) t) :
    Spec.Gcm.blocksAt t.mem (base.gpr .r7+BitVec.ofNat 64 (16*k)) (n-k)=blocks base count k (n-k) := by
  unfold Spec.Gcm.blocksAt blocks
  apply List.map_congr_left
  intro i hi
  have hi : i<n-k := List.mem_range.mp hi
  have hb := ht.blockAt (by have := lay.bound; omega) hi
  rw [hs.ptr] at hb
  rw [hb]
  by_cases hic : i<count-k
  · rw [ite_eq_left hic,source_addr hic hin]
    simp only [plain,ite_eq_left (show k+i<count by omega)]
    exact source_frame lay hs.frame (by omega)
  · rw [ite_eq_right hic]
    have hp := List.getElem_of_eq hs.pending (i := i)
      (by simpa only [Spec.Gcm.blocksAt,List.length_map,List.length_range] using hi)
    simp only [Spec.Gcm.blocksAt,List.getElem_map,List.getElem_range] at hp
    rw [hp,plain,ite_eq_right (show ¬k+i<count by omega),Offset.add_add]
    exact congrArg (fun j => Spec.Gcm.blockAt base.mem (base.gpr .r7+BitVec.ofNat 64 j)) (by omega)



abbrev Copied (base : State) (n nr count k : Nat) (s : State) :=
  Blocks.WrapperMidWith base n nr k (ciphertext base nr count)
    (fun j => blocks base count j (n-j)) s [.r17,.r19]


theorem copy_frame {base s t : State} {n nr count k : Nat} (hs : Mid base n nr count k s)
    (ht : Copy.Result s (n-k) (count-k) t) :
    Frame (Blocks.wrapperWrites base n) s.mem t.mem := by
  refine ht.frame.sub fun r hr => ?_
  rw [List.mem_singleton] at hr
  subst r
  refine ⟨Blocks.coreData (Blocks.wrapperView base) n,by simp [Blocks.wrapperWrites],?_⟩
  rw [hs.ptr]
  exact Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n) (by have := hs.bound; omega)


theorem copied {base s t : State} {n nr count k : Nat} (lay : Layout base n count)
    (hs : Mid base n nr count k s) (hin : input base count k (s.gpr .r17) (s.gpr .r19))
    (ht : Copy.Result s (n-k) (count-k) t) : Copied base n nr count k t := by
  have hk : Keep coreVolatile s t := ht.keep.mono (by simp [Copy.registers,coreVolatile,Blocks.coreVolatile])
  have hf := copy_frame hs ht
  have hmem : ∀ r ∈ [Blocks.coreCounter (Blocks.wrapperView base),Blocks.coreY (Blocks.wrapperView base)],
      r.Disjoint ⟨s.gpr .r30,16*(n-k)⟩ := by
    intro r hr
    rw [hs.ptr]
    exact (lay.wrapper.core.data r (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using Or.inr hr)).sub_right
      (Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n) (by have := hs.bound; omega))
  have hcounter : Spec.Gcm.blockAt t.mem (base.gpr .r5)=Spec.Gcm.blockAt s.mem (base.gpr .r5) :=
    Blocks.block_frame ht.frame (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hmem (Blocks.coreCounter (Blocks.wrapperView base)) (by simp))
  have hy : Spec.Gcm.blockAt t.mem (base.gpr .r6)=Spec.Gcm.blockAt s.mem (base.gpr .r6) :=
    Blocks.block_frame ht.frame (by
      intro r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hmem (Blocks.coreY (Blocks.wrapperView base)) (by simp))
  refine ⟨hs.bound,fixed_keep hs.fixed hk,?_,?_,?_,hs.frame.trans hf,?_,copy_pending lay hs hin ht,
    hcounter.trans hs.counter,hy.trans hs.y⟩
  · exact (hk.gpr (by decide)).trans hs.ptr
  · exact (hk.gpr (by decide)).trans hs.count
  · intro r hr hn
    have hvol : ∀ r ∈ preserved, r ∉ Blocks.coreVolatile := by decide
    have h17 : r≠.r17 := fun he => hn (List.mem_append_right _ (by simp [he]))
    have h19 : r≠.r19 := fun he => hn (List.mem_append_right _ (by simp [he]))
    exact (hk.gpr (by simpa only [coreVolatile,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] using
      (And.intro (hvol r hr) ⟨h17,h19⟩))).trans (hs.keep r hr hn)
  · refine (Blocks.blocks_frame ht.frame ?_).trans hs.completed
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    rw [hs.ptr]
    exact Offset.base_disjoint _ (by omega) (by have := lay.wrapper.core.size; have := hs.bound; omega)


theorem copy_saved {base s t : State} {n nr count k : Nat} (lay : Layout base n count)
    (hs : Mid base n nr count k s) (ht : Copy.Result s (n-k) (count-k) t) (g : Reg → BitVec 64)
    (hsv : Spill.Saved (base.gpr .r9) g extraSaved s.mem) :
    Spill.Saved (base.gpr .r9) g extraSaved t.mem := by
  refine hsv.frame_in (lo := 152) (n := 16) (by decide) ht.frame ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [hs.ptr]
  exact ((lay.wrapper.scratch (Blocks.coreData (Blocks.wrapperView base) n) (by simp)).symm.sub_left
    (Offset.sub_base _ (d := 152) (n := 16) (k := 2112) (by decide))).sub_right
      (Offset.sub_base _ (d := 16*k) (n := 16*(n-k)) (k := 16*n) (by have := hs.bound; omega))



def restoredBase (base : State) (g : Reg → BitVec 64) : State :=
  (base.write .r17 (g .r17)).write .r19 (g .r19)


theorem restored_header (base : State) (g : Reg → BitVec 64) :
    Blocks.wrapperHeaderMem (restoredBase base g)=Blocks.wrapperHeaderMem base := by
  simp only [Blocks.wrapperHeaderMem,Impl.AesGcm.PPC64LE.Blocks.wrapperSaved,Spill.saveMem,
    restoredBase,RegUpd.mem_write,RegUpd.gpr_write,RegUpd.lr_write,reduceCtorEq,ite_false]


theorem restored_layout {base : State} {n count : Nat} (lay : Layout base n count) (g : Reg → BitVec 64) :
    Blocks.WrapperLayout (restoredBase base g) n := by
  refine ⟨lay.wrapper.core.congr ?_ ?_ ?_ ?_ ?_ ?_ ?_,?_,?_,?_⟩
  all_goals first
    | solve | simp only [Blocks.wrapperView,restoredBase,RegUpd.gpr_write,RegUpd.rd_write,RegUpd.wr_write,
        reduceCtorEq,ite_true,ite_false]
    | simpa only [restoredBase,RegUpd.gpr_write,RegUpd.wr_write,reduceCtorEq,ite_false] using lay.wrapper.header
    | simpa only [Blocks.coreKey,Blocks.coreCounter,Blocks.coreY,Blocks.coreData,Blocks.wrapperView,
        restoredBase,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using lay.wrapper.scratch
    | simpa only [restoredBase,RegUpd.gpr_write,reduceCtorEq,ite_false] using lay.wrapper.fit


theorem restored_mid {base s t : State} {n nr count k : Nat} (hs : Copied base n nr count k s)
    (g : Reg → BitVec 64) (ht : Spill.Restored g extraSaved s t) :
    Blocks.WrapperMidWith (restoredBase base g) n nr k (ciphertext base nr count)
      (fun j => blocks base count j (n-j)) t := by
  have hk : Keep coreVolatile s t := by
    refine ⟨fun r hr => ht.other r ?_,ht.rd,ht.wr⟩
    have hn : r ∉ [.r17,.r19] := fun he => hr ((show [.r17,.r19] ⊆ coreVolatile by simp [coreVolatile]) he)
    exact hn
  have hfixed := fixed_keep hs.fixed hk
  have hfixed' : Blocks.WrapperFixed (restoredBase base g) t := by
    rcases hfixed with ⟨a,b,c,d,e,f,h⟩
    exact ⟨a,b,c,d,e,f,h⟩
  refine ⟨hs.bound,hfixed',?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [restoredBase,RegUpd.gpr_write,reduceCtorEq,ite_false] using (hk.gpr (by decide)).trans hs.ptr
  · exact (hk.gpr (by decide)).trans hs.count
  · intro r hr hn
    change r ∉ Impl.AesGcm.PPC64LE.Blocks.wrapperSaved.map Prod.fst at hn
    by_cases h17 : r=.r17
    · subst r
      simpa only [restoredBase,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true] using
        ht.gpr (.r17,152) (by decide)
    · by_cases h19 : r=.r19
      · subst r
        simpa only [restoredBase,RegUpd.gpr_write_self] using ht.gpr (.r19,160) (by decide)
      · have ho := ht.other r (by simp [extraSaved,h17,h19])
        rw [ho]
        simpa only [restoredBase,RegUpd.gpr_write,h17,h19,ite_false] using
          hs.keep r hr (by simpa only [List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,not_or] using
            (And.intro hn (And.intro h17 h19)))
  · rw [restored_header]
    simpa only [ht.mem,Blocks.wrapperWrites,Blocks.coreWork,Blocks.coreData,Blocks.coreCounter,Blocks.coreY,
      Blocks.wrapperView,restoredBase,RegUpd.gpr_write,reduceCtorEq,ite_true,ite_false] using hs.frame
  · simpa only [ht.mem,restoredBase,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using hs.completed
  · simpa only [ht.mem,restoredBase,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using hs.pending
  · simpa only [ht.mem,restoredBase,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using hs.counter
  · simpa only [ht.mem,restoredBase,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using hs.y


theorem blocks_add (base : State) (count start a b : Nat) :
    blocks base count start (a+b)=blocks base count start a ++ blocks base count (start+a) b := by
  simp only [blocks,List.range_add,List.map_append,List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply,Nat.add_assoc,Nat.add_comm a i]


theorem ciphertext_split (base : State) (nr count n k : Nat) (hk : k≤n) :
    ciphertext base nr count n=ciphertext base nr count k ++
      Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph base.mem (base.gpr .r3) nr)
        (Nat.repeat Spec.Gcm.inc32 k (Spec.Gcm.blockAt base.mem (base.gpr .r5))) (blocks base count k (n-k)) := by
  unfold ciphertext
  rw [show n=k+(n-k) by omega,blocks_add,VG.Proof.Gcm.ctr32_append]
  simp only [blocks,List.length_map,List.length_range,Nat.zero_add,Nat.add_sub_cancel_left]



theorem slot_read {base s : State} {n count : Nat} (lay : Layout base n count)
    (hrd : s.rd=base.rd) (hwr : s.wr=base.wr) (hwork : s.gpr .r31=base.gpr .r9) :
    ∀ p ∈ extraSaved, InRegions (s.rd++s.wr) (s.gpr .r31+BitVec.ofNat 64 p.2) 8 := by
  intro p hp
  rw [hrd,hwr,hwork]
  have ho : ∀ p ∈ extraSaved, 64≤p.2 ∧ p.2+8≤2112 := by decide
  exact Covers.right lay.wrapper.core.writes _ _ ⟨Blocks.coreWork (Blocks.wrapperView base),by simp,
    Offset.contains _ (d := p.2) (n := 8) (e := 64) (k := 2048) (ho p hp).1 (ho p hp).2 (by decide)⟩


theorem body_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] [VG.Proof.Gcm.PPC64LE.GhashLaw]
    (base : State) (n nr count : Nat) (lay : Layout base n count) (hn : base.gpr .r8=BitVec.ofNat 64 n)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hv : nr=10 ∨ nr=12 ∨ nr=14) (g : Reg → BitVec 64)
    (hsv : Spill.Saved (base.gpr .r9) g extraSaved base.mem) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.body base
      (Blocks.WrapperResultWith (restoredBase base g) n nr (ciphertext base nr count n)) := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.body]
  apply WP.seq
  refine WP.mono (Blocks.wrapperEntry_ok base (fun off ho => lay.wrapper.header _ _
    ⟨⟨base.gpr .r9,64⟩,by simp,Offset.contains_base _ ho (by omega)⟩)) fun entry he => ?_
  subst entry
  apply WP.seq
  refine WP.mono (optional_bulk_ok base n nr count lay hn hr
    (by rcases hv with h | h | h <;> omega) (by rcases hv with h | h | h <;> omega)) fun mid hm => ?_
  obtain ⟨k,hkn,_,hm,hin,hkeepSaved⟩ := hm
  apply WP.seq
  refine WP.mono (Copy.ok mid (n-k) (count-k) (copy_config lay hm hin)) fun copiedState hc => ?_
  have hcopied := copied lay hm hin hc
  have hslots := copy_saved lay hm hc g (hkeepSaved g hsv)
  have hslots' : Spill.Saved (copiedState.gpr .r31) g extraSaved copiedState.mem := by
    rw [hcopied.fixed.work]; exact hslots
  apply WP.seq
  refine WP.mono (restore_ok copiedState g hslots'
    (slot_read lay hcopied.fixed.rd hcopied.fixed.wr hcopied.fixed.work)) fun restored ht => ?_
  have hmid := restored_mid hcopied g ht
  apply WP.seq
  refine WP.mono (Blocks.wrapper_tailWith_ok (restored_layout lay g) hmid
    (by exact hr) hv ?_) fun done hd => ?_
  · simpa only [restoredBase,RegUpd.gpr_write,RegUpd.mem_write,reduceCtorEq,ite_false] using
      ciphertext_split base nr count n k hkn
  · exact Blocks.wrapper_finish (restored_layout lay g) hd



theorem blocks_spec (base : State) (n count : Nat) (hc : count≤n) :
    blocks base count 0 n=Spec.Gcm.blocksAt base.mem (base.gpr .r17) count ++
      (Spec.Gcm.blocksAt base.mem (base.gpr .r7) n).drop count := by
  apply List.ext_getElem (by simp only [blocks,Spec.Gcm.blocksAt,List.length_map,List.length_range,
    List.length_append,List.length_drop]; omega)
  intro i hi hi'
  have hi : i<n := by simpa only [blocks,List.length_map,List.length_range] using hi
  simp only [blocks,List.getElem_map,List.getElem_range,Nat.zero_add]
  by_cases hic : i<count
  · rw [List.getElem_append_left (by simpa only [Spec.Gcm.blocksAt,List.length_map,List.length_range] using hic)]
    simp only [Spec.Gcm.blocksAt,List.getElem_map,List.getElem_range,plain,ite_eq_left hic]
  · rw [List.getElem_append_right (by simpa only [Spec.Gcm.blocksAt,List.length_map,List.length_range] using Nat.le_of_not_gt hic)]
    simp only [Spec.Gcm.blocksAt,List.length_map,List.length_range,List.getElem_drop,List.getElem_map,
      List.getElem_range,plain,ite_eq_right hic,Nat.add_sub_cancel' (Nat.le_of_not_gt hic)]

end VG.Proof.AesGcm.PPC64LE.SplitBlocks.Wrapper
