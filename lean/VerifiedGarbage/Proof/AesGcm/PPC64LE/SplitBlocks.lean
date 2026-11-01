module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Lit

import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit

meta import VerifiedGarbage.Impl.AesGcm.PPC64LE.SplitBlocks
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Groups
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Lit

-- separate module: source-prefix reader proofs are shared by the kernel and its wrapper.
/-! # POWER8 GCM loads from an external source prefix and destination suffix -/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks
open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE.Blocks (dataReg dataOffset dataRegs)
open VG.Proof.Aes.PPC64LE.Crypto (Local)

def readValue (s : State) (count i : Nat) : BitVec 128 :=
  swapDwords (s.mem.read ((if i<count then s.gpr .r17 else s.gpr .r6)+BitVec.ofNat 64 (16*i)) 16)

theorem selector_ok (i count : Nat) (hi : i<8) (hc : count<8) (s : State)
    (hr : s.gpr .r19=BitVec.ofNat 64 count) :
    WP isa (.block ([.subi .r12 .r19 (i+1),.lsr .d .r12 .r12 63] : List Instr)) s fun t =>
      t.gpr .r12=(if i<count then 0 else 1) ∧ Local [.r12] [] s t := by
  have he : WP isa (.block ([.subi .r12 .r19 (i+1),.lsr .d .r12 .r12 63] : List Instr)) s
      (· = (s.write .r12 (s.gpr .r19-BitVec.ofNat 64 (i+1))).write .r12
        ((s.gpr .r19-BitVec.ofNat 64 (i+1)) >>> 63)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons,runStep_some,runBlock_nil,
      exec_subi (n := .r19) (imm := i+1) (by decide) (by omega),
      exec_lsr_d (sh := 63) (by decide),RegUpd.gpr_write_self,Option.some.injEq,exists_eq_left']
  refine WP.mono he fun t ht => ?_
  subst t
  refine ⟨?_,?_⟩
  · rw [RegUpd.gpr_write_self,hr,VG.Proof.AesGcm.PPC64LE.shr63 (by omega) (by omega)]
    by_cases h : i<count
    · simp only [ite_eq_left h,ite_eq_right (show ¬count<i+1 by omega)]
    · simp only [ite_eq_right h,ite_eq_left (show count<i+1 by omega)]
  · exact ((Local.write s .r12 _).trans (Local.write _ .r12 _)).weaken (by simp) (by simp)

theorem offset_free : ∀ i : Fin 8, dataOffset i≠.r12 := by decide

theorem partialLoad_ok (i : Fin 8) (count : Nat) (hc : count<8) (s : State)
    (hr : s.gpr .r19=BitVec.ofNat 64 count)
    (hoff : s.gpr (dataOffset i)=BitVec.ofNat 64 (16*i.val))
    (hread : InRegions (s.rd++s.wr)
      ((if i.val<count then s.gpr .r17 else s.gpr .r6)+BitVec.ofNat 64 (16*i.val)) 16) :
    WP isa (Impl.AesGcm.PPC64LE.SplitBlocks.partialLoad i) s fun t =>
      t.vpr (dataReg i)=readValue s count i ∧ Local [.r12] [dataReg i] s t := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.partialLoad]
  apply WP.seq
  refine WP.mono (selector_ok i count i.isLt hc s hr) fun u ⟨hu,hf⟩ => ?_
  have finish (p : Reg) (hp : p≠.r0) (hp12 : p≠.r12)
      (haddr : (if i.val<count then s.gpr .r17 else s.gpr .r6)=s.gpr p) :
      WP isa (.block [.lxvd2x (dataReg i) p (dataOffset i)]) u fun t =>
        t.vpr (dataReg i)=readValue s count i ∧ Local [.r12] [dataReg i] s t := by
    have hru : InRegions (u.rd++u.wr) (u.gpr p+u.gpr (dataOffset i)) 16 := by
      rw [hf.keep.2.1,hf.keep.2.2,hf.keep.gpr (by simpa using hp12),
        hf.keep.gpr (by simpa using offset_free i),hoff]
      simpa only [haddr] using hread
    refine WP.mono (Blocks.rawLoad_ok _ p _ u hp hru) fun t ⟨ht,hg⟩ => ⟨?_,?_⟩
    · rw [ht,hf.mem,hf.keep.gpr (by simpa using hp12),
        hf.keep.gpr (by simpa using offset_free i),hoff,readValue,haddr]
    · exact (hf.trans (Local.of_vector hg)).weaken (by simp) (by simp)
  have heval : eval (.zero .d .r12) u=some (decide (i.val<count)) := by
    simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hu]
    by_cases h : i.val<count <;> simp [h]
  refine WP.ite (decide (i.val<count)) heval (fun h => ?_) (fun h => ?_)
  · exact finish .r17 (by decide) (by decide) (by simp only [ite_eq_left (of_decide_eq_true h)])
  · exact finish .r6 (by decide) (by decide) (by simp only [ite_eq_right (of_decide_eq_false h)])

theorem readValue_of_local {base s : State} {vs : List VReg}
    (hs : Local [.r12] vs base s) (count i : Nat) : readValue s count i=readValue base count i := by
  rw [readValue,hs.mem,hs.keep.gpr (r := .r17) (by decide),hs.keep.gpr (r := .r6) (by decide)]
  rfl

structure PartialInv (base : State) (sourceN k : Nat) (s : State) : Prop where
  effects : Local [.r12] dataRegs base s
  values : ∀ i<k, s.vpr (dataReg i)=readValue base sourceN i

theorem partial_step (base : State) (sourceN : Nat) (hp : sourceN<8)
    (hr : base.gpr .r19=BitVec.ofNat 64 sourceN) (offsets : Blocks.DataOffsets base)
    (reads : ∀ i<8, InRegions (base.rd++base.wr)
      ((if i<sourceN then base.gpr .r17 else base.gpr .r6)+BitVec.ofNat 64 (16*i)) 16)
    {k : Nat} (hk : k<8) {s : State} (hs : PartialInv base sourceN k s) :
    WP isa (Impl.AesGcm.PPC64LE.SplitBlocks.partialLoad k) s (PartialInv base sourceN (k+1)) := by
  have hr' : s.gpr .r19=BitVec.ofNat 64 sourceN := (hs.effects.keep.gpr (by decide)).trans hr
  have off : s.gpr (dataOffset k)=BitVec.ofNat 64 (16*k) := by
    rw [hs.effects.keep.gpr (by simpa only [List.mem_singleton] using offset_free ⟨k,hk⟩)]
    exact offsets k hk
  have read : InRegions (s.rd++s.wr)
      ((if k<sourceN then s.gpr .r17 else s.gpr .r6)+BitVec.ofNat 64 (16*k)) 16 := by
    rw [hs.effects.keep.2.1,hs.effects.keep.2.2,hs.effects.keep.gpr (r := .r17) (by decide),
      hs.effects.keep.gpr (r := .r6) (by decide)]
    exact reads k hk
  refine WP.mono (partialLoad_ok ⟨k,hk⟩ sourceN hp s hr' off read) fun t ⟨hv,hf⟩ => ?_
  refine ⟨(hs.effects.trans hf).weaken (by simp) ?_,?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · rw [List.mem_singleton] at hr
      subst r
      have mems : ∀ i : Fin 8, dataReg i ∈ dataRegs := by decide
      exact mems ⟨k,hk⟩
  · intro i hi
    by_cases he : i=k
    · subst i
      exact hv.trans (readValue_of_local hs.effects sourceN k)
    · have hne : dataReg i≠dataReg k := fun e => he (Blocks.data_injective ⟨i,by omega⟩ ⟨k,hk⟩ e)
      rw [hf.v _ (by simpa only [List.mem_singleton] using hne)]
      exact hs.values i (by omega)

theorem partialLoadsFrom_ok (base : State) (sourceN : Nat) (hp : sourceN<8)
    (hr : base.gpr .r19=BitVec.ofNat 64 sourceN) (offsets : Blocks.DataOffsets base)
    (reads : ∀ i<8, InRegions (base.rd++base.wr)
      ((if i<sourceN then base.gpr .r17 else base.gpr .r6)+BitVec.ofNat 64 (16*i)) 16)
    (start count : Nat) (hb : start+count≤8) (s : State) (hs : PartialInv base sourceN start s) :
    WP isa (Impl.AesGcm.PPC64LE.SplitBlocks.partialLoadsFrom start count) s
      (PartialInv base sourceN (start+count)) := by
  induction count generalizing start s with
  | zero => exact WP.block_nil (by simpa only [Nat.add_zero] using hs)
  | succ count ih =>
    rw [Impl.AesGcm.PPC64LE.SplitBlocks.partialLoadsFrom]
    apply WP.seq
    refine WP.mono (partial_step base sourceN hp hr offsets reads (by omega) hs) fun t ht => ?_
    have he : start+(count+1)=start+1+count := by omega
    rw [he]
    exact ih (start+1) (by omega) t ht

structure ReadResult (base : State) (count : Nat) (s : State) : Prop where
  effects : Local [.r12,.r17,.r19] dataRegs base s
  values : ∀ i<8, s.vpr (dataReg i)=readValue base count i
  source : s.gpr .r17=base.gpr .r17+BitVec.ofNat 64 (16*min 8 count)
  left : s.gpr .r19=BitVec.ofNat 64 (count-8)

theorem fullAdvance_ok (s : State) :
    WP isa (.block ([.addi .r17 .r17 128,.subi .r19 .r19 8] : List Instr)) s
      (· = (s.write .r17 (s.gpr .r17+128)).write .r19 (s.gpr .r19-8)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,
    exec_addi (n := .r17) (imm := 128) (by decide) (by decide),
    exec_subi (n := .r19) (imm := 8) (by decide) (by decide),RegUpd.gpr_write,
    reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl

theorem partialAdvance_ok (s : State) :
    WP isa (.block ([.lsl .r12 .r19 4,.add .r17 .r17 .r12,.li .r19 0] : List Instr)) s
      (· = ((s.write .r12 (s.gpr .r19 <<< 4)).write .r17
        (s.gpr .r17+(s.gpr .r19 <<< 4))).write .r19 0) := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec_lsl (sh := 4) (by decide),
    exec_add,exec_li (imm := 0) (by decide),RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
    Option.some.injEq,exists_eq_left']
  rfl

theorem load_ok (base : State) (count : Nat) (hn : count<2^64)
    (hr : base.gpr .r19=BitVec.ofNat 64 count) (offsets : Blocks.DataOffsets base)
    (reads : ∀ i<8, InRegions (base.rd++base.wr)
      ((if i<count then base.gpr .r17 else base.gpr .r6)+BitVec.ofNat 64 (16*i)) 16) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.load base (ReadResult base count) := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.load]
  by_cases hz : count=0
  · subst count
    refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hr]; rfl)
      (fun _ => ?_) (by simp)
    refine WP.mono (Blocks.dataLoad_ok base offsets (by simpa using reads)) fun t ht => ?_
    refine ⟨(Local.of_vector ht.effects).weaken (by simp) (by simp),?_,?_,?_⟩
    · intro i hi
      simpa only [readValue,Nat.not_lt_zero,ite_false] using ht.val i hi
    · simp only [ht.effects.gpr,Nat.min_zero,Nat.mul_zero,BitVec.add_zero]
    · simpa only [ht.effects.gpr,Nat.zero_sub] using hr
  · have hne : base.gpr .r19≠0 := by
      rw [hr]; intro e
      have he := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn] at he
      exact hz he
    refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hne) (by simp) (fun _ => ?_)
    apply WP.seq
    have hquot : WP isa (.block ([.lsr .d .r12 .r19 3] : List Instr)) base
        (· = base.write .r12 (base.gpr .r19 >>> 3)) := by
      apply WP.of_runBlock
      simp only [runBlock_cons,runStep_some,runBlock_nil,exec_lsr_d (sh := 3) (by decide),
        Option.some.injEq,exists_eq_left']
    refine WP.mono hquot fun u hu => ?_
    subst u
    let u := base.write .r12 (base.gpr .r19 >>> 3)
    have hf : Local [.r12] [] base u := Local.write base .r12 _
    have hr' : u.gpr .r19=BitVec.ofNat 64 count := (hf.keep.gpr (by decide)).trans hr
    have offs : Blocks.DataOffsets u := by
      intro i hi
      rw [hf.keep.gpr (by simpa only [List.mem_singleton] using offset_free ⟨i,hi⟩)]
      exact offsets i hi
    have readu : ∀ i<8, InRegions (u.rd++u.wr)
        ((if i<count then u.gpr .r17 else u.gpr .r6)+BitVec.ofNat 64 (16*i)) 16 := by
      intro i hi
      rw [hf.keep.2.1,hf.keep.2.2,hf.keep.gpr (r := .r17) (by decide),hf.keep.gpr (r := .r6) (by decide)]
      exact reads i hi
    have h12 : (base.write .r12 (base.gpr .r19 >>> 3)).gpr .r12=BitVec.ofNat 64 count >>> 3 := by
      rw [RegUpd.gpr_write_self,hr]
    by_cases hbig : 8≤count
    · have hshift : BitVec.ofNat 64 count >>> 3≠0 :=
        fun e => Nat.not_lt_of_ge hbig ((VG.Proof.Aes.PPC64LE.Crypto.quotient_zero hn).mp e)
      refine WP.ite true (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
        h12,Option.some.injEq,bne_iff_ne] using hshift) (fun _ => ?_) (by simp)
      rw [WP.block_append_iff]
      refine WP.mono (Blocks.dataLoadAt_ok .r17 (by decide) u offs (by
        intro i hi; simpa only [ite_eq_left (show i<count by omega)] using readu i hi)) fun s hs => ?_
      refine WP.mono (fullAdvance_ok s) fun t ht => ?_
      subst t
      have he := ((hf.trans (Local.of_vector hs.effects)).trans
        (Local.write s .r17 (s.gpr .r17+128))).trans (Local.write _ .r19 (s.gpr .r19-8))
      refine ⟨he.weaken (by simp [or_comm]) (by simp),?_,?_,?_⟩
      · intro i hi
        simp only [vpr_write]
        rw [hs.val i hi,readValue,ite_eq_left (show i<count by omega),hf.mem,hf.keep.gpr (by decide)]
      · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,hs.effects.gpr,
          hf.keep.gpr (r := .r17) (by decide),Nat.min_eq_left hbig]
        rfl
      · simp only [RegUpd.gpr_write_self,hs.effects.gpr,hr']
        exact Offset.ofNat_sub_ofNat hbig
    · have hsmall : count<8 := by omega
      have hshift := (VG.Proof.Aes.PPC64LE.Crypto.quotient_zero hn).mpr hsmall
      refine WP.ite false (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,h12,hshift]; rfl)
        (by simp) (fun _ => ?_)
      apply WP.seq
      refine WP.mono (partialLoadsFrom_ok u count hsmall hr' offs readu 0 8 (by decide) u
        ⟨Local.refl _ _ _,fun _ hi => by omega⟩) fun s hs => ?_
      refine WP.mono (partialAdvance_ok s) fun t ht => ?_
      subst t
      have hs19 : s.gpr .r19=BitVec.ofNat 64 count := (hs.effects.keep.gpr (by decide)).trans hr'
      have he := (((hf.trans hs.effects).trans (Local.write s .r12 (s.gpr .r19 <<< 4))).trans
        (Local.write _ .r17 (s.gpr .r17+(s.gpr .r19 <<< 4)))).trans (Local.write _ .r19 0)
      refine ⟨he.weaken (by simp [or_comm]) (by simp),?_,?_,?_⟩
      · intro i hi
        simp only [vpr_write]
        exact (hs.values i hi).trans (readValue_of_local hf count i)
      · simp only [RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,
          hs.effects.keep.gpr (r := .r17) (by decide),hf.keep.gpr (r := .r17) (by decide),
          hs19,Nat.min_eq_right (Nat.le_of_lt hsmall)]
        have sh : ∀ n : Fin 8, BitVec.ofNat 64 n.val <<< 4=BitVec.ofNat 64 (16*n.val) := by decide
        rw [sh ⟨count,hsmall⟩]
      · simp only [RegUpd.gpr_write_self,Nat.sub_eq_zero_of_le (Nat.le_of_lt hsmall)]
        rfl

def sourceRegion (base : State) (count : Nat) : Region := ⟨base.gpr .r17,16*count⟩

structure SourceLayout (base : State) (n count : Nat) : Prop where
  left : base.gpr .r19=BitVec.ofNat 64 count
  reads : InRegions (base.rd++base.wr) (base.gpr .r17) (16*count)
  size : 16*count≤2^64
  work : (sourceRegion base count).Disjoint (Blocks.coreWork base)
  data : (sourceRegion base count).Disjoint (Blocks.coreData base n)

def plaintext (base : State) (count i : Nat) : Spec.Gcm.Block :=
  if i<count then Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))
  else Blocks.defaultPlaintext base i

def input (base : State) (count k : Nat) (p left : BitVec 64) : Prop :=
  p=base.gpr .r17+BitVec.ofNat 64 (16*min k count) ∧ left=BitVec.ofNat 64 (count-k)

theorem source_addr {base start : State} {count k i : Nat}
    (hi : i<count-k) (hin : input base count k (start.gpr .r17) (start.gpr .r19)) :
    start.gpr .r17+BitVec.ofNat 64 (16*i)=base.gpr .r17+BitVec.ofNat 64 (16*(k+i)) := by
  rw [hin.1,Nat.min_eq_left (show k≤count by omega),Offset.add_add]
  exact congrArg (fun j => base.gpr .r17+BitVec.ofNat 64 j) (by omega)

theorem SourceLayout.read_block {base : State} {n count : Nat} (src : SourceLayout base n count)
    {i : Nat} (hi : i<count) :
    InRegions (base.rd++base.wr) (base.gpr .r17+BitVec.ofNat 64 (16*i)) 16 := by
  exact (Covers.one src.reads) _ _ ⟨_,List.mem_singleton_self _,
    Offset.contains_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega) (by have := src.size; omega)⟩

theorem SourceLayout.block_frame {base start : State} {n count : Nat} (src : SourceLayout base n count)
    (hf : Frame [Blocks.coreWork base,Blocks.coreData base n] base.mem start.mem)
    {i : Nat} (hi : i<count) :
    Spec.Gcm.blockAt start.mem (base.gpr .r17+BitVec.ofNat 64 (16*i))=
      Spec.Gcm.blockAt base.mem (base.gpr .r17+BitVec.ofNat 64 (16*i)) := by
  rw [← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,← VG.Proof.Aes.PPC64LE.Crypto.read_blockAt]
  rw [hf.read (r := sourceRegion base count)
    (Offset.contains_base _ (d := 16*i) (n := 16) (k := 16*count) (by omega) (by have := src.size; omega))
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl; exacts [src.work,src.data]) (by decide)]

theorem reader_global (base start : State) (n nr count k : Nat) (lay : Blocks.CoreLayout base n)
    (src : SourceLayout base n count) (hk : k+8≤n)
    (fx : Blocks.LoopFixed base nr start)
    (hf : Frame [Blocks.coreWork base,Blocks.coreData base n] base.mem start.mem)
    (ptr : start.gpr .r6=base.gpr .r6+BitVec.ofNat 64 (16*k))
    (hp : VG.Proof.Aes.Memory.Processed base.mem start.mem (base.gpr .r6) n k
      (Blocks.cipherStateWith base nr (plaintext base count)))
    (hin : input base count k (start.gpr .r17) (start.gpr .r19)) :
    (∀ i<8, InRegions (start.rd++start.wr)
      ((if i<count-k then start.gpr .r17 else start.gpr .r6)+BitVec.ofNat 64 (16*i)) 16) ∧
    (∀ i<8, VG.Proof.Aes.PPC64LE.Crypto.flip (readValue start (count-k) i)=plaintext base count (k+i)) := by
  refine ⟨?_,?_⟩
  · intro i hi
    rw [fx.rd,fx.wr]
    by_cases hsrc : i<count-k
    · rw [ite_eq_left hsrc,source_addr hsrc hin]
      exact src.read_block (by omega)
    · rw [ite_eq_right hsrc,ptr,Offset.add_add,show 16*k+16*i=16*(k+i) by omega]
      obtain ⟨r,hr,hp⟩ := lay.writes _ _ ⟨Blocks.coreData base n,by simp,
        Offset.contains_base _ (d := 16*(k+i)) (n := 16) (k := 16*n) (by omega) (by have := lay.size; omega)⟩
      exact ⟨r,List.mem_append_right _ hr,hp⟩
  · intro i hi
    rw [readValue,VG.Proof.Aes.PPC64LE.Crypto.flip_load,VG.Proof.Aes.PPC64LE.Crypto.read_blockAt,plaintext]
    by_cases hsrc : i<count-k
    · rw [ite_eq_left hsrc,ite_eq_left (show k+i<count by omega),source_addr hsrc hin]
      exact src.block_frame hf (by omega)
    · rw [ite_eq_right hsrc,ite_eq_right (show ¬k+i<count by omega),ptr,Offset.add_add,
        show 16*k+16*i=16*(k+i) by omega]
      exact Blocks.processed_original_block hp (by omega) (by omega)

theorem input_advance {base start s : State} {count k : Nat}
    (hin : input base count k (start.gpr .r17) (start.gpr .r19))
    (hr : ReadResult start (count-k) s) : input base count (k+8) (s.gpr .r17) (s.gpr .r19) := by
  refine ⟨?_,?_⟩
  · rw [hr.source,hin.1,Offset.add_add]
    exact congrArg (fun j => base.gpr .r17+BitVec.ofNat 64 j) (by omega)
  · rw [hr.left,Nat.sub_sub]

theorem stores_correct (base : State) (n nr count : Nat) (lay : Blocks.CoreLayout base n)
    (src : SourceLayout base n count) (hmax : nr<15) :
    Blocks.StoreCorrect base n nr (plaintext base count) (input base count)
      (.seq Impl.AesGcm.PPC64LE.SplitBlocks.load (.block Impl.AesGcm.PPC64LE.Blocks.storesFinish)) := by
  intro k start hk fx frame ptr offsets proc vals hin
  have global := reader_global base start n nr count k lay src hk fx frame ptr proc hin
  apply WP.seq
  refine WP.mono (load_ok start (count-k) (by have := src.size; omega) hin.2 offsets global.1)
    fun s hs => ?_
  have hmask := (hs.effects.v .v19 (by decide)).trans fx.mask
  have fxs : Blocks.LoopFixed base nr s := fx.update
    (hs.effects.keep.mono (by simp [Blocks.loopGprs])) (hs.effects.v .v19 (by decide))
    (hs.effects.v .v13 (by decide)) (by simpa only [hs.effects.mem] using fx.tables)
  have offs : Blocks.DataOffsets s := by
    intro i hi
    have free : ∀ i : Fin 8, dataOffset i ∉ [.r12,.r17,.r19] := by decide
    rw [hs.effects.keep.gpr (free ⟨i,hi⟩)]; exact offsets i hi
  have ptrs : s.gpr .r6=base.gpr .r6+BitVec.ofNat 64 (16*k) :=
    (hs.effects.keep.gpr (by decide)).trans ptr
  have wrs : ∀ i<8, InRegions s.wr (base.gpr .r6+BitVec.ofNat 64 (16*(k+i))) 16 := by
    intro i hi
    rw [hs.effects.keep.2.2,fx.wr]
    exact lay.writes _ _ ⟨Blocks.coreData base n,by simp,
      Offset.contains_base _ (d := 16*(k+i)) (n := 16) (k := 16*n)
        (by omega) (by have := lay.size; omega)⟩
  have cv : ∀ i<8, Blocks.mixValue s i=Blocks.cipherBlockWith base nr (plaintext base count) (k+i) := by
    intro i hi
    rw [Blocks.mixValue,hs.values i hi,global.2 i hi]
    have free : ∀ i : Fin 8, Impl.AesGcm.PPC64LE.Blocks.reg i ∉ dataRegs := by decide
    have hc : Blocks.cipherAt s i=Blocks.cipherAt start i := hs.effects.v _ (free ⟨i,hi⟩)
    rw [hc,vals i hi,Blocks.cipherBlockWith]
    exact BitVec.xor_comm _ _
  have states : ∀ i<8, VG.Proof.Aes.PPC64LE.Crypto.aesState (Blocks.mixValue s i)=
      Blocks.cipherStateWith base nr (plaintext base count) (k+i) := by
    intro i hi; rw [cv i hi]; rfl
  have procs : VG.Proof.Aes.Memory.Processed base.mem s.mem (base.gpr .r6) n k
      (Blocks.cipherStateWith base nr (plaintext base count)) := by
    rw [hs.effects.mem]; exact proc
  refine WP.mono (Blocks.storesFinish_ok s base.mem (base.gpr .r6) n k _ hk lay.size
    hmask ptrs offs wrs states procs) fun t ht => ?_
  have dis : (⟨base.gpr .r10+128,512⟩ : Region).Disjoint (Blocks.coreData base n) :=
    (lay.scratch (Blocks.coreData base n) (by simp)).symm.sub_left
      (Offset.sub_base _ (d := 128) (n := 512) (k := 2048) (by decide))
  refine ⟨?_,?_,?_,ht.processed,?_,?_,?_,?_,?_⟩
  · exact fxs.update (ht.keep.mono (by simp [Blocks.loopGprs]))
      (ht.v .v19 (by decide)) (ht.v .v13 (by decide))
      (fxs.tables.frame hmax ht.frame (by simpa only [List.mem_singleton,forall_eq,Blocks.coreData] using dis))
  · exact (hs.effects.keep.trans ht.keep).mono (by simp [Blocks.storeGprs])
  · simpa only [hs.effects.mem,Blocks.coreData] using ht.frame
  · intro i hi; exact (ht.values i hi).trans (cv i hi)
  · rw [ht.ptr,hs.effects.keep.gpr (by decide)]
  · rw [ht.left,hs.effects.keep.gpr (by decide)]
  · exact (ht.v .v10 (by decide)).trans (hs.effects.v .v10 (by decide))
  · rw [ht.keep.gpr (r := .r17) (by decide),ht.keep.gpr (r := .r19) (by decide)]
    exact input_advance hin hs

theorem input_initial {base : State} {n count : Nat} (src : SourceLayout base n count) :
    input base count 0 (base.gpr .r17) (base.gpr .r19) := by
  refine ⟨?_,?_⟩
  · simp only [Nat.zero_min,Nat.mul_zero,BitVec.add_zero]
  · simpa only [Nat.sub_zero] using src.left

def coreVolatile : List Reg := Blocks.coreVolatile++[.r17,.r19]

theorem core_ok [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (base : State) (n nr count : Nat) (lay : Blocks.CoreLayout base n) (src : SourceLayout base n count)
    (hn : base.gpr .r7=BitVec.ofNat 64 n) (hm : n%8=0) (hmin : 9<nr) (hmax : nr<15)
    (hr : base.gpr .r4=BitVec.ofNat 64 nr) (hH : base.gpr .r8=base.gpr .r3+240#64) :
    WP isa Impl.AesGcm.PPC64LE.SplitBlocks.code base fun t =>
      Blocks.CoreResultWith base n nr (plaintext base count) (input base count) t ∧ Keep coreVolatile base t := by
  have hfunc : WP isa Impl.AesGcm.PPC64LE.SplitBlocks.code base
      (Blocks.CoreResultWith base n nr (plaintext base count) (input base count)) := by
    by_cases hz : n=0
    · subst n
      rw [Impl.AesGcm.PPC64LE.SplitBlocks.code,Impl.AesGcm.PPC64LE.Blocks.codeWith]
      refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hn]; rfl)
        (fun _ => WP.block_nil ?_) (by simp)
      refine ⟨Frame.refl _ _,?_,rfl,?_,fun _ _ => rfl,input_initial src,Frame.refl _ _⟩
      · simp only [Spec.Gcm.blocksAt,List.range_zero,List.map_nil,Spec.Gcm.ctr32,Spec.Gcm.keystream,
          List.length_nil,List.zipWith_nil_left]
      · rfl
    · exact Blocks.core_nonemptyWith_ok base n nr (plaintext base count) (input base count)
        Impl.AesGcm.PPC64LE.SplitBlocks.batch (fun hk hs =>
          Blocks.batchWithStore_ok lay _ (stores_correct base n nr count lay src hmax) hmin hmax hk hs)
        (input_initial src) lay hn (by omega) hm hmax hr hH
  refine WP.mono (WP.keep (coreVolatile++Impl.AesGcm.PPC64LE.Blocks.saved.map Prod.fst) hfunc
    (by lit_decide) (by lit_decide)) fun t ⟨ht,hk⟩ => ⟨ht,?_,hk.2⟩
  intro r hr
  by_cases hs : r ∈ Impl.AesGcm.PPC64LE.Blocks.saved.map Prod.fst
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hs
    exact ht.restored p hp
  · exact hk.gpr (by simpa only [List.mem_append,not_or] using And.intro hr hs)

theorem load_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r0,.r6,.r11,.r17,.r18,.r19,.r20,.r21,.r22,.r23,.r24])
    Impl.AesGcm.PPC64LE.SplitBlocks.load h).isSome=true := ⟨_,by taint_decide⟩

theorem code_taint : ∃ h, (VG.Taint.check vectorTaint
    (Taint.ofRegs [.r3,.r4,.r5,.r6,.r7,.r8,.r9,.r10,.r17,.r19])
    Impl.AesGcm.PPC64LE.SplitBlocks.code h).isSome=true := ⟨_,by taint_decide⟩

end VG.Proof.AesGcm.PPC64LE.SplitBlocks
