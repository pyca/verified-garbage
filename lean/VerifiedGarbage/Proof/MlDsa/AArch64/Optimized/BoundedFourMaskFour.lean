module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourTable
public import VerifiedGarbage.Impl.Tbl.AArch64
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourRead
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Semantics
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlDsa.AArch64.Optimized.BoundedFourInitialized`, which the modules that import this one used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourReady`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourInitMemory`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.BoundedFourInitCode`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def initLo (mask : Nat) : BitVec 64 := BitVec.ofNat 64 (bytesWord ((shuffleBytes mask).take 8))
def initHi (mask : Nat) : BitVec 64 := BitVec.ofNat 64 (bytesWord ((shuffleBytes mask).drop 8))

def initEntry (mask : Nat) : List Instr :=
 VG.Impl.Tbl.AArch64.const64 .x6 (initLo mask) ++
 ([.str .x .x6 .x19 (6000+64*mask)] : List Instr) ++
 VG.Impl.Tbl.AArch64.const64 .x6 (initHi mask) ++
 [.str .x .x6 .x19 (6000+64*mask+8),
  .movz .x .x6 (BitVec.ofNat 16 (acceptedIndices mask).length) 0,
  .str .x .x6 .x19 (6000+64*mask+32)]

theorem entryInit_eq {mask : Nat} (hm : mask<16) : entryInit true mask=initEntry mask := by
  have h : ∀m : Fin 16,entryInit true m.val=initEntry m.val := by decide
  exact h ⟨mask,hm⟩

theorem init_words {mask : Nat} (hm : mask<16) :
    ofVDwords (initLo mask) (initHi mask)=shuffleWord mask := by
  have h : ∀m : Fin 16,ofVDwords (initLo m.val) (initHi m.val)=shuffleWord m.val := by decide
  exact h ⟨mask,hm⟩

theorem init_count {mask : Nat} (hm : mask<16) :
    (BitVec.ofNat 16 (acceptedIndices mask).length).setWidth 64=
      BitVec.ofNat 64 (acceptedIndices mask).length := by
  have h : ∀m : Fin 16,(BitVec.ofNat 16 (acceptedIndices m.val).length).setWidth 64=
      BitVec.ofNat 64 (acceptedIndices m.val).length := by decide
  exact h ⟨mask,hm⟩
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end


/-! ## From `BoundedFourInitStore.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def storeConstant (v : BitVec 64) (off : Nat) : List Instr :=
 VG.Impl.Tbl.AArch64.const64 .x6 v ++ [.str .x .x6 .x19 off]

/-- A table word is emitted through x6 and preserves every SIMD register. -/
theorem storeConstant_ok {v : BitVec 64} {off : Nat}
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%8=0 ∧ off<32768)
    (hw : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 off) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      t.mem=s.mem.writeW (s.gpr .x19+BitVec.ofNat 64 off) v → WP isa (.block rest) t Q) :
    WP isa (.block (storeConstant v off++rest)) s Q := by
  unfold storeConstant
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x6 v) fun a ⟨hav,hag,has⟩ => ?_
  have ha : Only [.x6] s a := by
    refine ⟨fun r hr => hag r (by simpa using hr),?_,?_,?_,?_,?_⟩
    all_goals rw [has]
    all_goals first | rfl | exact fun _ _ => rfl
  have hs : WP isa (.block [.str .x .x6 .x19 off]) a fun t =>
      MemTo a t (a.mem.writeW (a.gpr .x19+BitVec.ofNat 64 off) (a.gpr .x6)) :=
    wp_strx ho rfl (by rw [ha.wr,ha.get .x19]; exact hw) fun _ ht => wp_nil ht
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by rfl) hs) fun t ⟨ht,hvec⟩ =>
    k t ((ha.keep.trans ht.keep).mono (by simp)) ?_ ?_
  · have hvec' : a.v=s.v := by rw [has]
    exact hvec.trans hvec' 
  · rw [ht.mem,ha.mem,ha.get .x19,hav]
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitEntry.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def storeCount (mask : Nat) : List Instr :=
 [.movz .x .x6 (BitVec.ofNat 16 (acceptedIndices mask).length) 0,
  .str .x .x6 .x19 (6000+64*mask+32)]

theorem storeCount_ok {mask : Nat} (hm : mask<16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+32)) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      t.mem=s.mem.writeW (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+32))
        (BitVec.ofNat 64 (acceptedIndices mask).length) → WP isa (.block rest) t Q) :
    WP isa (.block (storeCount mask++rest)) s Q := by
  have hs : WP isa (.block (storeCount mask)) s fun t => Keep [.x6] s t ∧
      t.mem=s.mem.writeW (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+32))
        (BitVec.ofNat 64 (acceptedIndices mask).length) := by
    refine wp_movz fun u hu hval => wp_strx (by omega_using [hm]) rfl
      (by rw [hu.wr,hu.get .x19]; exact hw) fun t ht => wp_nil ⟨(hu.keep.trans ht.keep).mono (by simp),?_⟩
    rw [ht.mem,hu.mem,hu.get .x19,hval,init_count hm]
  rw [WP.block_append_iff]
  exact WP.mono (WP.keepV (by rfl) hs) fun t ⟨⟨hk,hmem⟩,hv⟩ => k t hk hv hmem

def initEntryMemory (m : Mem) (scratch : Addr) (mask : Nat) : Mem :=
 ((m.writeW (scratch+BitVec.ofNat 64 (6000+64*mask)) (initLo mask)).writeW
   (scratch+BitVec.ofNat 64 (6000+64*mask+8)) (initHi mask)).writeW
   (scratch+BitVec.ofNat 64 (6000+64*mask+32)) (BitVec.ofNat 64 (acceptedIndices mask).length)

theorem entryInit_ok {mask : Nat} (hm : mask<16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀off∈[0,8,32],InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+off)) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v → t.mem=initEntryMemory s.mem (s.gpr .x19) mask →
      WP isa (.block rest) t Q) :
    WP isa (.block (entryInit true mask++rest)) s Q := by
  rw [entryInit_eq hm]
  have he : initEntry mask=storeConstant (initLo mask) (6000+64*mask) ++
      storeConstant (initHi mask) (6000+64*mask+8) ++ storeCount mask := by
    simp only [initEntry,storeConstant,storeCount,List.append_assoc,List.cons_append,List.nil_append]
  rw [he]
  simp only [List.append_assoc]
  refine storeConstant_ok (by omega_using [hm]) (by simpa using hw 0 (by simp)) fun a ha hav ham => ?_
  refine storeConstant_ok (by omega_using [hm])
    (by rw [ha.wr,ha.get .x19]; exact hw 8 (by simp)) fun b hb hbv hbm => ?_
  have hk : Keep [.x6] s b := (ha.trans hb).mono (by simp)
  refine storeCount_ok hm (by rw [hk.wr,hk.get .x19]; exact hw 32 (by simp)) fun t ht htv htm =>
    k t ((hk.trans ht).mono (by simp)) (htv.trans (hbv.trans hav)) ?_
  rw [htm,hbm,ham,hk.get .x19,ha.get .x19]
  rfl
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

theorem initEntryMemory_eq (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    initEntryMemory m p mask=
      (m.write (p+BitVec.ofNat 64 (6000+64*mask)) 16 (shuffleWord mask)).writeW
        (p+BitVec.ofNat 64 (6000+64*mask+32)) (BitVec.ofNat 64 (acceptedIndices mask).length) := by
  rw [←init_words hm,write16_dwords]
  simp only [initEntryMemory,BitVec.add_assoc,←BitVec.ofNat_add]

theorem initEntryMemory_frame (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    Frame [⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩] m (initEntryMemory m p mask) := by
  rw [initEntryMemory_eq m p hm]
  have h16 : (⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ : Region).Contains
      (p+BitVec.ofNat 64 (6000+64*mask)) 16 := Offset.contains p (by omega_using []) (by omega_using []) (by omega_using [hm])
  have h32 : (⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ : Region).Contains
      (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 := Offset.contains p (by omega_using []) (by omega_using []) (by omega_using [hm])
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem initEntryMemory_read (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    (initEntryMemory m p mask).read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
    (initEntryMemory m p mask).readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=
      BitVec.ofNat 64 (acceptedIndices mask).length := by
  rw [initEntryMemory_eq m p hm]
  constructor
  · rw [Mem.writeW,Mem.read_write_sep (Offset.sep p (by omega_using []) (by omega_using [hm]) (by omega_using [hm])) (by decide)]
    have hs := Mem.readW_writeW_self m (p+BitVec.ofNat 64 (6000+64*mask)) 16 (shuffleWord mask) (by decide)
    simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using hs
  · exact Mem.readW_writeW_self64 _ _ _

theorem initEntryMemory_other (m : Mem) (p : Addr) {mask other : Nat}
    (hm : mask<16) (ho : other<16) (hne : other≠mask) :
    (initEntryMemory m p mask).read (p+BitVec.ofNat 64 (6000+64*other)) 16=
      m.read (p+BitVec.ofNat 64 (6000+64*other)) 16 ∧
    (initEntryMemory m p mask).readW (p+BitVec.ofNat 64 (6000+64*other+32)) 64=
      m.readW (p+BitVec.ofNat 64 (6000+64*other+32)) 64 := by
  have hf := initEntryMemory_frame m p hm
  have hd : (⟨p+BitVec.ofNat 64 (6000+64*other),64⟩ : Region).Disjoint
      ⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ := Offset.disjoint p (by omega_using [hne]) (by omega_using [ho]) (by omega_using [hm])
  constructor
  · exact hf.read (Offset.contains p (e := 6000+64*other) (k := 64) (by omega_using []) (by omega_using []) (by omega_using [ho]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
  · exact hf.readW (Offset.contains p (e := 6000+64*other) (k := 64) (by omega_using []) (by omega_using []) (by omega_using [ho]))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

/-! ## From `BoundedFourCounts.lean` -/

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/BoundedFourSamplerState.lean`, which only this module imported.
section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

abbrev samplerSeed := ResidentRej.seedP
abbrev samplerOut := ResidentRej.aP
abbrev samplerScratch := ResidentRej.scr
abbrev samplerAt := ResidentRej.at'
abbrev SamplerEnv := ResidentRej.Env 4

def samplerSeeds (s : State) : Region := ⟨samplerSeed s,264⟩
def samplerOutput (s : State) : Region := ⟨samplerOut s,4096⟩
def samplerWorkspace (s : State) : Region := ⟨samplerScratch s,8192⟩
def samplerSeedAt (s : State) (i : Nat) : Addr := samplerSeed s+BitVec.ofNat 64 (66*i)
def samplerA (s : State) (i : Nat) : Spec.Sha3.State := ResidentMask.seedState s.mem (samplerSeedAt s i)

structure SamplerPre (s : State) : Prop where
 rd : s.rd=[samplerSeeds s]
 wr : s.wr=[samplerOutput s,samplerWorkspace s]
 seed_output : (samplerSeeds s).Disjoint (samplerOutput s)
 seed_work : (samplerSeeds s).Disjoint (samplerWorkspace s)
 output_work : (samplerOutput s).Disjoint (samplerWorkspace s)

theorem sampler_in_work {σ s : State} (hp : SamplerPre σ) (hw : s.wr=σ.wr)
    {d n : Nat} (hd : d+n≤8192) : InRegions s.wr (samplerAt σ d) n := by
  rw [hw,hp.wr]
  exact ⟨samplerWorkspace σ,by simp,Offset.contains_base (samplerScratch σ) hd (by omega_using [hd])⟩

theorem sampler_in_seed {σ s : State} (hp : SamplerPre σ) (hr : s.rd=σ.rd)
    {d n : Nat} (hd : d+n≤264) : InRegions (s.rd++s.wr) (samplerSeed σ+BitVec.ofNat 64 d) n := by
  rw [hr,hp.rd]
  exact ⟨samplerSeeds σ,by simp,Offset.contains_base (samplerSeed σ) hd (by omega_using [hd])⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
end

end

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem initCounts_ok {s : State} {b : Addr} (hb : s.gpr .x19=b)
    (hw : ∀i<4,InRegions s.wr (countAt b i) 8) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      (Keep [.x4] s t ∧
      Frame [⟨b+7904#64,32⟩] s.mem t.mem ∧
      ∀i<4,t.mem.readW (countAt b i) 64=256) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts
  refine wp_movz fun a ha h4=>?_
  refine WP.mono (ResidentRej.countsStore_ok 4 (by decide) (s := a) (p := b)
    (by rw [ha.get .x19]; exact hb) h4 (fun i hi=>by rw [ha.wr]; exact hw i hi))
    fun t ⟨ht,hf,hc⟩=>?_
  refine ⟨?_,?_,hc⟩
  · exact ⟨fun r hr=>by rw [ht.gpr]; exact ha.gpr r hr,
      ht.rd.trans ha.rd,ht.wr.trans ha.wr,ht.sp.trans ha.sp,
      fun r hr=>by rw [ht.vec]; exact ha.vcs r hr⟩
  · rw [ha.mem] at hf
    exact hf

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitTable.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def tableMemory (m : Mem) (p : Addr) : Nat → Mem
 | 0 => m
 | n+1 => initEntryMemory (tableMemory m p n) p n

def TablePrefix (m : Mem) (p : Addr) (n : Nat) : Prop := ∀mask<n,
 m.read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
 m.readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=BitVec.ofNat 64 (acceptedIndices mask).length

theorem tableMemory_prefix (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    TablePrefix (tableMemory m p n) p n := by
  induction n with
  | zero => intro mask hm; omega_arith
  | succ n ih =>
    have hprev := ih (by omega_arith)
    intro mask hm
    by_cases he : mask=n
    · subst mask; exact initEntryMemory_read _ p (by omega_arith)
    · have hother := initEntryMemory_other (tableMemory m p n) p (by omega_arith : n<16) (by omega_arith : mask<16) he
      have hp := hprev mask (by omega_arith)
      exact ⟨hother.1.trans hp.1,hother.2.trans hp.2⟩

theorem TablePrefix.table {m : Mem} {p : Addr} (h : TablePrefix m p 16) : TableAt m (p+6000) := by
  intro mask hm
  have e0 : (p+6000)+BitVec.ofNat 64 (64*mask)=p+BitVec.ofNat 64 (6000+64*mask) := by
    change (p+BitVec.ofNat 64 6000)+BitVec.ofNat 64 (64*mask)=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have e1 : (p+BitVec.ofNat 64 (6000+64*mask))+32=p+BitVec.ofNat 64 (6000+64*mask+32) := by
    change (p+BitVec.ofNat 64 (6000+64*mask))+BitVec.ofNat 64 32=_
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [e0,e1]
  exact h mask hm

theorem tableMemory_table (m : Mem) (p : Addr) : TableAt (tableMemory m p 16) (p+6000) :=
  (tableMemory_prefix m p (by decide : 16≤16)).table

def tablePrefixCode (n : Nat) : List Instr := (List.range n).flatMap (entryInit true)

theorem tablePrefixCode_ok {n : Nat} (hn : n≤16)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀mask<n,∀off∈[0,8,32],InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (6000+64*mask+off)) 8)
    (k : ∀t,Keep [.x6] s t → t.v=s.v → t.mem=tableMemory s.mem (s.gpr .x19) n →
      WP isa (.block rest) t Q) :
    WP isa (.block (tablePrefixCode n++rest)) s Q := by
  induction n generalizing s rest with
  | zero => exact k s (Keep.refl _ _) rfl rfl
  | succ n ih =>
    have he : tablePrefixCode (n+1)=tablePrefixCode n++entryInit true n := by
      simp only [tablePrefixCode,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [he,List.append_assoc]
    refine ih (by omega_arith) (by intro mask hm; exact hw mask (by omega_arith)) fun a ha hav ham => ?_
    refine entryInit_ok (by omega_arith) (by
      intro off hoff
      rw [ha.wr,ha.get .x19]
      exact hw n (by omega_arith) off hoff) fun t ht htv htm =>
        k t ((ha.trans ht).mono (by simp)) (htv.trans hav) ?_
    rw [htm,ham,ha.get .x19]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourPro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

theorem samplerPro_ok {σ : State} (hp : SamplerPre σ) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.pro) σ (SamplerEnv σ) :=
  ResidentRej.pro_with 4 (fun _ _ h=>sampler_in_work hp rfl h)

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourInitVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def initTableRegion (p : Addr) : Region := ⟨p+BitVec.ofNat 64 6000,1024⟩

theorem initEntryMemory_tableFrame (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    Frame [initTableRegion p] m (initEntryMemory m p mask) := by
  rw [initEntryMemory_eq m p hm]
  have h16 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask)) 16 :=
    Offset.contains p (by omega_arith) (by omega_arith) (by decide)
  have h32 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 :=
    Offset.contains p (by omega_arith) (by omega_arith) (by decide)
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem tableMemory_frame (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    Frame [initTableRegion p] m (tableMemory m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih => exact (ih (by omega_arith)).trans (initEntryMemory_tableFrame _ p (by omega_arith))

/-- The selected fast initializer builds all sixteen entries, changes only x6,
and confines writes to the 1024-byte table at scratch+6000. -/
theorem tableInit_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀a n,InRegions [initTableRegion (s.gpr .x19)] a n → InRegions s.wr a n)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      TableAt t.mem (s.gpr .x19+6000) →
      Frame [initTableRegion (s.gpr .x19)] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (tableInit true++rest)) s Q := by
  change WP isa (.block (tablePrefixCode 16++rest)) s Q
  refine tablePrefixCode_ok (by decide) (by
    intro mask hm off hoff
    apply hw
    refine ⟨initTableRegion (s.gpr .x19),by simp,?_⟩
    have ho : off=0 ∨ off=8 ∨ off=32 := by simpa using hoff
    exact Offset.contains _ (by omega_arith) (by omega_arith) (by decide)) fun t ht hv hm => k t ht hv ?_ ?_
  · rw [hm]
    exact tableMemory_table _ _
  · rw [hm]
    exact tableMemory_frame _ _ (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourAbsorb.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (absorbPair)
open ResidentRej (seedP scr at' scrR stateP)
open ResidentMask (absorbBody_ok seedState_eq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (zeros_ok pair_sub)

def absorbArgs (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66]

theorem absorbPair_eq (p : Nat) : absorbPair p=absorbArgs p++Impl.MlDsa.AArch64.Optimized.ResidentMask.absorbBody := rfl

theorem absorbArgs_ok {p : Nat} (hp : p<2) {s : State} :
    WP isa (.block (absorbArgs p)) s fun t=>Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2=s.gpr .x19+BitVec.ofNat 64 (400*p) ∧
      t.gpr .x3=s.gpr .x20+BitVec.ofNat 64 (132*p) ∧
      t.gpr .x4=s.gpr .x20+BitVec.ofNat 64 (132*p+66) := by
  unfold absorbArgs
  refine Proof.MlKem.AArch64.wp_addImm (by omega_arith) fun a ha h2=>
    Proof.MlKem.AArch64.wp_addImm (by omega_arith) fun b hb h3=>
    Proof.MlKem.AArch64.wp_addImm (by decide) fun t ht h4=>Proof.MlKem.AArch64.wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,hb.get .x2,h2]
  · rw [ht.get .x3,h3,ha.get .x20]
  · rw [h4,h3,ha.get .x20,BitVec.add_assoc,←BitVec.ofNat_add]

private theorem seed_sub {σ : State} {k : Nat} (hk : k<4) :
    Region.Sub (ResidentMask.seedR (seedP σ+BitVec.ofNat 64 (66*k)))
      (samplerSeeds σ) := Offset.sub_base (seedP σ) (by omega_arith)

private theorem seed_eq {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s)
    {k : Nat} (hk : k<4) :
    Spec.Sha3.bytesAt s.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66=Spec.Sha3.bytesAt σ.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66 := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_output.sub_left (seed_sub hk)
  · exact hp.seed_work.sub_left (seed_sub hk)

theorem zeroAll_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => SamplerEnv σ t ∧
      ∀i<50,t.mem.read (wordAddr (scr σ) i) 16=0 := by
  refine WP.mono (zeros_ok he.x19 (fun i hi => sampler_in_work hp he.wr (by omega_arith))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩

theorem absorbPair_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) {p : Nat} (hstream : 2*p+1<4)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => SamplerEnv σ t ∧
      PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  have hpn : p<2 := by omega_arith
  rw [absorbPair_eq,WP.block_append_iff]
  refine WP.mono (absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : SamplerEnv σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := seedP σ+BitVec.ofNat 64 (66*(2*p))
  let b := seedP σ+BitVec.ofNat 64 (66*(2*p+1))
  have e2' : s1.gpr .x2 = stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 132*p = 66*(2*p) by omega_arith]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 132*p+66 = 66*(2*p+1) by omega_arith]
  have seed_in (k : Nat) (hk : k < 4) (d n : Nat) (hd : d+n ≤ 66) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (66*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact sampler_in_seed hp he1.rd (by omega_arith)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    change InRegions s1.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact sampler_in_work hp he1.wr (by omega_arith)
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega_arith)
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega_arith) (8*j) 8 (by omega_arith))
    (fun j hj => seed_in (2*p+1) (by omega_arith) (8*j) 8 (by omega_arith))
    (seed_in (2*p) (by omega_arith) 64 1 (by decide)) (seed_in (2*p) (by omega_arith) 65 1 (by decide))
    (seed_in (2*p+1) (by omega_arith) 64 1 (by decide)) (seed_in (2*p+1) (by omega_arith) 65 1 (by decide))
    hws ((hp.seed_work.sub_left (seed_sub (by omega_arith))).sub_right hps)
    ((hp.seed_work.sub_left (seed_sub (by omega_arith))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega_arith : 2*p < 4),seed_eq hp he1 (by omega_arith : 2*p+1 < 4)] at hp2
    simpa only [samplerA,samplerSeedAt,seedState_eq] using hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourStart.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr)

def samplerInit : List Instr := Impl.MlDsa.AArch64.Sample.Rej4.pro++
 Impl.MlDsa.AArch64.Sample.Rej4.zeroStates++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 0++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.absorbPair 1

theorem pairs_disjoint (σ : State) : (pairR (stateP σ 0)).Disjoint (pairR (stateP σ 1)) :=
  Offset.disjoint (scr σ) (d := 400*0) (e := 400*1) (n := 400) (k := 400) (by decide) (by decide) (by decide)

theorem state_word (σ : State) (p i : Nat) : wordAddr (stateP σ p) i = wordAddr (scr σ) (25*p+i) := by
  change stateP σ p + BitVec.ofNat 64 (16*i) = scr σ + BitVec.ofNat 64 (16*(25*p+i))
  change (scr σ + BitVec.ofNat 64 (400*p)) + BitVec.ofNat 64 (16*i) = _
  rw [Offset.add_add,show 400*p+16*i = 16*(25*p+i) by omega_arith]

/-- Absorb all four seeds as two pairs of lanes, preserving the ABI save record. -/
theorem initFour_ok {σ : State} (hp : SamplerPre σ) : WP isa (.block samplerInit) σ fun t => SamplerEnv σ t ∧
    PairAt t.mem (stateP σ 0) (samplerA σ 0) (samplerA σ 1) ∧
    PairAt t.mem (stateP σ 1) (samplerA σ 2) (samplerA σ 3) := by
  unfold samplerInit
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (samplerPro_ok hp) fun s1 he1 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (zeroAll_ok hp he1) fun s2 ⟨he2,hz2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (absorbPair_ok (p := 0) hp he2 (by decide : 2*0+1 < 4) (fun i hi => by
    rw [state_word,Nat.mul_zero,Nat.zero_add]; exact hz2 i (by omega_arith))) fun s3 ⟨he3,hp3,hf3⟩ => ?_
  have hz3 : ∀ i < 25,s3.mem.read (wordAddr (stateP σ 1) i) 16 = 0 := by
    intro i hi
    rw [hf3.read (pair_contains (stateP σ 1) hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (pairs_disjoint σ).symm) (by decide),state_word]
    exact hz2 (25+i) (by omega_arith)
  refine WP.mono (absorbPair_ok (p := 1) hp he3 (by decide : 2*1+1 < 4) hz3) fun t ⟨het,hpt,hft⟩ => ?_
  refine ⟨het,?_,hpt⟩
  intro i hi
  rw [hft.read (pair_contains (stateP σ 0) hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact pairs_disjoint σ) (by decide)]
  exact hp3 i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourReady.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open ResidentRej (stateP scr lowR)

structure InitialPairs (σ s : State) : Prop where
 env : SamplerEnv σ s
 pair : ∀p<2,PairAt s.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1))

structure Ready (σ s : State) : Prop extends InitialPairs σ s where
 counts : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256
 table : TableAt s.mem (scr σ+6000)

theorem pairs_count_keep {σ s t : State} (hs : InitialPairs σ s)
    (hf : Frame [⟨scr σ+7904#64,32⟩] s.mem t.mem) {p : Nat} (hp : p<2) :
    PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint (scr σ) (d := 400*p) (e := 7904) (n := 400) (k := 32)
      (by omega_arith) (by omega_arith) (by decide)) (by decide)]
  exact hs.pair p hp i hi

theorem initCounts_pairs {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts) s fun t=>
      InitialPairs σ t ∧∀i<4,t.mem.readW (countAt (scr σ) i) 64=256 := by
  refine WP.mono (initCounts_ok hs.env.x19 (fun i hi=>sampler_in_work hp hs.env.wr (by omega_arith)))
    fun t ⟨⟨ht,hf,hc⟩,_⟩=>?_
  refine ⟨⟨?_,fun p hp=>pairs_count_keep hs hf hp⟩,hc⟩
  exact hs.env.lowStep hf (fun r hr=>by
    rw [List.mem_singleton.mp hr]
    exact Offset.sub_base (scr σ) (d := 7904) (n := 32) (k := 7968) (by decide))
    ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> decide))

theorem tableInit_ready {σ s : State} (hp : SamplerPre σ) (hs : InitialPairs σ s)
    (hc : ∀i<4,s.mem.readW (countAt (scr σ) i) 64=256) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)) s (Ready σ) := by
  rw [←List.append_nil (Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true)]
  refine tableInit_ok (fun a n h=>?_) fun t ht hv htable hf=>WP.block_nil_iff.mpr ?_
  · obtain ⟨r,hr,hcontains⟩:=h
    rw [List.mem_singleton.mp hr] at hcontains
    rw [hs.env.x19] at hcontains
    rw [hs.env.wr,hp.wr]
    exact ⟨samplerWorkspace σ,by simp,by
      change (a-scr σ).toNat+n≤8192
      change (a-(scr σ+6000#64)).toNat+n≤1024 at hcontains
      have hadd : a-scr σ=(a-(scr σ+6000#64))+6000#64 := by bv_omega
      rw [hadd]
      rw [BitVec.toNat_add,show (6000#64).toNat=6000 from rfl]
      have hh:=Nat.mod_le ((a-(scr σ+6000#64)).toNat+6000) (2^64)
      omega_arith⟩
  · rw [hs.env.x19] at hf htable
    refine ⟨⟨?_,?_⟩,?_,htable⟩
    · exact hs.env.lowStep hf (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.sub_base (scr σ) (d := 6000) (n := 1024) (k := 7968) (by decide))
        ht.rd ht.wr ht.sp (fun r hr=>ht.get r (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl|rfl|rfl|rfl <;> decide))
    · intro p hp i hi
      rw [hf.read (pair_contains (stateP σ p) hi) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 400*p) (e := 6000) (n := 400) (k := 1024)
          (by omega_arith) (by omega_arith) (by decide)) (by decide)]
      exact hs.pair p hp i hi
    · intro i hi
      rw [hf.readW (Region.contains_self (countAt (scr σ) i) 8) (fun r hr=>by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint (scr σ) (d := 7904+8*i) (e := 6000) (n := 8) (k := 1024)
          (by omega_arith) (by omega_arith) (by decide)) (by decide)]
      exact hc i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def samplerSetup : List Instr := samplerInit++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true

theorem samplerSetup_ok {σ : State} (hp : SamplerPre σ) :
    WP isa (.block samplerSetup) σ (Ready σ) := by
  unfold samplerSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (initFour_ok hp) fun s ⟨he,h0,h1⟩=>?_
  have hs : InitialPairs σ s := ⟨he,fun p h=>by
    rcases (show p=0∨p=1 by omega_using [h]) with rfl|rfl
    · exact h0
    · exact h1⟩
  rw [WP.block_append_iff]
  refine WP.mono (initCounts_pairs hp hs) fun t ⟨ht,hc⟩=>?_
  exact tableInit_ready hp ht hc

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

/-! ### `MlDsa.AArch64.Optimized.BoundedFourMaskInit`, which only this module used -/

section

/-! ## From `BoundedFourMaskLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem maskGuard {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) :
    isa.eval (.nonzero .x .x5) s=some (decide (j<64)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega_using []

theorem maskLoop_ok {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) (hj : j<64)
    (hr : ∀i<64,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5)) s
      (fun t=>MaskInv σ t p v 64) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=64-j ∧MaskInv σ s p v j ∧j<64)
    ?_ (64-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (maskStep_ok hi hj hr hw) fun t ht=>?_
  have hg:=maskGuard ht
  by_cases hn : j+1<64
  · exact .inr ⟨by rw [hg,decide_eq_true hn],64-(j+1),by omega_using [hj],j+1,rfl,ht,hn⟩
  · have he : j+1=64 := by omega_using [hj, hn]
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def outputMask (x : BitVec 64) : BitVec 128 := if x=0#64 then ~~~0#128 else 0#128

def maskScalar : List Instr :=
 [.subImm .x .x4 .x4 1,.lsr .x .x4 .x4 63,.movz .x .x6 0 0,.sub .w .x4 .x6 .x4]

theorem maskScalar_ok (s : State) (hx : (s.gpr .x4).toNat≤256) :
    WP isa (.block maskScalar) s fun t=>
      ((t.gpr .x4=(if s.gpr .x4=0#64 then 4294967295#64 else 0#64) ∧t.mem=s.mem) ∧
        Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskScalar
  arun
  have h:=ResidentRej.smallFlag_status (s.gpr .x4) (by omega_using [hx])
  rw [h]
  by_cases hz : s.gpr .x4=0#64
  · simp only [ite_eq_left hz]
    rfl
  · simp only [ite_eq_right hz]
    rfl

def maskFooter (k : Nat) : List Instr :=
 [.addImm .x .x3 .x21 (1024*k),.movz .x .x5 64 0]

theorem maskFooter_ok (s : State) {k : Nat} (hk : k<4) :
    WP isa (.block (maskFooter k)) s fun t=>
      ((t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧t.mem=s.mem) ∧
        Keep [.x3,.x5] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskFooter
  have hb : 1024*k<4096 := by omega_using [hk]
  arun [hb]


def maskLoadScalar (k : Nat) : List Instr := .ldr .x .x4 .x19 (7904+8*k)::maskScalar

theorem maskLoadScalar_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskLoadScalar k)) s fun t=>
      ((t.gpr .x4=(if s.mem.readW (countAt b k) 64=0#64 then 4294967295#64 else 0#64) ∧
        t.mem=s.mem) ∧Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold maskLoadScalar
  refine wp_ldrx (by omega_using [hk]) (by rw [hb]; rfl) hr fun a ha h4=>?_
  refine WP.mono (maskScalar_ok a (by rw [h4]; exact hx)) fun t ⟨⟨⟨hv,hm⟩,ht⟩,_⟩=>?_
  exact ⟨⟨by rw [hv,h4],hm.trans ha.mem⟩,(ha.keep.trans ht).mono (by decide)⟩

def maskSetup (k : Nat) : List Instr := maskLoadScalar k ++
 [.vop (.dup .s4 .v0 .x4)]++maskFooter k

theorem maskSetup_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskSetup k)) s fun t=>
      InitKeep [.x3,.x4,.x5,.x6] [.v0] s t ∧
      t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧
      t.v .v0=outputMask (s.mem.readW (countAt b k) 64) := by
  unfold maskSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (maskLoadScalar_ok hk hb hr hx) fun a ⟨⟨⟨h4,hm⟩,ha⟩,hv⟩=>?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v0) rfl fun c hc=>?_
  refine WP.mono (maskFooter_ok c hk) fun t ⟨⟨⟨hp,h5,htm⟩,ht⟩,htv⟩=>?_
  refine ⟨?_,?_,h5,?_⟩
  · refine ⟨((ha.trans (hc.keep (by decide))).trans ht).mono (by decide),?_,?_⟩
    · rw [htm,hc.mem,hm]
    · intro r hr
      rw [htv,hc.other r (by simpa using hr),hv]
  · rw [hp,hc.gpr,ha.get .x21]
  · rw [htv,hc.v,h4]
    unfold outputMask
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end


/-! ## From `BoundedFourMaskOne.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

theorem maskOne_ok {s : State} {k : Nat} (hk : k<4) {b p : Addr}
    (hb : s.gpr .x19=b) (hp : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p)
    (hc : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256)
    (hr : ∀i<64,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>
      Keep [.x3,.x4,.x5,.x6] s t ∧
      (∀r,r∉[VReg.v0,.v1]→t.v r=s.v r) ∧Frame [polyR p] s.mem t.mem ∧
      (s.mem.readW (countAt b k) 64=0#64→t.mem=s.mem) ∧
      (s.mem.readW (countAt b k) 64≠0#64→∀i<256,coeffAt t.mem p i=0#32) := by
  change WP isa (.seq (.block (maskSetup k))
    (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5))) s _
  refine WP.seq (WP.mono (maskSetup_ok hk hb hc hx) fun a ⟨ha,hp',h5,hv⟩=>?_)
  let v:=outputMask (s.mem.readW (countAt b k) 64)
  have hi : MaskInv a a p v 0 := by
    refine ⟨by decide,Keep.refl _ _,fun _ _=>rfl,rfl,?_,h5,hv⟩
    change a.gpr .x3=p+0#64
    rw [BitVec.add_zero]
    exact hp'.trans hp
  refine WP.mono (maskLoop_ok hi (by decide)
    (fun i hi=>by rw [ha.keep.rd,ha.keep.wr]; exact hr i hi)
    (fun i hi=>by rw [ha.keep.wr]; exact hw i hi)) fun t ht=>?_
  refine ⟨(ha.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r h
    rw [ht.vec r (by simpa using fun he=>h (by simp [he])),ha.vec r (fun he=>h (by simp_all))]
  · rw [ht.mem,ha.mem]
    exact maskRun_frame _ _ _ (by decide)
  · intro hz
    rw [ht.mem,ha.mem]
    change maskRun s.mem p (outputMask _) 64=s.mem
    rw [outputMask,ite_eq_left hz,maskRun_identity]
  · intro hz i hi
    rw [ht.mem,ha.mem]
    change coeffAt (maskRun s.mem p (outputMask _) 64) p i=0#32
    rw [outputMask,ite_eq_right hz]
    exact maskRun_zero (by decide) i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskRows.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def maskedWord (m : Mem) (b p : Addr) (i j : Nat) : BitVec 32 :=
 if m.readW (countAt b i) 64=0#64 then coeffAt m (outputAt p i) j else 0#32

structure MaskRows (σ s : State) (b p : Addr) (k : Nat) : Prop where
 keep : Keep [.x3,.x4,.x5,.x6] σ s
 frame : Frame [⟨p,4096⟩] σ.mem s.mem
 counts : ∀i<4,s.mem.readW (countAt b i) 64=σ.mem.readW (countAt b i) 64
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt p i) j=
   if i<k then maskedWord σ.mem b p i j else coeffAt σ.mem (outputAt p i) j

theorem maskRows_zero (s : State) (b p : Addr) : MaskRows s s b p 0 :=
 ⟨Keep.refl _ _,Frame.refl _ _,fun _ _=>rfl,by intro i hi j hj; simp⟩

theorem maskRows_step {σ s : State} {b p : Addr} {k : Nat} (hk : k<4)
    (hs : MaskRows σ s b p k) (hb : σ.gpr .x19=b) (hp : σ.gpr .x21=p)
    (hbound : ∀i<4,(σ.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (σ.rd++σ.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (σ.rd++σ.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions σ.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (polyR (outputAt p j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>MaskRows σ t b p (k+1) := by
  refine WP.mono (maskOne_ok (s := s) (b := b) (p := outputAt p k) hk (by rw [hs.keep.get .x19]; exact hb)
    (by rw [hs.keep.get .x21,hp]; rfl)
    (by rw [hs.keep.rd,hs.keep.wr]; exact hrc k hk)
    (by rw [hs.counts k hk]; exact hbound k hk)
    (fun j hj=>by rw [hs.keep.rd,hs.keep.wr]; exact hr k hk j hj)
    (fun j hj=>by rw [hs.keep.wr]; exact hw k hk j hj)) fun t ⟨ht,_,hf,hyes,hno⟩=>?_
  refine ⟨(hs.keep.trans ht).mono (by decide),hs.frame.trans (hf.sub (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact ⟨_,by simp,outputAt_sub p hk⟩)),?_,?_⟩
  · intro i hi
    rw [hf.readW (Region.contains_self _ _) (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hsep i hi k hk) (by decide)]
    exact hs.counts i hi
  · intro i hi j hj
    by_cases hik : i=k
    · subst i
      rw [ite_eq_left (by omega_using [])]
      unfold maskedWord
      by_cases hz : σ.mem.readW (countAt b k) 64=0#64
      · rw [ite_eq_left hz,hyes (by rw [hs.counts k hk]; exact hz),hs.words k hk j hj,ite_eq_right (by omega_using [])]
      · rw [ite_eq_right hz]
        exact hno (by rw [hs.counts k hk]; exact hz) j hj
    · have hframe : coeffAt t.mem (outputAt p i) j=coeffAt s.mem (outputAt p i) j := by
        unfold coeffAt
        apply hf.readW
          (Offset.contains_base (outputAt p i) (by omega_using [hj] : 4*j+4≤1024) (by omega_using [hj]))
          (fun r hr=>by rw [List.mem_singleton.mp hr]; exact outputs_apart p hi hk hik) (by decide)
      rw [hframe,hs.words i hi j hj]
      by_cases hlt : i<k
      · rw [ite_eq_left hlt,ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt,ite_eq_right (by omega_using [hik, hlt])]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def maskFour : Prog isa :=
 .seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 0)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 1)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 2)
       (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 3)))

theorem maskFour_ok {s : State} {b p : Addr} (hb : s.gpr .x19=b) (hp : s.gpr .x21=p)
    (hbound : ∀i<4,(s.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (s.rd++s.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (s.rd++s.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions s.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (Proof.MlDsa.Sample.polyR (outputAt p j))) :
    WP isa maskFour s (fun t=>MaskRows s t b p 4) := by
  unfold maskFour
  refine WP.seq (WP.mono (maskRows_step (by decide) (maskRows_zero s b p) hb hp hbound hrc hr hw hsep) fun a ha=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) ha hb hp hbound hrc hr hw hsep) fun b hb'=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) hb' hb hp hbound hrc hr hw hsep) fun c hc=>?_)
  exact maskRows_step (by decide) hc hb hp hbound hrc hr hw hsep

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
