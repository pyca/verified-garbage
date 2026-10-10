import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitCode
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-! ## From `BoundedFourInitStore.lean` -/

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
    refine wp_movz fun u hu hval => wp_strx (by omega) rfl
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
  refine storeConstant_ok (by omega) (by simpa using hw 0 (by simp)) fun a ha hav ham => ?_
  refine storeConstant_ok (by omega)
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
      (p+BitVec.ofNat 64 (6000+64*mask)) 16 := Offset.contains p (by omega) (by omega) (by omega)
  have h32 : (⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ : Region).Contains
      (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 := Offset.contains p (by omega) (by omega) (by omega)
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem initEntryMemory_read (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    (initEntryMemory m p mask).read (p+BitVec.ofNat 64 (6000+64*mask)) 16=shuffleWord mask ∧
    (initEntryMemory m p mask).readW (p+BitVec.ofNat 64 (6000+64*mask+32)) 64=
      BitVec.ofNat 64 (acceptedIndices mask).length := by
  rw [initEntryMemory_eq m p hm]
  constructor
  · rw [Mem.writeW,Mem.read_write_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
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
      ⟨p+BitVec.ofNat 64 (6000+64*mask),64⟩ := Offset.disjoint p (by omega) (by omega) (by omega)
  constructor
  · exact hf.read (Offset.contains p (e := 6000+64*other) (k := 64) (by omega) (by omega) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
  · exact hf.readW (Offset.contains p (e := 6000+64*other) (k := 64) (by omega) (by omega) (by omega))
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
