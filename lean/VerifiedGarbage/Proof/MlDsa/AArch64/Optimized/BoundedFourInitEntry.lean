import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitStore

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
