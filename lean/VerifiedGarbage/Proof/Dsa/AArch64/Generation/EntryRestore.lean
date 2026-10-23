module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill

import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Restore every AAPCS64 preserved register from its protected slot. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure RestoredEntry (s t u : State) : Prop where
  gprs : ∀ r ∈ preserved, u.gpr r = s.gpr r
  vectors : ∀ v ∈ preservedV, (u.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64
  memory : u.mem = t.mem
  stack : u.sp = t.sp
  read : u.rd = t.rd
  write : u.wr = t.wr
  result : u.gpr .x0 = t.gpr .x0

theorem entryRestore_ok {s t : State}
    (sp : t.sp = generationBase s)
    (read : ∀ d, d + 8 ≤ 448 → InRegions (t.rd ++ t.wr) (generationBase s + BitVec.ofNat 64 d) 8)
    (g : Spill.Saved (generationBase s) s.gpr abiGprs t.mem)
    (v : Spill.Saved (generationBase s) (vectorValues s) vectorSlots t.mem)
    (lr : t.mem.readW (generationBase s + BitVec.ofNat 64 296) 64 = s.gpr .x30) :
    WP isa (.block entryRestore) t (RestoredEntry s t) := by
  simp only [entryRestore, abiGprs, abiVectors, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append]
  brun [exec_ldrSp (off := 304) (by decide),
    exec_ldrSp (off := 312) (by decide),
    exec_ldrSp (off := 320) (by decide),
    exec_ldrSp (off := 328) (by decide),
    exec_ldrSp (off := 336) (by decide),
    exec_ldrSp (off := 344) (by decide),
    exec_ldrSp (off := 352) (by decide),
    exec_ldrSp (off := 360) (by decide),
    exec_ldrSp (off := 368) (by decide),
    exec_ldrSp (off := 376) (by decide),
    exec_ldrSp (off := 384) (by decide),
    exec_ldrSp (off := 392) (by decide),
    exec_ldrSp (off := 400) (by decide),
    exec_ldrSp (off := 408) (by decide),
    exec_ldrSp (off := 416) (by decide),
    exec_ldrSp (off := 424) (by decide),
    exec_ldrSp (off := 432) (by decide),
    exec_ldrSp (off := 440) (by decide),
    exec_ldrSp (off := 296) (by decide),
    exec_ins (by decide : 0 < 2),
    sp,
    read 304 (by decide),
    read 312 (by decide),
    read 320 (by decide),
    read 328 (by decide),
    read 336 (by decide),
    read 344 (by decide),
    read 352 (by decide),
    read 360 (by decide),
    read 368 (by decide),
    read 376 (by decide),
    read 384 (by decide),
    read 392 (by decide),
    read 400 (by decide),
    read 408 (by decide),
    read 416 (by decide),
    read 424 (by decide),
    read 432 (by decide),
    read 440 (by decide),
    read 296 (by decide),
    g ⟨.x19, 304⟩ (by decide),
    g ⟨.x20, 312⟩ (by decide),
    g ⟨.x21, 320⟩ (by decide),
    g ⟨.x22, 328⟩ (by decide),
    g ⟨.x23, 336⟩ (by decide),
    g ⟨.x24, 344⟩ (by decide),
    g ⟨.x25, 352⟩ (by decide),
    g ⟨.x26, 360⟩ (by decide),
    g ⟨.x27, 368⟩ (by decide),
    g ⟨.x28, 376⟩ (by decide),
    v ⟨.x0, 384⟩ (by decide),
    v ⟨.x1, 392⟩ (by decide),
    v ⟨.x2, 400⟩ (by decide),
    v ⟨.x3, 408⟩ (by decide),
    v ⟨.x4, 416⟩ (by decide),
    v ⟨.x5, 424⟩ (by decide),
    v ⟨.x6, 432⟩ (by decide),
    v ⟨.x7, 440⟩ (by decide),
    lr,
    vectorValues,
    laneOf,
    State.write,
    State.setV]
  refine ⟨?_, ?_, rfl, sp.symm, rfl, rfl, rfl⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    all_goals exact extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)

end VG.Proof.Dsa.AArch64.Generation
