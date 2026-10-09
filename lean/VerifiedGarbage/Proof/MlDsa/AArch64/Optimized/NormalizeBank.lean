import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Normalize
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Bank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem normalizeBank_ok (regs : Vector VReg 8) (hd : regs.toList.Nodup)
    (ha : ∀ d ∈ regs.toList, d ≠ .v4 ∧ d ≠ .v16)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    (hb : Bank s regs values) (hq : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (.v4::regs.toList) s t →
      Bank t regs (values.map positiveVector) → WP isa (.block rest) t Q) :
    WP isa (.block (regs.toList.flatMap canon ++ rest)) s Q := by
  refine positive_many_ok regs.toList hd ha hq fun t hc hv => k t hc ?_
  intro i
  have hi : i.val < regs.toList.length := by simp
  have hm : regs[i.val] ∈ regs.toList := by
    simpa only [Vector.getElem_toList] using List.getElem_mem hi
  rw [hv _ hm,hb i,Vector.getElem_map]

end VG.Proof.MlDsa.AArch64.Optimized
