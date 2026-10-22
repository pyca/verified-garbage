module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundPolicy
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! Account separately for total rounds and uniform witnesses. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem round_count {s : State} {base : Addr} {bytes i uniform : Nat} {u : Bool}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (index : s.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i)
    (count : s.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform)
    (witness : s.mem.readW (off base witnessUniform) 32 = BitVec.ofNat 32 u.toNat) :
    WP isa (.block roundCount) s fun t =>
      t.gpr .ecx = BitVec.ofNat 32 (i + 1) ∧
      t.gpr .edx = BitVec.ofNat 32 (uniform + u.toNat) ∧
      t.mem = (s.mem.writeW (off base roundIndex) (BitVec.ofNat 32 (i + 1))).writeW
        (off base uniformCount) (BitVec.ofNat 32 (uniform + u.toNat)) ∧
      Keeps [.ecx, .edx] s t := by
  have indexFit : roundIndex + 4 ≤ bytes := Nat.le_trans (by decide : roundIndex + 4 ≤ 40960) capacity
  have countFit : uniformCount + 4 ≤ bytes := Nat.le_trans (by decide : uniformCount + 4 ≤ 40960) capacity
  have witnessFit : witnessUniform + 4 ≤ bytes := Nat.le_trans (by decide : witnessUniform + 4 ≤ 40960) capacity
  unfold roundCount
  refine wp_movS (readSrc_sc scr (d := roundIndex) (by omega)) fun a A _ =>
    wp_addS rfl fun b B _ => ?_
  have value : b.gpr .ecx = BitVec.ofNat 32 (i + 1) := by
    rw [B.gpr, A.gpr, index, BitVec.ofNat_add]
    rfl
  have Kb : Keeps [.ecx, .edx] s b := (A.keeps.mono (by decide)).trans (B.keeps.mono (by decide))
  have Sb := scr.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (d := roundIndex) (by omega)) (Sb.write indexFit) fun c C => ?_
  have Kc := Kb.trans (C.keeps _)
  have Sc := scr.of_keeps Kc (by decide)
  have countC : c.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform := by
    rw [C.mem, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : roundIndex + 4 ≤ uniformCount))
      (by decide) (by decide)) (by decide), B.mem, A.mem, count]
  have witnessC : c.mem.readW (off base witnessUniform) 32 = BitVec.ofNat 32 u.toNat := by
    rw [C.mem, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : roundIndex + 4 ≤ witnessUniform))
      (by decide) (by decide)) (by decide), B.mem, A.mem, witness]
  refine wp_movS (readSrc_sc Sc (d := uniformCount) (by omega)) fun d D _ => ?_
  have Kd := Kc.trans (D.keeps.mono (by decide))
  have Sd := scr.of_keeps Kd (by decide)
  refine wp_addS (readSrc_sc Sd (d := witnessUniform) (by omega)) fun e E _ => ?_
  have sum : e.gpr .edx = BitVec.ofNat 32 (uniform + u.toNat) := by
    rw [E.gpr, D.gpr, countC, D.mem, witnessC, ← BitVec.ofNat_add]
  have Ke := Kd.trans (E.keeps.mono (by decide))
  have Se := scr.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (d := uniformCount) (by omega)) (Se.write countFit) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, Ke.trans (T.keeps _)⟩
  · rw [T.gpr, E.other _ (by decide), D.other _ (by decide), C.gpr, value]
  · rw [T.gpr, sum]
  · rw [T.mem, sum, E.mem, D.mem, C.mem, value, B.mem, A.mem]

end VG.Proof.Dsa.X86.Generation
