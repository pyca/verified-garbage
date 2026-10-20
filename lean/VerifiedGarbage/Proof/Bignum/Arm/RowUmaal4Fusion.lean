module

public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Body
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Shift
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Control
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Two pair iterations fuse without changing their memory accesses. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem ready_noFlags (k : Nat) {s t : State} (h : NoFlags s t) :
    WordReadyU k s ↔ WordReadyU k t := by
  simp only [WordReadyU, h.rd, h.wr, h.gpr]

theorem ready_shift8 (k : Nat) (s : State) : WordReadyU k (shift8 s) ↔ WordReadyU (8+k) s := by
  simp only [WordReadyU, shift8, rd_setReg, wr_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte]
  have add (v : BitVec 32) : v + 8 + BitVec.ofNat 32 k = v + BitVec.ofNat 32 (8+k) := by
    rw [BitVec.add_assoc]
    congr 1
    exact (BitVec.ofNat_add 8 k).symm
  rw [add, add]

theorem rowFourFusion : RowFourFusion := by
  intro s n u v tr1 tr2 agree first second
  obtain ⟨hr0, hw0, hr4, hw4, rfl, trace1⟩ := rowBodyU_forward first
  obtain ⟨hr8, hw8, hr12, hw12, value2, trace2⟩ := rowBodyU_forward second
  let a := stepNew 4 (stepNew 0 s)
  let c := stepNew 12 (stepNew 8 a)
  have h8 : WordReadyU 8 s := by
    have h : WordReadyU 0 (advState a) := ⟨hr8,hw8⟩
    have h' := (ready_shift8 0 a).mp ((ready_noFlags 0 (advState_shift8 a)).mp h)
    exact h'
  have h12 : WordReadyU 12 s := by
    have h : WordReadyU 4 (advState a) := ⟨hr12,hw12⟩
    have h' := (ready_shift8 4 a).mp ((ready_noFlags 4 (advState_shift8 a)).mp h)
    exact h'
  have firstShift : NoFlags (stepNew 0 (advState a)) (shift8 (stepNew 8 a)) := by
    simpa only [stepNew_shift8, Nat.add_zero] using stepNew_noFlags 0 (advState_shift8 a)
  have secondShift : NoFlags (stepNew 4 (stepNew 0 (advState a))) (shift8 c) := by
    simpa only [stepNew_shift8, show 8+4=12 from rfl] using stepNew_noFlags 4 firstShift
  have value : v = advState (shift8 c) := value2.trans (advState_noFlags_eq secondShift)
  have same : NoFlags c (stepNew 12 (stepNew 8 (stepNew 4 (stepNew 0 n)))) :=
    stepNew_noFlags 12 (stepNew_noFlags 8 (stepNew_noFlags 4 (stepNew_noFlags 0 agree)))
  have output : advState4 (stepNew 12 (stepNew 8 (stepNew 4 (stepNew 0 n)))) = advState4 c :=
    (advState4_noFlags_eq same).symm
  have run := Exec.block_iff.mpr (rowBodyU4_exec n
    ((ready_noFlags 0 agree).mp ⟨hr0,hw0⟩) ((ready_noFlags 4 agree).mp ⟨hr4,hw4⟩)
    ((ready_noFlags 8 agree).mp h8) ((ready_noFlags 12 agree).mp h12))
  rw [output] at run
  have traces : tr1 ++ tr2 = wordTraceU 0 n ++ wordTraceU 4 n ++ wordTraceU 8 n ++ wordTraceU 12 n := by
    rw [trace1, trace2]
    simp only [wordTraceU, advState, stepNew, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte,
      BitVec.add_assoc, agree.gpr, List.append_assoc]
    rfl
  refine ⟨advState4 c, traces ▸ run, ?_, ?_, ?_⟩
  · rw [value]
    exact advState_shift8_four c
  · rw [value]
    simp only [advState, shift8, advState4, subFlags, z_setReg, gpr_setReg, reduceCtorEq, ↓reduceIte]
    congr 1
    rw [BitVec.sub_sub]
    rfl
  · intro zero
    have count : c.gpr .lr = 4 := by
      rw [value] at zero
      change (c.gpr .lr - 2) - 2 = 0 at zero
      rw [BitVec.sub_sub] at zero
      exact (BitVec.sub_eq_iff_eq_add.mp zero).trans (by decide)
    exact value.trans (advState_shift8_zero c count)

end VG.Proof.Bignum.Arm
