module

public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal4
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Pair iterations can be grouped in fours using the public remaining count. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

 theorem rowBodyU_count {s t : State} {tr : List Leak}
    (run : Exec isa (.block rowBodyU) s tr t) :
    t.gpr .lr = s.gpr .lr - 2 ∧ t.z = (t.gpr .lr == 0) := by
  have block := Exec.block_iff.mp run
  rw [rowBodyU, execBlock_append] at block
  cases hp : execBlock isa (rowFirstU ++ rowStepU 4) s with
  | none => simp only [hp, Option.bind_none, reduceCtorEq] at block
  | some out =>
    obtain ⟨u, trace⟩ := out
    simp only [hp, Option.bind_some, advState_exec, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at block
    obtain ⟨rfl, _⟩ := block
    have kept : u.gpr .lr = s.gpr .lr := execBlock_gpr (by
      intro i hi
      simp only [List.mem_append, rowFirstU, rowStepU, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> rfl) hp
    simp only [advState, gpr_setReg, subFlags, kept, ↓reduceIte]
    exact ⟨trivial,rfl⟩

 theorem rowBodyU_count_nat {s t : State} {tr : List Leak}
    (run : Exec isa (.block rowBodyU) s tr t) (large : 2 ≤ (s.gpr .lr).toNat) :
    (t.gpr .lr).toNat = (s.gpr .lr).toNat - 2 ∧ t.z = decide ((s.gpr .lr).toNat = 2) := by
  obtain ⟨count,zero⟩ := rowBodyU_count run
  have value : (t.gpr .lr).toNat = (s.gpr .lr).toNat - 2 := by
    rw [count, BitVec.toNat_sub]
    have := (s.gpr .lr).isLt
    change (2 ^ 32 - 2 + (s.gpr .lr).toNat) % 2 ^ 32 = _
    omega
  refine ⟨value, ?_⟩
  rw [zero]
  apply Bool.eq_iff_iff.mpr
  have equiv : t.gpr .lr = 0 ↔ (t.gpr .lr).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  simp only [beq_iff_eq, decide_eq_true_eq, equiv, value]
  omega

/-- The arithmetic packet interface: incoming flags may differ, and only
zero-count exits require all outgoing flags to agree. -/
def RowFourFusion : Prop := ∀ {s n u v : State} {tr1 tr2 : List Leak},
  NoFlags s n → Exec isa (.block rowBodyU) s tr1 u → Exec isa (.block rowBodyU) u tr2 v →
  ∃ n', Exec isa (.block rowBodyU4) n (tr1 ++ tr2) n' ∧ NoFlags v n' ∧ v.z = n'.z ∧
    (v.gpr .lr = 0 → v = n')

 theorem rowLoopU4_control (fusion : RowFourFusion) : ∀ count : Nat,
    ∀ {s n t : State} {tr : List Leak}, (s.gpr .lr).toNat = count →
      0 < count → count % 4 = 0 → NoFlags s n →
      Exec isa (.loop (.block rowBodyU) .ne) s tr t →
      ∃ newTrace, Exec isa (.loop (.block rowBodyU4) .ne) n newTrace t := by
  intro count
  induction count using Nat.strongRecOn with
  | ind count ih =>
    intro s n t tr value positive even agree run
    have large : 4 ≤ count := by omega
    cases run with
    | loopExit first exit =>
      obtain ⟨_, zero⟩ := rowBodyU_count_nat first (by omega)
      change some (!_) = some false at exit
      rw [zero, show decide ((s.gpr .lr).toNat = 2) = false by simp only [decide_eq_false_iff_not,value]; omega] at exit
      cases exit
    | loopNext first _ tail =>
      obtain ⟨middle, zero1⟩ := rowBodyU_count_nat first (by omega)
      have middleLarge : 2 ≤ (s.gpr .lr).toNat - 2 := by omega
      rw [← middle] at middleLarge
      cases tail with
      | loopExit second exit =>
        obtain ⟨last,zero2⟩ := rowBodyU_count_nat second middleLarge
        obtain ⟨v,packet,_,sameZero,terminal⟩ := fusion agree first second
        have exitZ : t.z = true := by
          cases z : t.z with
          | false => change some (!t.z) = some false at exit; rw [z] at exit; cases exit
          | true => rfl
        have middleEq := of_decide_eq_true (zero2.symm.trans exitZ)
        have oldZero : t.gpr .lr = 0 := by
          apply BitVec.eq_of_toNat_eq
          change (t.gpr .lr).toNat = 0
          omega
        have equal := terminal oldZero
        subst v
        exact ⟨_, Exec.loopExit packet (by simpa only [eval, sameZero] using exit)⟩
      | loopNext second branch rest =>
        obtain ⟨last,zero2⟩ := rowBodyU_count_nat second middleLarge
        obtain ⟨v,packet,nf,sameZero,_⟩ := fusion agree first second
        have branchZ : v.z = false := by
          change some (!_) = some true at branch
          rw [sameZero] at branch
          cases z : v.z with
          | false => rfl
          | true => rw [z] at branch; cases branch
        have middleNe := of_decide_eq_false (zero2.symm.trans (sameZero.trans branchZ))
        have nextPositive : 0 < count - 4 := by omega
        have nextEven : (count - 4) % 4 = 0 := by omega
        obtain ⟨trace, recurse⟩ := ih (count - 4) (by omega) (by omega) nextPositive nextEven nf rest
        exact ⟨_, Exec.loopNext packet (by simpa only [eval,← sameZero] using branch) recurse⟩

end VG.Proof.Bignum.Arm
