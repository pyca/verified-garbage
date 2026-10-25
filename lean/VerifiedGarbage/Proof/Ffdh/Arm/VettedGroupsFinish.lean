module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! Public success and continuation controls of the exact-domain scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd
open VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem zero_test (s : State) (r : Reg) :
    WP isa (.block [.cmp r (.imm 0)]) s fun t =>
      (t.z = (s.gpr r == 0) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest_all [] ?_ (by rfl) (by rfl)
  ffrun []
  change (s.gpr r - 0#32 == 0#32) = (s.gpr r == 0#32)
  rw [BitVec.sub_zero]

 theorem matched_ok (s : State) :
    WP isa (.block matched) s fun t => (t.gpr .r7 = 0 ∧ t.mem = s.mem) ∧ Rest [.r7] s t := by
  refine withRest_all [.r7] ?_ (by rfl) (by rfl)
  unfold matched
  ffrun []

 theorem next_ok (s : State) {table : BitVec 32} {len n : Nat}
    (ptr : s.gpr .r4 = table + 8) (size : s.gpr .r5 = BitVec.ofNat 32 (3 * len))
    (count : s.gpr .r7 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block next) s fun t =>
      (t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * len) ∧
       t.gpr .r7 = BitVec.ofNat 32 n ∧ t.mem = s.mem) ∧ Rest [.r4, .r7, .r11] s t := by
  refine withRest_all [.r4, .r7, .r11] ?_ (by rfl) (by rfl)
  have pc : (table + 8) + BitVec.ofNat 32 (3 * len) = table + BitVec.ofNat 32 (8 + 3 * len) := by
    change (table + BitVec.ofNat 32 8) + BitVec.ofNat 32 (3 * len) = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have nc : BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n := by
    change BitVec.ofNat 32 (n + 1) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  unfold next
  ffrun [ptr, size, count, pc, nc, BitVec.ofNat_eq_ofNat]
  exact ⟨pc, nc⟩

 theorem finish_ok (s : State) {table : BitVec 32} {len bits n : Nat} {hit : Prop}
    [Decidable hit] (equal : s.gpr .r2 = 0 ↔ hit)
    (ptr : s.gpr .r4 = table + 8) (size : s.gpr .r5 = BitVec.ofNat 32 (3 * len))
    (cap : s.gpr .r11 = BitVec.ofNat 32 bits) (count : s.gpr .r7 = BitVec.ofNat 32 (n + 1))
    (fit : n < 2 ^ 32) :
    WP isa finish s fun t => t.mem = s.mem ∧
      (if hit then t.gpr .r11 = BitVec.ofNat 32 bits ∧ t.gpr .r7 = 0 ∧ t.z = true else
        t.gpr .r11 = 0 ∧ t.gpr .r4 = table + BitVec.ofNat 32 (8 + 3 * len) ∧
          t.gpr .r7 = BitVec.ofNat 32 n ∧ t.z = decide (n = 0)) ∧
      Rest [.r4, .r7, .r11] s t := by
  rw [finish, WP.seq_iff]
  refine WP.mono (zero_test s .r2) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have test : u.z = decide hit := by
    rw [zero]
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, decide_eq_true_eq] using equal
  rw [WP.seq_iff]
  refine WP.ite (decide hit) (by simpa only [eval] using congrArg some test) ?_ ?_
  · intro yes
    have hy : hit := of_decide_eq_true yes
    refine WP.mono (matched_ok u) ?_
    rintro v ⟨⟨countV, memV⟩, restV⟩
    refine WP.mono (zero_test v .r7) ?_
    rintro t ⟨⟨zeroT, memT⟩, restT⟩
    refine ⟨memT.trans (memV.trans memU), ?_, ?_⟩
    · rw [ite_eq_left hy]
      exact ⟨(restT.gpr .r11 (by simp)).trans ((restV.gpr .r11 (by simp)).trans ((restU.gpr .r11 (by simp)).trans cap)),
        (restT.gpr .r7 (by simp)).trans countV, by rw [zeroT, countV]; rfl⟩
    · exact (restU.mono (by simp)).trans ((restV.mono (by simp)).trans (restT.mono (by simp)))
  · intro no
    have hn : ¬hit := of_decide_eq_false no
    refine WP.mono (next_ok u ((restU.gpr .r4 (by simp)).trans ptr)
      ((restU.gpr .r5 (by simp)).trans size) ((restU.gpr .r7 (by simp)).trans count)) ?_
    rintro v ⟨⟨capV, ptrV, countV, memV⟩, restV⟩
    refine WP.mono (zero_test v .r7) ?_
    rintro t ⟨⟨zeroT, memT⟩, restT⟩
    refine ⟨memT.trans (memV.trans memU), ?_, ?_⟩
    · rw [ite_eq_right hn]
      refine ⟨(restT.gpr .r11 (by simp)).trans capV, (restT.gpr .r4 (by simp)).trans ptrV,
        (restT.gpr .r7 (by simp)).trans countV, ?_⟩
      rw [zeroT, countV]
      exact VG.Proof.X25519.Arm.ofNat_beq_zero fit
    · exact (restU.mono (by simp)).trans (restV.trans (restT.mono (by simp)))

end VG.Proof.Ffdh.Arm.VettedGroups
