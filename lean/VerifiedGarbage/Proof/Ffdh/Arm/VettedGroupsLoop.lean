module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsStep
import VerifiedGarbage.Proof.Framework.Block

/-! The exact-domain scan returns the first matching table record or zero. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem loop_ok {table src : BitVec 32} {k : Nat} {dom : List Byte} {gs : List Group}
    (s : State) (source : Source src k dom s) (tableAt : TableAt table gs s)
    (cursor : Cursor table src k dom gs s) (positive : gs ≠ [])
    (kfit : k < 2 ^ 32) (fit : gs.length < 2 ^ 32) :
    WP isa loop s fun t => t.gpr .r11 = BitVec.ofNat 32 (recognize gs k dom) ∧
      t.mem = s.mem ∧ Rest clobbers s t := by
  induction gs generalizing s table with
  | nil => exact False.elim (positive rfl)
  | cons g gs ih =>
    have nextFit : gs.length < 2 ^ 32 := by simp only [List.length_cons] at fit; omega
    obtain ⟨trace, u, run, memU, result, restU⟩ := step_ok s source tableAt.1 cursor kfit nextFit
    by_cases hit : g.len = k ∧ dom = g.domain.take dom.length
    · rw [ite_eq_left hit] at result
      refine ⟨_, u, Exec.loopExit run ?_, ?_, memU, restU⟩
      · simp only [eval, result.2.2, Bool.not_true]
      · simpa only [recognize, ite_eq_left hit] using result.1
    · rw [ite_eq_right hit] at result
      by_cases last : gs = []
      · subst gs
        refine ⟨_, u, Exec.loopExit run ?_, ?_, memU, restU⟩
        · simp only [eval, result.2.2.2, List.length_nil, decide_true, Bool.not_true]
        · simp only [recognize, ite_eq_right hit]
          apply BitVec.eq_of_toNat_eq
          rw [result.1]
          rfl
      · have cursorU : Cursor (table + BitVec.ofNat 32 (8 + 3 * g.len)) src k dom gs u :=
          ⟨result.2.1, result.2.2.1,
            (restU.gpr .r6 (by simp [clobbers])).trans cursor.width,
            (restU.gpr .r9 (by simp [clobbers])).trans cursor.source,
            (restU.gpr .r10 (by simp [clobbers])).trans cursor.length⟩
        have ready := ih u (source.after memU restU) (tableAt.2.after memU restU) cursorU last nextFit
        obtain ⟨traceT, t, runT, capT, memT, restT⟩ := ready
        refine ⟨_, t, Exec.loopNext run ?_ runT, ?_, memT.trans memU, restU.trans restT⟩
        · have hn : gs.length ≠ 0 := by intro hz; apply last; exact List.eq_nil_of_length_eq_zero hz
          simp only [eval, result.2.2.2, hn, decide_false, Bool.not_false]
        · simpa only [recognize, ite_eq_right hit] using capT

end VG.Proof.Ffdh.Arm.VettedGroups
