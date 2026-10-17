module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicStack
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Saved public arguments survive workspace and acceptance-slot writes -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem PublicStack.after_checks {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat} {rs : List Reg}
    (h : PublicStack base dst np ep xp len k eLen s)
    (frame : Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem)
    (rest : Rest rs s t) : PublicStack base dst np ep xp len k eLen t := by
  have word (d : Nat) (fit : d + 4 ≤ 80) (gap : d + 4 ≤ 48 ∨ 52 ≤ d) :
      t.mem.readW (off (State.addr s.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
    apply frame.readW (r := ⟨off (State.addr s.sp) d, 4⟩) (by simp [Region.Contains]) _ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.separate.sub_left (Offset.sub_base _ fit)
    · exact Offset.disjoint _ gap (by omega) (by decide)
  refine ⟨by rw [rest.sp]; exact h.nowrap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr, rest.sp]; exact h.frameWritable
  · rw [rest.rd, rest.wr, rest.sp]; exact h.argumentsRead
  · rw [rest.sp]; exact h.separate
  · rw [rest.sp]
    have keep := word 0 (by decide) (by decide)
    simpa only [off, BitVec.add_zero] using keep.trans (by simpa only [off, BitVec.add_zero] using h.savedBase)
  · rw [rest.sp, word 4 (by decide) (by decide)]; exact h.savedOutput
  · rw [rest.sp, word 8 (by decide) (by decide)]; exact h.savedModulus
  · rw [rest.sp, word 12 (by decide) (by decide)]; exact h.savedCount
  · rw [rest.sp, word 56 (by decide) (by decide)]; exact h.exponent
  · rw [rest.sp, word 60 (by decide) (by decide)]; exact h.exponentCount
  · rw [rest.sp, word 64 (by decide) (by decide)]; exact h.input
end VG.Proof.Bignum.Arm
