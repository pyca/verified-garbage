module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Composition
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Rotation
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE

theorem cmpLength_ok (s : State) :
    ∃ s', runBlock isa [.subi .r8 .r4 16] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (s.gpr .r4 == 16) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r4 - BitVec.ofNat 64 16), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq]
    exact congrArg some (by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      bv_omega)

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Kept [.r8] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr),
    by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x == 16) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0) :
    WP isa Impl.TripleDes.PPC64LE.Key.expandKey s (Components origin · 3) := by
  rw [Impl.TripleDes.PPC64LE.Key.expandKey]
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpLength_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have hs₃ := hs₂.keep keep₃
  have flag : isa.eval (.zero .d .r8) s₃ = some (decide ((origin.gpr .r4).toNat = 16)) := by
    rw [flag₃, hs₂.reg .r4 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .r4).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

end VG.Proof.TripleDes.PPC64LE.Key
