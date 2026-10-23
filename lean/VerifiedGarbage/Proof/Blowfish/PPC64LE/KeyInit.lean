module

public import VerifiedGarbage.Proof.Blowfish.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Blowfish on PPC64LE, key expansion: the initial schedule

`initSteps_run`: the 521 doublewords of the initial schedule's image, as
immediates, into the schedule at `r5`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE

/-- Doubleword `i` of the initial schedule. -/
def initStep (i : Nat) : List Instr :=
  movImm64 tmp (Impl.Blowfish.initWord i) ++ ([.store .d tmp .r5 (8 * i)] : List Instr)

theorem initSchedule_eq : initSchedule = (List.range 521).flatMap initStep := rfl

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem initStep_run (u : State) {S : Addr} {i : Nat} (hi : i < 521) (h5 : u.gpr .r5 = S)
    (hw : InRegions u.wr (S + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (initStep i)) u fun t =>
      t.mem = u.mem.writeW (S + BitVec.ofNat 64 (8 * i)) (Impl.Blowfish.initWord i) ∧ Keep [.r12] u t := by
  refine WP.mono (WP.keep [.r12] (Q := fun t =>
    t.mem = u.mem.writeW (S + BitVec.ofNat 64 (8 * i)) (Impl.Blowfish.initWord i)) ?_
    (by simp [writesOnly, Code.allInstrs_eq, instrs, initStep, movImm64, dstOf, tmp]) rfl)
    fun t ⟨a, b⟩ => ⟨a, b⟩
  unfold initStep movImm64
  brun [h5, hw, show 8 * i < 32768 by omega, show 8 * i % 4 = 0 by omega]
  exact congrArg _ (movImm64_eq _)

/-- The first `k` doublewords. -/
theorem initSteps_run {S : Addr} {t : State} (h5 : t.gpr .r5 = S) (hW : (⟨S, 4168⟩ : Region) ∈ t.wr) :
    ∀ k ≤ 521, WP isa (.block ((List.range k).flatMap initStep)) t fun t' =>
      (∀ i < k, t'.mem.readW (S + BitVec.ofNat 64 (8 * i)) 64 = Impl.Blowfish.initWord i) ∧
      Frame [⟨S, 4168⟩] t.mem t'.mem ∧ Keep [.r12] t t'
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega), Frame.refl _ _, Keep.refl _ _⟩
  | k + 1, hk => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (initSteps_run h5 hW k (by omega)) fun u ⟨d, f, kp⟩ => ?_
    refine WP.mono (initStep_run u (i := k) (by omega) (by rw [kp.gpr (by decide)]; exact h5)
      ⟨_, by rw [kp.2.2]; exact hW, Offset.contains_base S (by omega) (by omega)⟩)
      fun v ⟨m, kv⟩ => ⟨fun i hi => ?_, ?_, (kp.trans kv).mono (by decide)⟩
    · rw [m]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
        exact d i hi
      · exact Mem.readW_writeW_self64 _ _ _
    · rw [m]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base S (by omega) (by omega))

end VG.Proof.Blowfish.PPC64LE
