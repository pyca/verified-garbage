module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CountInit
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyReady
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Compose native initialization and the exact factor-of-two loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Arm.Keys (num opRegs)
open VG.Spec.Rsa (splitTwos)

theorem expDecompose_ok {s : State} {base : BitVec 32} {capacity w n : Nat}
    (workspace : Workspace s base (8 * capacity)) (ready : KeyReady base capacity w s)
    (data : MontData base capacity w s.mem) (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (number : num s.mem (base + 96#32) (2 * w + 2) 0 = n) (large : 1 < n) (odd : n % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose s fun t =>
      KeyReady base capacity w t ∧ MontData base capacity w t.mem ∧
      num t.mem (base + 96#32) (2 * w + 2) 29 = (splitTwos (n - 1)).2 ∧
      t.mem.readW (State.addr (t.sp + 60#32)) 32 = BitVec.ofNat 32 (splitTwos (n - 1)).1 ∧
      (∀ j, j < 30 → j ≠ 29 → num t.mem (base + 96#32) (2 * w + 2) j =
        num s.mem (base + 96#32) (2 * w + 2) j) ∧
      (∀ d, d + 8 ≤ 256 → t.mem.readW (off (State.addr base) d) 64 =
        s.mem.readW (off (State.addr base) d) 64) ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩] s.mem t.mem ∧ Rest opRegs s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.expDecompose, WP.seq_iff]
  refine WP.mono (expCountInit_ok workspace ready data stack separate number large odd) ?_
  intro u h
  refine WP.mono (halfCountLoop_ok h.workspace h.ready h.data h.stack h.separate h.number h.positive h.even h.saved) ?_
  rintro t ⟨readyT, dataT, valueT, countT, arraysT, headerT, frameT, restT⟩
  rw [h.rest.sp] at frameT
  exact ⟨readyT, dataT, valueT, countT,
    fun j bound different => (arraysT j bound different).trans (h.arrays j bound different),
    fun d bound => (headerT d bound).trans (h.header d bound), h.frame.trans frameT, h.rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
