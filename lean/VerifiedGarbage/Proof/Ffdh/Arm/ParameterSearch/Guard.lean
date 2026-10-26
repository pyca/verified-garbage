module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CounterMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Counter
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Packed
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import Mathlib.Util.CompileInductive

/-! Exhaustion tests both native halves of the attempt counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Controller lowWord)
open VG.Proof.X25519.Arm (Rest)

theorem guard_ok (s : State) {base : BitVec 32} {n : Nat} (h : Controller base s)
    (bound : n ≤ 2 ^ 32) (counter : s.mem.readW (State.addr base) 64 = BitVec.ofNat 64 n) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 0, .ldr .r10 .r4 4] ++
      VG.Impl.Ffdh.Arm.ParameterSearch.budgetGuard)) s fun t =>
      (t.z = decide (n = 0) ∧ t.mem = s.mem) ∧ Rest [.r9, .r10] s t := by
  have fits : n < 2 ^ 64 := by omega
  have lo := packedLow s.mem base 0 n fits (by simpa [off] using counter)
  have hi := packedHigh s.mem base 0 n fits (by simpa [off] using counter)
  rw [WP.block_append_iff]
  refine WP.mono (counterLoads_ok s h) ?_
  rintro u ⟨⟨lowU, highU, memU⟩, restU⟩
  refine WP.mono (budgetGuard_ok u bound (lowU.trans lo) (highU.trans hi)) ?_
  rintro t ⟨⟨zero, memT⟩, restT⟩
  exact ⟨⟨zero, memT.trans memU⟩, restU.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
