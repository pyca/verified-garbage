module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessLower
public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrScan
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessLowerFinish
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The complete native witness scan detects exactly the lower bound two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessLower
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.WitnessLower

theorem code_ok {s : State} {base : Addr} {size n src : Nat} (scratch : Scr s base size)
    (positive : 2 ≤ n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      t.gpr .ebx = cmask (decide (2 ≤ val32 s.mem base src n)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ebp, .edx] s t := by
  refine WP.seq (WP.mono (OrScan.code_ok scratch (by omega_arith) (by omega_arith)) fun a ⟨Z, M, K⟩ => ?_)
  refine WP.mono (finish_ok (scratch.of_keeps K (by decide)) (by omega_arith) Z) fun t ⟨V, Mt, Kt⟩ => ?_
  rw [M] at V
  have compare : (¬(val32 s.mem base (src + 4) (n - 1) = 0 ∧ w32 s.mem base src < 2)) ↔
      2 ≤ val32 s.mem base src n := by
    rw [← below_two _ _ _ _ (by omega_arith)]
    omega_arith
  rw [decide_eq_decide.mpr compare] at V
  exact ⟨V, Mt.trans M, (K.mono (by decide)).widen Kt⟩

end VG.Proof.RsaKeyGen.X86.WitnessLower
