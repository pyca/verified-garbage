module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Prime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInit
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePrepared
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTapeSpec

/-! # Native prepared-candidate Miller–Rabin with exact shared-specification results -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem primeTest_ok {G : PrimeConfig} {s : State} {used : Nat} (R : PrimeInputs G s)
    (used_le : used ≤ G.tapeLen)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used) :
    WP isa (primeTest G.len) s fun t =>
      let result := primeRun G s.mem used 0
      PrimeReady G t ∧ result.status ≠ 4 ∧
      t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used ∧
      PrimeTestFrame G s.mem t.mem ∧ Keeps powerClob s t := by
  have checks : (if G.len ≤ 256 then 64 else 128) = G.checks := by
    unfold PrimeConfig.checks Spec.Dsa.primeChecks
    have h : (G.len ≤ 256) ↔ 8 * G.len ≤ 2048 := by omega
    simp only [h]
  unfold primeTest
  rw [checks]
  refine WP.seq (WP.mono (primePrepared_ok R) fun a ⟨Ra, useda, Oa, Ka⟩ => ?_)
  have Fa := primePrepare_testFrame Oa (by have := R.scratch.nowrap; omega)
  refine WP.mono (primeLoop_ok Ra used_le (useda.trans consumed))
    fun t ⟨Rt, terminal, status, _, usedt, Ft, Kt⟩ => ?_
  rw [primeRun_tape used 0 Fa.tape] at terminal status usedt
  exact ⟨Rt, terminal, status, usedt, Fa.trans Ft.testFrame, Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
