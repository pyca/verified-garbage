module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun

/-! # Termination and exact counter results of the native witness loop -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

structure PrimeLoopInv (G : PrimeConfig) (s : State) (target : PrimeStepResult) (left used uniform : Nat) (t : State) : Prop where
  ready : PrimeReady G t
  usedBound : used ≤ G.tapeLen
  uniformBound : uniform < G.checks
  measure : left = G.tapeLen - used
  consumed : t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used
  count : t.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 uniform
  result : target = primeRun G t.mem used uniform
  frame : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem
  keeps : Keeps powerClob s t

theorem primeLoopBody_ok {G : PrimeConfig} {s : State} {used uniform : Nat} (R : PrimeReady G s)
    (used_le : used ≤ G.tapeLen) (uni_lt : uniform < G.checks)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used)
    (count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (.loop (primeStep G.len G.draw G.checks) .e) s fun t =>
      let result := primeRun G s.mem used uniform
      PrimeReady G t ∧ result.status ≠ 4 ∧
      t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status ∧
      t.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 result.uniform ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  refine WP.loop (M := isa) (fun left t => ∃ u c, PrimeLoopInv G s (primeRun G s.mem used uniform) left u c t) ?_
    (G.tapeLen - used) s ⟨used, uniform, R, used_le, uni_lt, rfl, consumed, count, rfl,
      Frame.refl _ _, Keeps.refl _ _⟩
  intro left t ⟨usedNow, uniformNow, I⟩
  have bound : uniformNow + 1 < 2 ^ 32 := by
    have h := I.uniformBound
    unfold PrimeConfig.checks Spec.Dsa.primeChecks at h
    split at h <;> omega
  refine WP.mono (primeStep_ok I.ready I.usedBound bound I.consumed I.count)
    fun u ⟨Ru, zf, status, uniformu, usedu, F, K⟩ => ?_
  let next := primeStepResult G t.mem usedNow uniformNow
  change u.zf = some (decide (next.status = 4)) at zf
  by_cases more : next.status = 4
  · have progress : usedNow < next.used ∧ next.used ≤ G.tapeLen ∧ next.uniform < G.checks := primeStepResult_continue more
    refine .inr ⟨by simp [eval, zf, more], G.tapeLen - next.used, by have := I.measure; omega,
      next.used, next.uniform, Ru, progress.2.1, progress.2.2, rfl, usedu, uniformu, ?_,
      I.frame.trans F, I.keeps.trans K⟩
    rw [primeRun_frame F, I.result]
    conv => lhs; rw [primeRun]
    exact dite_eq_left more
  · have terminal : primeRun G s.mem used uniform = next := by
      rw [I.result]
      rw [primeRun]
      exact dite_eq_right more
    refine .inl ⟨by simp [eval, zf, more], Ru, ?_, ?_, ?_, ?_, I.frame.trans F, I.keeps.trans K⟩
    · rw [terminal]; exact more
    · rw [terminal]; exact status
    · rw [terminal]; exact uniformu
    · rw [terminal]; exact usedu
end VG.Proof.Dsa.X86.Generation
