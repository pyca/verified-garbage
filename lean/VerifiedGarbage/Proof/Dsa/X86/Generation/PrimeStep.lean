module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeDrawRound
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeControl
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTape

/-! # One terminating or continuing iteration of the witness loop -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

structure PrimeStepResult where
  status : Nat
  uniform : Nat
  used : Nat

def primeStepResult (G : PrimeConfig) (mem : Mem) (used uniform : Nat) : PrimeStepResult :=
  if used + G.draw ≤ G.tapeLen then
    let w := primeDrawValue G mem used
    let passed := Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent w.1
    ⟨primeResultStatus passed (uniform + w.2.toNat) G.checks,
      if passed then uniform + w.2.toNat else uniform, used + G.draw⟩
  else ⟨0, uniform, used⟩

theorem primeStepResult_bound (G : PrimeConfig) (mem : Mem) (used uniform : Nat) :
    (primeStepResult G mem used uniform).status < 2 ^ 32 := by
  unfold primeStepResult primeResultStatus
  split
  · dsimp only
    split
    · split <;> decide
    · decide
  · exact Nat.zero_lt_succ _

theorem primeStep_ok {G : PrimeConfig} {s : State} {used uniform : Nat} (R : PrimeReady G s)
    (used_le : used ≤ G.tapeLen) (bound : uniform + 1 < 2 ^ 32)
    (consumed : s.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 used)
    (count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (primeStep G.len G.draw G.checks) s fun t =>
      let result := primeStepResult G s.mem used uniform
      PrimeReady G t ∧ t.zf = some (decide (result.status = 4)) ∧
      t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status ∧
      t.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 result.uniform ∧
      t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  let result := primeStepResult G s.mem used uniform
  have finish {a : State} (Ra : PrimeReady G a)
      (status : a.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status)
      (cu : a.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 result.uniform)
      (useda : a.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used)
      (F : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem a.mem) (K : Keeps powerClob s a) :
      WP isa (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc primeStatus)), .alu .cmp .eax (.imm 4)]) a fun t =>
        PrimeReady G t ∧ t.zf = some (decide (result.status = 4)) ∧
        t.mem.readW (off G.base primeStatus) 32 = BitVec.ofNat 32 result.status ∧
        t.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 result.uniform ∧
        t.mem.readW (off G.base primeUsed) 32 = BitVec.ofNat 32 result.used ∧
        PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
    refine WP.mono (primeStatusTest_ok Ra (primeStepResult_bound G s.mem used uniform) status)
      fun t ⟨zf, mem, Kt⟩ => ?_
    exact ⟨Ra.unchanged mem Kt (by decide) (by decide), zf, by rw [mem, status], by rw [mem, cu],
      by rw [mem, useda], by rw [mem]; exact F, K.trans Kt⟩
  have room : primeTapeLen + 4 ≤ G.size := by have := G.flagRoom; unfold primeTapeLen primeIsUniform at *; omega
  have draw32 : G.draw < 2 ^ 32 := by have := G.width; unfold PrimeConfig.draw; omega
  unfold primeStep
  refine WP.seq (WP.mono (primeTapeCheck_ok R.context.scr room used_le G.tapeLen32 draw32 R.tapeLen consumed)
    fun a ⟨cf, mem, Ka⟩ => ?_)
  have Ra := R.unchanged mem Ka (by decide) (by decide)
  by_cases full : used + G.draw ≤ G.tapeLen
  · refine WP.seq (WP.ite false (by simp [eval, cf, show ¬ G.tapeLen - used < G.draw by omega])
      (fun e => Bool.noConfusion e) (fun _ => ?_))
    refine WP.mono (primeDrawRound_ok Ra full bound (by rw [mem, consumed]) (by rw [mem, count]))
      fun b ⟨Rb, status, uniformb, usedb, Fb, Kb⟩ => ?_
    apply finish Rb
    · simpa only [result, primeStepResult, full, ite_true, mem] using status
    · simpa only [result, primeStepResult, full, ite_true, mem] using uniformb
    · simpa only [result, primeStepResult, full, ite_true] using usedb
    · rw [← mem]; exact Fb
    · exact (Ka.mono (by decide)).trans Kb
  · refine WP.seq (WP.ite true (by simp [eval, cf, show G.tapeLen - used < G.draw by omega])
      (fun _ => ?_) (fun e => Bool.noConfusion e))
    refine WP.mono (primeMarkReady_ok Ra 0) fun b ⟨Rb, status, uniformb, usedb, Fb, Kb⟩ => ?_
    apply finish Rb
    · simpa only [result, primeStepResult, full, ite_false] using status
    · simpa only [result, primeStepResult, full, ite_false] using uniformb.trans (mem ▸ count)
    · simpa only [result, primeStepResult, full, ite_false] using usedb.trans (mem ▸ consumed)
    · rw [← mem]; exact Fb
    · exact (Ka.mono (by decide)).trans Kb
end VG.Proof.Dsa.X86.Generation
