module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeResult
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects

/-! # The result decision preserves the candidate context and consumed-byte count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation VG.Proof.Ecdsa.X86

theorem primeResultReady_ok {G : PrimeConfig} {s : State} {uniform : Nat} {isUniform passed : Bool}
    (R : PrimeReady G s) (bound : uniform + 1 < 2 ^ 32)
    (answer : s.gpr .eax = BitVec.ofNat 32 passed.toNat)
    (flag : s.mem.readW (off G.base primeIsUniform) 32 = mask32 (isUniform = true))
    (count : s.mem.readW (off G.base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (primeRoundResult G.checks) s fun t => PrimeReady G t ∧
      t.mem.readW (off G.base primeStatus) 32 =
        BitVec.ofNat 32 (primeResultStatus passed (uniform + isUniform.toNat) G.checks) ∧
      t.mem.readW (off G.base primeUniform) 32 =
        BitVec.ofNat 32 (if passed then uniform + isUniform.toNat else uniform) ∧
      t.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  have checks32 : G.checks < 2 ^ 32 := by unfold PrimeConfig.checks Spec.Dsa.primeChecks; split <;> decide
  refine WP.mono (primeRoundResult_ok R.context.scr G.flagRoom bound checks32 answer flag count)
    fun t ⟨status, uniform, O, K⟩ => ?_
  have F : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem :=
    primeFrame_local O (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [primeWrites]) G.width G.flagRoom (by have := R.context.scr.nowrap; omega)
  refine ⟨R.keep F K (by decide) (by decide), status, uniform, ?_, F, K⟩
  apply BitVec.eq_of_toNat_eq
  have v := O.val32 (d := primeUsed) (k := 1) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide) (by decide)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using v
end VG.Proof.Dsa.X86.Generation
