module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorEvaluate
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Mont.X86.ExponentBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorExponent
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPower

/-! # Load the saved quotient and test the resulting generator -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

theorem generatorEvaluate_ok {s : State} {base : Addr} {size n p len : Nat}
    (C : Context n p base size s) (width : n ≤ 48) (ndef : n = (len + 7) / 8)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2 ^ (128 * n) % p)
    (h4 : 4 ≤ len) (hw4 : len % 4 = 0)
    (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (read : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 4)
    (apart : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (generatorEvaluate len) s fun t =>
      let value := wordsVal s.mem base (slot n 5) n ^
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((s.gpr .esi).setWidth 64) len) % p
      Context n p base size t ∧ wordsVal t.mem base (slot n 6) n = value ∧
      t.gpr .eax = (if 1 < value then 1 else 3) ∧
      Outs base ((slot n 8, 8 * n) :: (exponentRanges n (2 * n) ++ [(slot n 7, 8 * n)])) s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold generatorEvaluate
  dsimp only
  rw [← ndef]
  refine WP.seq (WP.mono (generatorExponent_ok C h4 (by omega) hw4 fit read apart)
    fun a ⟨Ca, exponent, saved, Oa, Ka⟩ => ?_)
  refine WP.mono (generatorPower_ok Ca width ((saved 3 (by decide)).trans one) ((saved 4 (by decide)).trans r2))
    fun t ⟨Ct, result, status, Ot, Kt⟩ => ?_
  rw [saved 5 (by decide), exponent] at result status
  exact ⟨Ct, result, status, (Outs.of_outside Oa (by simp)).trans
    (Ot.mono (by intro r hr; exact List.mem_cons_of_mem _ hr)), (Ka.mono (by decide)).trans Kt⟩
end VG.Proof.Dsa.X86.Generation
