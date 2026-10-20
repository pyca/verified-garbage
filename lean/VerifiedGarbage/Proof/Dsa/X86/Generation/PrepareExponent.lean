module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.Factor
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundMinus
import VerifiedGarbage.Proof.Rsa.X86.DivCopy

/-! # Prepare and save the exact odd part of the candidate's predecessor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Spec.Rsa

def prepareWrites (n : Nat) : List (Nat × Nat) := [(slot n 8, 8 * n), (primeTwos, 4), (primeExponent, 8 * n)]

theorem prepareExponent_ok {s : State} {base : Addr} {size n m : Nat}
    (C : Context n m base size s) (width : n ≤ 48) (room : primeExponent + 8 * n ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1) (odd : m % 2 = 1) :
    WP isa (prepareExponent n) s fun t =>
      t.mem.readW (off base primeTwos) 32 = BitVec.ofNat 32 (splitTwos (m - 1)).1 ∧
      val32 t.mem base primeExponent (2 * n) = (splitTwos (m - 1)).2 ∧
      Outs base (prepareWrites n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have hn : 0 < n := C.modulus.n0
  have gt := C.gt_one
  have far : slot n 8 + 8 * n ≤ primeTwos := by simp only [slot, stride, primeTwos]; omega
  have cr : primeTwos + 4 ≤ size := by unfold primeTwos primeExponent at *; omega
  have er : slot n 8 + 8 * n ≤ size := by omega
  unfold prepareExponent
  refine WP.seq (WP.mono (roundMinusOne_ok C one) fun a ⟨Ca, va, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (factor_ok (original := m - 1) Ca.scr hn width er cr (by omega) (by omega)
    (by rw [← wordsVal_eq_val32, va])) fun b ⟨count, exponent, Ob, Kb⟩ => ?_)
  have Kpre : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
  refine WP.mono (VG.Proof.Rsa.X86.Div.copyWords_ok (C.scr.of_keeps Kpre (by decide))
    (by omega) (by omega) (by omega) (.inr (.inr (by unfold primeExponent primeTwos at *; omega))))
    fun t ⟨Ot, value, Kt⟩ => ?_
  refine ⟨?_, value.trans exponent, ?_, Kpre.trans (Kt.mono (by decide))⟩
  · have same : t.mem.readW (off base primeTwos) 32 = b.mem.readW (off base primeTwos) 32 := by
      apply BitVec.eq_of_toNat_eq
      exact Ot.w32 (by unfold primeTwos primeExponent; omega) (by decide)
    exact same.trans count
  · have Oa' : Outs base (prepareWrites n) s.mem a.mem := Outs.of_outside Oa (by simp [prepareWrites])
    have Ob' : Outs base (prepareWrites n) a.mem b.mem := Ob.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [prepareWrites])
    have Ot' : Outside base primeExponent (8 * n) b.mem t.mem := by
      simpa only [show 4 * (2 * n) = 8 * n by omega] using Ot
    exact (Oa'.trans Ob').trans (Outs.of_outside Ot' (by simp [prepareWrites]))
end VG.Proof.Dsa.X86.Generation
