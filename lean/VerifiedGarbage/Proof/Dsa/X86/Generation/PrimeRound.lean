module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrepareExponent
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.RestoreExponent

/-! # Restore the candidate exponent and test one sampled witness -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def primeRoundControl (d : Nat) : Prop := d = primeUsed ∨ d = primeUniform ∨ d = primeIsUniform

theorem primeRound_word {base : Addr} {s t : Mem} {rs : List (Nat × Nat)} {d : Nat}
    (O : Outs base rs s t) (ends : ∀ r ∈ rs, r.1 + r.2 ≤ primeUniform)
    (hd : primeRoundControl d) : t.readW (off base d) 32 = s.readW (off base d) 32 := by
  apply BitVec.eq_of_toNat_eq
  have v := O.val32 (d := d) (k := 1) (by
    intro r hr
    have := ends r hr
    rcases hd with rfl | rfl | rfl <;> simp only [primeUniform, primeUsed, primeIsUniform] at * <;> omega)
    (by rcases hd with rfl | rfl | rfl <;> decide)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using v

theorem primeRound_ok {G : PrimeConfig} {s : State} (R : PrimeReady G s) :
    WP isa (.seq (restoreExponent G.n) (round G.n (2 * G.n))) s fun t =>
      PrimeReady G t ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent
        (wordsVal s.mem G.base (slot G.n 5) G.n)).toNat ∧
      (∀ d, primeRoundControl d → t.mem.readW (off G.base d) 32 = s.mem.readW (off G.base d) 32) ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps powerClob s t := by
  have width := G.width
  have bound : G.size ≤ 2 ^ 64 := by have := R.context.scr.nowrap; omega
  have positive : 0 < G.n := by have := G.lenMin; unfold PrimeConfig.n; omega
  refine WP.seq (WP.mono (restoreExponent_ok R.context.scr positive width G.room G.twosPos R.twos)
    fun a ⟨count, exponent, Oa, Ka⟩ => ?_)
  have Fa := primeFrame_restore (witness := G.witness.setWidth 64) (len := G.len) Oa width G.flagRoom bound
  have Ra := R.keep Fa Ka (by decide) (by decide)
  have wa : wordsVal a.mem G.base (slot G.n 5) G.n = wordsVal s.mem G.base (slot G.n 5) G.n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply Oa.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot, stride, roundCount] <;> omega
    · simp only [slot, stride]; omega
  have ca (d : Nat) := primeRound_word (d := d) Oa (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [slot, stride, roundCount, primeUniform] <;> omega)
  have room : roundStatus + 4 ≤ G.size := by have := G.flagRoom; unfold roundStatus primeIsUniform at *; omega
  refine WP.mono (round_ok Ra.context width room Ra.one Ra.r2 (by omega) (by omega)
    G.twosPos G.twosBound (by have h := G.twos32; change (Spec.Rsa.splitTwos (G.modulus - 1)).1 < 2 ^ 32 at h; omega) count (exponent.trans R.exponent) wa)
    fun t ⟨answer, Ot, Kt⟩ => ?_
  have Ft := primeFrame_round (witness := G.witness.setWidth 64) (len := G.len) Ot width G.flagRoom bound
  have ct (d : Nat) := primeRound_word (d := d) Ot (by
    intro r hr
    simp only [roundAllWrites, exponentRanges, VG.Proof.Mont.X86.Dynamic.productRanges,
      roundFinishWrites, roundWrites, VG.Proof.Dsa.X86.productRanges, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
      (((rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl) <;>
      simp only [slot, stride, roundCount, roundStatus, primeUniform] <;> omega)
  exact ⟨Ra.keep Ft Kt (by decide) (by decide), answer, fun d hd => (ct d hd).trans (ca d hd),
    Fa.trans Ft, (Ka.mono (by decide)).trans Kt⟩
end VG.Proof.Dsa.X86.Generation
