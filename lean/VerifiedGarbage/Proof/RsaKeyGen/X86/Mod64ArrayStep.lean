module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayAdvance
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayMath
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Word

/-! # Each array iteration extends the modular prefix and updates public control -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.step {g : ArrayGeometry} (v : g.Valid) {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) (index : i < g.n) :
    WP isa (arrayStep g.exponent) s fun t =>
      ArrayState g candidate exponent (i + 1) t ∧ t.zf = some (decide (i + 1 = g.n)) ∧
      Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold arrayStep
  refine WP.seq (WP.mono (S.loadWord v index) fun a ⟨A, inputWord, Ma, Ka⟩ => ?_)
  refine WP.seq (WP.mono (word_ok A.context.scratch v.exponentFit
    (by rw [A.context.exponentEq]; exact A.bound)) fun b ⟨value, bound, _, Mb, Kb⟩ => ?_)
  have Cb := A.context.keepReadonly Kb (by decide) (by decide) Mb
  rw [A.context.exponentEq, A.value, inputWord,
    show g.n - i = (g.n - 1 - i) + 1 by omega, high_mod_step] at value
  rw [A.context.exponentEq] at bound
  have Pb : b.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.pointer i := by rw [Mb]; exact A.pointer
  have Nb : b.mem.readW (off (g.sp.setWidth 64) 4) 32 = BitVec.ofNat 32 (g.n - i) := by rw [Mb]; exact A.count
  have countBound : g.n - i < 2 ^ 32 := by have := v.sourceFit; have := Cb.scratch.nowrap; omega
  refine WP.mono (advance_ok v Cb (by omega) countBound Pb Nb) fun t ⟨Ct, P, N, Z, O, K⟩ => ?_
  refine ⟨⟨Ct, P, ?_, ?_, ?_⟩, ?_, ?_, ((Ka.mono (by decide)).trans Kb).widen K⟩
  · rw [show g.n - i - 1 = g.n - (i + 1) by omega] at N
    exact N
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide), value,
      show g.n - 1 - i = g.n - (i + 1) by omega]
  · rw [K.1 .ecx (by decide), K.1 .ebx (by decide)]
    exact bound
  · simpa only [show g.n - i - 1 = 0 ↔ i + 1 = g.n by omega] using Z
  · rw [Mb, Ma] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Mod64
