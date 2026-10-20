module

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedWidth
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedFn
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.WordsFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicControls
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Public width selection retains all input buffers and caller resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem precomputedValidSetup_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (H : PrecomputedInputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.saveExponent) (.block PrecomputedFn.widthArgs)) s fun t =>
      PrecomputedInputs base bytes len args t ∧ t.gpr .esp = s.gpr .esp ∧
      t.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.modulusWords len) ∧
      Spec.Rsa.wordsAt t.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) =
        Spec.Rsa.wordsAt s.mem (byteAddr (args 2)) (2 * Spec.Rsa.modulusWords len) ∧
      val32 t.mem base 128 2 = (s.gpr .ebx).toNat + 2 ^ 32 * (s.gpr .edx).toNat := by
  have size := H.space
  rw [PublicContext.size_eq] at size
  refine WP.seq (WP.mono (saveExponent_value H.scratch (by omega)) fun u ⟨X, O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have Hu := H.keep K (by decide) (by decide) O'
  refine WP.mono (precomputedWidth_ok H.upper (by rw [← H.outLen]; exact (Hu.stack 1 (by decide)).readSrc))
    fun t ⟨W, M, Kt⟩ => ?_
  have Kst := (K.mono (by simp : ([] : List Reg) ⊆ [.eax])).trans Kt
  have Ost : Outside base 0 bytes s.mem t.mem := by rw [M]; exact O'
  exact ⟨H.keep Kst (by decide) (by decide) Ost, Kst.1 _ (by decide), W,
    scratch_words Ost (by have := H.scratch.nowrap; omega) (by have := H.upper; simp only [Spec.Rsa.modulusWords]; omega) (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords len) = 16 * Spec.Rsa.modulusWords len by omega] using H.preApart),
    by rw [M]; exact X⟩

end VG.Proof.Bignum.X86
