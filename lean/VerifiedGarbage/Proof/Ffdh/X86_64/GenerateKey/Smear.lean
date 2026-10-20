module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # FFDH on x86-64: the public leading-byte mask -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The three shifts spread the highest set bit to all lower positions. -/
def smear64 (b : Byte) : BitVec 64 :=
  let a := b.setWidth 64 ||| b.setWidth 64 >>> 1
  let c := a ||| a >>> 2
  c ||| c >>> 4

theorem smear64_value (b : Byte) : (smear64 b).toNat = KeyScalar.smearN b.toNat := by
  simp only [smear64, KeyScalar.smearN, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by have := b.isLt; omega)]

/-- Store the exact bit-length mask without changing the public pointers. -/
theorem smear_ok {s : State} {B : Addr} {Z : Nat} {b : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hax : s.gpr .rax = b.setWidth 64) :
    WP isa (.block smear) s fun t =>
      word t.mem B (8 * sMsk) = smear64 b ∧
      Frm B [(8 * sMsk, 8)] s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hd : 8 * sMsk + 8 ≤ Z := by unfold sMsk sFn; omega
  let m := s.mem.writeW (off B (8 * sMsk)) (smear64 b)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = m) (by
    unfold smear
    xrun [State.ea, hdr, hdi, hdrOff, hax, hs.st hd, m, smear64]) rfl)
    fun t ⟨hm, k⟩ => ?_
  refine ⟨by rw [hm]; exact word_writeW_self _ _ _ _, ?_, k⟩
  intro a ha
  rw [hm]
  exact writeW_outside (d := 8 * sMsk) s.mem B (smear64 b) (by decide) a (ha (8 * sMsk, 8) (by simp))

end VG.Proof.Ffdh.X86_64.GenerateKey
