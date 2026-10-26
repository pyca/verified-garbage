module
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH on x86-64: retain the scalar's significant slice -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem cutFinish_ok {s : State} {B xp : Addr} {Z ld n : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 256 ≤ Z)
    (hX : word s.mem B (8 * sX) = xp) (hN : word s.mem B (8 * sEl) = BitVec.ofNat 64 n)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 ld) :
    WP isa (.block cutFinish) s fun t =>
      word t.mem B (8 * sX) = off xp ld ∧ word t.mem B (8 * sXl) = BitVec.ofNat 64 n ∧
      Frm B [(8 * sX, 8), (8 * sXl, 8)] s.mem t.mem ∧ Keep [.rax] s t := by
  let m₁ := s.mem.writeW (off B (8 * sX)) (off xp ld)
  let m := m₁.writeW (off B (8 * sXl)) (BitVec.ofNat 64 n)
  have ox := writeW_outside (d := 8 * sX) s.mem B (off xp ld) (by decide)
  have on := writeW_outside (d := 8 * sXl) m₁ B (BitVec.ofNat 64 n) (by decide)
  have hN' : word m₁ B (8 * sEl) = BitVec.ofNat 64 n := by
    rw [ox.word (by decide) (by decide)]
    exact hN
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = m) (by
    unfold cutFinish
    xrun [State.ea, hdr, hdi, hdrOff, h8, hX, hN',
      hs.ld (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.st (d := 8 * sX) (by change 168 ≤ Z; omega),
      hs.ld (d := 8 * sEl) (by change 200 ≤ Z; omega),
      hs.st (d := 8 * sXl) (by change 176 ≤ Z; omega), m, m₁, off]) rfl)
    fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, ?_, ?_, k⟩
  · rw [hm, on.word (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro a ha
    rw [hm]
    exact (on a (ha (8 * sXl, 8) (by simp))).trans (ox a (ha (8 * sX, 8) (by simp)))

end VG.Proof.Ffdh.X86_64.GenerateKey
