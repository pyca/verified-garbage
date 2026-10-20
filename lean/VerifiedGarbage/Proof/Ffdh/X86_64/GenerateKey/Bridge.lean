module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # FFDH key generation on x86-64: reuse the exchange output workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only the outer header's public-value and output pointers change. -/
theorem bridge_ok {s : State} {B yp gp : Addr} {Z o w : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w w mi)
    (hY : word s.mem B (8 * sY) = yp) (hG : word s.mem B (8 * sG) = gp) :
    WP isa (.block bridge) s fun t =>
      word t.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut) = yp ∧
      word t.mem B (8 * sY) = gp ∧
      Frm B [(8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8), (8 * sY, 8)] s.mem t.mem ∧
      Keep [.rax, .rdx] s t := by
  have hZ : 256 ≤ Z := by have := hc.lo; have := hc.hi; unfold slot hdrBytes at *; omega
  have hs := hc.scr
  have hldY := hs.ld (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hstO := hs.st (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) (by change 184 ≤ Z; omega)
  have hstY := hs.st (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hldG := hs.ld (d := 8 * sG) (by change 224 ≤ Z; omega)
  let m₁ := s.mem.writeW (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut)) yp
  let m := m₁.writeW (off B (8 * sY)) gp
  have ho := writeW_outside (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) s.mem B yp (by decide)
  have hy := writeW_outside (d := 8 * sY) m₁ B gp (by decide)
  have hG' : word m₁ B (8 * sG) = gp := by
    rw [ho.word (by decide) (by decide)]
    exact hG
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = m) (by
    unfold bridge
    xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc.rdi, hdrOff, hc.good.scr.ld (hdr_lt_slot w 8 (show VG.Impl.Rsa.X86_64.Crt.sLink < 32 by decide)),
      hc.link, hldY, hY, hstO, hldG, hG', hstY, m, m₁]) rfl) fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, ?_, ?_, k⟩
  · rw [hm, hy.word (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro a ha
    rw [hm]
    exact (hy a (ha (8 * sY, 8) (by simp))).trans
      (ho a (ha (8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8) (by simp)))

end VG.Proof.Ffdh.X86_64.GenerateKey
