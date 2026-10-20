module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # FFDH public-key validation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure CpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  yl : (s.gpr .r8).toNat = (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (scrLen s).toNat * 8
  hs : Scr s (s.gpr .r9) ((scrLen s).toNat * 8)
  dom : Src s (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rdi) (cpDom s)
  y : Src s (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rcx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)

theorem cpCtx_of {s : State} (h : cpPre s) : CpCtx s := by
  obtain ⟨_, hrd, hwr, dds, dys, _, _, _, _, _, wD, wY, wS, ⟨hk1, hk2⟩, hdl, hyl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  exact ⟨hk1, hk2, hdl, hyl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds, src_of_region (by rw [hrd]; simp) (by omega) dys⟩

end VG.Proof.Ffdh.X86_64.CheckPublic
