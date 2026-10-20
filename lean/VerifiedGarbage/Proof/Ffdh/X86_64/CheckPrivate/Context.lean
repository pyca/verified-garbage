module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! # FFDH private-key validation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure KpCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .rdx).toNat
  k2 : (s.gpr .rdx).toNat ≤ 1024
  dl : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat ∨ (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat
  yl : (s.gpr .r8).toNat = (s.gpr .rdx).toNat
  hZ : 128 * (s.gpr .rdx).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (kpDom s)
  y : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rcx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .rdx).toNat
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (kpX s)
  ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8

theorem kpCtx_of {s : State} (h : kpPre s) : KpCtx s := by
  obtain ⟨hsp, hrd, hwr, dds, dys, dxs, _, wD, wY, wX, wS,
    _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hyl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) dys, hxl1, hxl2,
    src_of_region (by rw [hrd]; simp) (by omega) dxs, ?_⟩
  intro i hi
  refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
  rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega]
  exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Ffdh.X86_64.CheckPrivate
