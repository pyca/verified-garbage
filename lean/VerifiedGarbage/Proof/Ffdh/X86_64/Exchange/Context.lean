module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Contract
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # FFDH exchange on x86-64: memory and lengths -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

structure ExCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  dl : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat ∨ (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat
  ol : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  yl : (stackArg s 2).toNat = (s.gpr .r8).toNat
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  hZ : 128 * (s.gpr .r8).toNat + 256 ≤ (stackArg s 4).toNat * 8
  hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8)
  dom : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdx) (exDom s)
  x : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .r9) (exX s)
  y : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (stackArg s 1) (exY s)
  ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  out : ∀ i < (s.gpr .r8).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i) 1
  sep : ∀ i < (s.gpr .r8).toNat, (stackArg s 4).toNat * 8 ≤
    ofs (stackArg s 3) (s.gpr .rdi + BitVec.ofNat 64 i)

theorem exCtx_of {s : State} (h : exPre s) : ExCtx s := by
  obtain ⟨hsp, hrd, hwr, _, _, _, dos, _, dds, dxs, dys, _, wO, wD, wX, wY, wS,
    _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hol, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hol, hyl, hxl1, hxl2, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) dxs,
    src_of_region (by rw [hrd]; simp) (by omega) dys, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 40⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
      congr 2
      omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dos (contains_byte _ (by omega) (by omega))

end VG.Proof.Ffdh.X86_64.Exchange
