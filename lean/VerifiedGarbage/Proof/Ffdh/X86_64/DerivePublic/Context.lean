module

public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Rsa.X86_64.CvCode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH public-value derivation on x86-64: input context -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.DerivePublic

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure DvCtx (s : State) : Prop where
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  dl : (s.gpr .rcx).toNat = 2 * (s.gpr .r8).toNat ∨ (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat
  yl : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  hZ : 128 * (s.gpr .r8).toNat + 256 ≤ (stackArg s 2).toNat * 8
  hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8)
  dom : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdx) (dvDom s)
  xl1 : 1 ≤ (stackArg s 0).toNat
  xl2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  x : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .r9) (dvX s)
  y : OutOk s (stackArg s 1) ((stackArg s 2).toNat * 8) (s.gpr .rdi) (s.gpr .r8).toNat
  yd : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .rdx) (s.gpr .rcx).toNat
  yx : Apart (s.gpr .rdi) (s.gpr .r8).toNat (s.gpr .r9) (stackArg s 0).toNat
  ha : ∀ i < 3, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8

theorem dvCtx_of {s : State} (h : dvPre s) : DvCtx s := by
  obtain ⟨_, hrd, hwr, dyd, dyx, dys, _, dds, dxs, _, wY, wD, wX, wS,
    _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hyl, hxl1, hxl2, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hyl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds, hxl1, hxl2,
    src_of_region (by rw [hrd]; simp) (by omega) dxs, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyd (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyx (by omega) (by omega))
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 24⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
      congr 2
      omega]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Ffdh.X86_64.DerivePublic
