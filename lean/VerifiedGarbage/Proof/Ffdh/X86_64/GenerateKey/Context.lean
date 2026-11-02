module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # FFDH key-generation attempts on x86-64: inputs and disjoint outputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

structure GkCtx (s : State) : Prop where
  k1 : 64 ≤ (stackArg s 0).toNat
  k2 : (stackArg s 0).toNat ≤ 1024
  dl : (s.gpr .r9).toNat = 2 * (stackArg s 0).toNat ∨ (s.gpr .r9).toNat = 3 * (stackArg s 0).toNat
  xl : (s.gpr .rsi).toNat = (stackArg s 0).toNat
  yl : (s.gpr .rcx).toNat = (stackArg s 0).toNat
  rl : (stackArg s 2).toNat = (stackArg s 0).toNat
  hZ : 128 * (stackArg s 0).toNat + 256 ≤ (stackArg s 4).toNat * 8
  hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8)
  dom : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .r8) (gkDom s)
  rand : Src s (stackArg s 3) ((stackArg s 4).toNat * 8) (stackArg s 1) (gkRand s)
  ha : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8
  x : OutOk s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdi) (stackArg s 0).toNat
  y : OutOk s (stackArg s 3) ((stackArg s 4).toNat * 8) (s.gpr .rdx) (stackArg s 0).toNat
  xy : Apart (s.gpr .rdi) (stackArg s 0).toNat (s.gpr .rdx) (stackArg s 0).toNat
  xd : Apart (s.gpr .rdi) (stackArg s 0).toNat (s.gpr .r8) (s.gpr .r9).toNat
  xr : Apart (s.gpr .rdi) (stackArg s 0).toNat (stackArg s 1) (stackArg s 0).toNat
  yd : Apart (s.gpr .rdx) (stackArg s 0).toNat (s.gpr .r8) (s.gpr .r9).toNat
  yr : Apart (s.gpr .rdx) (stackArg s 0).toNat (stackArg s 1) (stackArg s 0).toNat

theorem gkCtx_of {s : State} (h : gkPre s) : GkCtx s := by
  obtain ⟨_, hrd, hwr, dxy, dxd, dxr, dxs, _, dyd, dyr, dys, _, dds, drs, _,
    wX, wY, wD, wR, wS, _, _, _, _, _, _, ⟨hk1, hk2⟩, hdl, hxl, hyl, hrl, hsl⟩ := h
  unfold Spec.Rsa.scratchWords at hsl
  refine ⟨hk1, hk2, hdl, hxl, hyl, hrl, by omega, Scr.of_mem (by rw [hwr]; simp) wS,
    src_of_region (by rw [hrd]; simp) (by omega) dds,
    src_of_region (by rw [hrd]; simp) (by omega) drs, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨⟨stackArgAddr s 0, 40⟩, by rw [hrd]; simp, ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dxs (contains_byte _ (by omega) (by omega))
  · intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, by simp, contains_byte _ (by omega) (by omega)⟩
  · intro i hi
    exact out_scr dys (contains_byte _ (by omega) (by omega))
  · simpa only [hxl, hyl] using (apart_of dxy (by omega) (by omega))
  · simpa only [hxl] using (apart_of dxd (by omega) (by omega))
  · simpa only [hxl, hrl] using (apart_of dxr (by omega) (by omega))
  · simpa only [hyl] using (apart_of dyd (by omega) (by omega))
  · simpa only [hyl, hrl] using (apart_of dyr (by omega) (by omega))

end VG.Proof.Ffdh.X86_64.GenerateKey
