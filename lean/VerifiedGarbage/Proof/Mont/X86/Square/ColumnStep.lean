module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull
public import VerifiedGarbage.Proof.Mont.X86.Square.ColumnMath
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Framework.Taint

import VerifiedGarbage.Proof.Mont.X86.Square.ColumnParts
import VerifiedGarbage.Proof.Mont.X86.Square.CarryIn
import VerifiedGarbage.Proof.Mont.X86.Square.CrossGuard

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem column_ok {s : State} {W : Addr} {L S m inv a o N k c : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hw : Ws s W L) (V : ArgVals A W N S m inv o a a)
    (lay : VG.Proof.Mont.X86.Rt.Lay L N S m inv a a) (hk : k<2*N) (hc : c≤4*N*2^32)
    (edi : PtrAt s W .edi S) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (carry : s.xmm .xmm3 = packed (BitVec.ofNat 64 c))
    (mask : s.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1))) :
    WP isa VG.Impl.Mont.X86.Rt.Square.column s fun t =>
      t.mem = (s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 (preLow s W a S m N k c))).writeW
        (off W (S+52+4*k)) (BitVec.ofNat 32 (if k<N then nextQ s W a S m inv N k c else preLow s W a S m N k c)) ∧
      t.xmm .xmm3 = packed (BitVec.ofNat 64 (nextCarry s W a S m inv N k c)) ∧
      t.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1)) ∧
      t.gpr .esi = BitVec.ofNat 32 (4*(k+1)) ∧ t.zf = some (decide (k+1=2*N)) ∧
      Keeps [.eax, .edx, .ecx, .ebp, .ebx, .esi] s t := by
  have h8 : 8*N<2^32 := by have := hw.nowrap; have := lay.scr; omega
  have n : N=2*(A 2).toNat := by have := V.n; omega
  have base : A 0 = BitVec.ofNat 32 W.toNat := by rw [← V.ws, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have av : A 7 = BitVec.ofNat 32 a := by rw [← V.a, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have mv : A 3 = BitVec.ofNat 32 m := by rw [← V.mo, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have iv : A 4 = BitVec.ofNat 32 inv := by rw [← V.inv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bounds := column_bounds s W a S m inv hk h8 hc
  apply (column_wp s _).mpr
  unfold columnCode
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨clearState s, run_clear s, ?_⟩
  have clearv := clear_values s
  have cs := clear_scalar s
  have K0 : Keeps [] s (clearState s) := ⟨fun r _ => congrArg (fun g => g r) cs.1, cs.2.2.1, cs.2.2.2⟩
  have ha0 := ha.of_keeps K0 (by simp) (by rw [cs.2.1]; exact Outs.refl _ _ _)
  have ws0 := hw.of_keeps K0
  have si0 : (clearState s).gpr .esi = BitVec.ofNat 32 (4*k) := (K0.1 _ (by simp)).trans si
  refine WP.seq (WP.mono (cross_ok ha0 ws0 lay.a_le base av n h8 hk si0 clearv.1 clearv.2.1)
    fun t1 ⟨lowC, highC, c31, c71, memC, KC⟩ => ?_)
  have mem1 : t1.mem = s.mem := memC.trans cs.2.1
  have K1 : Keeps [.eax, .edx, .ecx, .ebp] s t1 := (K0.mono (by simp)).trans KC
  have low1 : t1.xmm .xmm0 = packed (BitVec.ofNat 64 (inputLow s W a N k)) := by
    simpa only [inputLow, pairLow, diagProduct, dotProd, cs.2.1] using lowC
  have high1 : t1.xmm .xmm1 = packed (BitVec.ofNat 64 (inputHigh s W a N k)) := by
    simpa only [inputHigh, pairHigh, diagProduct, dotProd, cs.2.1] using highC
  have c1 : t1.xmm .xmm3 = packed (BitVec.ofNat 64 c) := c31.trans (clearv.2.2.1.trans carry)
  have mask1 : t1.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1)) := c71.trans (clearv.2.2.2.trans mask)
  have ha1 := ha.of_keeps K1 (by decide) (by rw [mem1]; exact Outs.refl _ _ _)
  have ws1 := hw.of_keeps K1
  have edi1 : PtrAt t1 W .edi S := by rw [PtrAt, K1.1 _ (by decide)]; exact edi
  have si1 : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (K1.1 _ (by decide)).trans si
  have cv := carry_values low1 high1 c1 mask1 bounds.2.2.2
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨carryState t1, run_carry t1, ?_⟩
  have carryS := carry_scalar t1
  have Kcarry : Keeps [] t1 (carryState t1) :=
    ⟨fun r _ => congrArg (fun g => g r) carryS.1, carryS.2.2.1, carryS.2.2.2⟩
  have ha2 := ha1.of_keeps Kcarry (by simp) (by rw [carryS.2.1]; exact Outs.refl _ _ _)
  have ws2 := ws1.of_keeps Kcarry
  have mem2 : (carryState t1).mem = s.mem := carryS.2.1.trans mem1
  have edi2 : PtrAt (carryState t1) W .edi S := by rw [PtrAt, Kcarry.1 _ (by simp)]; exact edi1
  have si2 : (carryState t1).gpr .esi = BitVec.ofNat 32 (4*k) := (Kcarry.1 _ (by simp)).trans si1
  refine WP.seq (WP.mono (reductionCode_ok ha2 ws2 lay.mo_le lay.inv_le lay.scr lay.smo lay.sinv
    base mv iv n h8 hk edi2 si2 cv.1 cv.2.1) fun t3 ⟨low3, high3, _, c73, mem3, K3⟩ => ?_)
  have low3' : t3.xmm .xmm0 = packed (BitVec.ofNat 64 (sumLow s W a S m inv N k c)) := by
    simpa only [sumLow, preLow, nextQ, redLow, dotProd, mem2] using low3
  have high3' : t3.xmm .xmm1 = packed (BitVec.ofNat 64 (sumHigh s W a S m inv N k c)) := by
    simpa only [sumHigh, preHigh, preLow, nextQ, redLow, redHigh, dotProd, mem2] using high3
  have mask3 : t3.xmm .xmm7 = packed (BitVec.ofNat 64 (2^32-1)) := c73.trans (cv.2.2.2.trans mask1)
  have mem3' : t3.mem = (s.mem.writeW (off W (S+20)) (BitVec.ofNat 64 (preLow s W a S m N k c))).writeW
      (off W (S+52+4*k)) (BitVec.ofNat 32 (if k<N then nextQ s W a S m inv N k c else preLow s W a S m N k c)) := by
    simpa only [preLow, nextQ, redLow, dotProd, mem2] using mem3
  have Kall : Keeps [.eax, .edx, .ecx, .ebp, .ebx] s t3 := (K1.mono (by decide)).trans ((Kcarry.mono (by simp)).trans K3)
  have O : Outside W S (12*N+56) s.mem t3.mem := by
    rw [mem3']
    exact ((writeW_outside _ _ _ (by have := hw.nowrap; have := lay.scr; omega)).mono (by omega) (by omega)).trans
      ((writeW32_outside _ _ _ (by have := hw.nowrap; have := lay.scr; omega)).mono (by omega) (by omega))
  have ha3 := ha.of_keeps Kall (by decide)
    (Outs.of_outside (O.mono (Nat.zero_le _) (by have := lay.scr; omega)) (List.mem_singleton_self _))
  have si3 : t3.gpr .esi = BitVec.ofNat 32 (4*k) := (Kall.1 _ (by decide)).trans si
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨carryOutState t3, run_carryOut t3, ?_⟩
  have out := carryOut_values low3' high3' bounds.1
  have outS := carryOut_scalar t3
  have Kout : Keeps [] t3 (carryOutState t3) :=
    ⟨fun r _ => congrArg (fun g => g r) outS.1, outS.2.2.1, outS.2.2.2⟩
  have ha4 := ha3.of_keeps Kout (by simp) (by rw [outS.2.1]; exact Outs.refl _ _ _)
  have si4 : (carryOutState t3).gpr .esi = BitVec.ofNat 32 (4*k) := (Kout.1 _ (by simp)).trans si3
  refine WP.mono (endCtl_ok ha4 n h8 hk si4) fun t ⟨siT, zfT, memT, KT, xT⟩ => ?_
  refine ⟨memT.trans (outS.2.1.trans mem3'), ?_, ?_, siT, zfT,
    (Kall.mono (by decide)).trans ((Kout.mono (by simp)).trans (KT.mono (by decide)))⟩
  · rw [xT, out.1]; rfl
  · rw [xT, out.2, mask3]

end VG.Proof.Mont.X86.Square
