module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombInputs
public import VerifiedGarbage.Proof.Weierstrass.CombDigitW
public import VerifiedGarbage.Proof.Weierstrass.Env

/-! Side conditions for a fixed-base comb, independent of its input scalar. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open Spec.Weierstrass

structure Config (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat)))
    (start : Nat × Nat) : Prop where
  layout : Layout K
  fieldK : K.F.k=K.L.M.n
  fieldM : K.F.m=C.p
  modulus : VG.Proof.Weierstrass.Arm.Mont.ModOk K.L.M.n C.p
  unit : UnitMod C.p (2^(64*K.L.M.n))
  tables : CombOkW C K.w K.J tbl start
  one_lt : K.one<C.p
  one : toM C.p (2^(64*K.L.M.n)) K.one=1
  startX : K.start.1=start.1*2^(64*K.L.M.n)%C.p
  startY : K.start.2=start.2*2^(64*K.L.M.n)%C.p
  w1 : 1≤K.w
  w9 : K.w<9
  J1 : 1≤K.J
  J32 : K.J<2^32
  startBits : K.w*(K.J-1)≤K.L.nbits
  coverBits : K.L.nbits≤K.w*K.J
  bitsLow : 4096≤K.L.bits
  bitsHigh : K.L.bits+K.L.nbits≤8192
  bitsFit : K.L.bits<8192
  windowFit : K.L.bits%4096+K.w≤4096
  encJ : encodable (BitVec.ofNat 32 K.J)=true
  encLast : encodable (BitVec.ofNat 32 (K.J-1))=true
  encRow : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true
  encEntry : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true
  encH : encodable (BitVec.ofNat 32 (K.H+1))=true

def tableWords (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : List (BitVec 64) :=
  tcombWords K.L.M.n (2^(64*K.L.M.n)) C.p tbl

abbrev CurveInputs (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat)))
    (base T : Addr) (k : Nat) (s : State) : Prop :=
  Inputs K base T (tableWords K C tbl) k (C.a*2^(64*K.L.M.n)%C.p)
    ((3*C.b)*2^(64*K.L.M.n)%C.p) s

theorem Config.magnitude {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))}
    {start : Nat × Nat} (h : Config K C tbl start) (k j : Nat) :
    magH K.H (combWin K.w k j)≤K.H := by
  apply magH_le
  have pow : 2^K.w=2*K.H := by
    change 2^K.w=2*2^(K.w-1)
    calc
      2^K.w=2^((K.w-1)+1) := congrArg (fun n => 2^n) (by have := h.w1; omega)
      _ = 2*2^(K.w-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [← pow]
  exact combWin_lt _ _ _

theorem Config.halfBound {K : TCombCfg} {C : Curve} {tbl : List (List (Nat × Nat))}
    {start : Nat × Nat} (h : Config K C tbl start) : K.H+1<2^31 := by
  have hw := h.w9
  have bound : K.H≤2^8 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end VG.Proof.Weierstrass.Arm.TComb
