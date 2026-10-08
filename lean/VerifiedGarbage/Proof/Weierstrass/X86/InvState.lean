import VerifiedGarbage.Impl.Weierstrass.X86.InvCfg
import VerifiedGarbage.Proof.Divstep.Alg32Def
import VerifiedGarbage.Proof.Mont.X86.Ops
import VerifiedGarbage.Proof.Weierstrass.X86.MontCall

/-! # Memory layout and state of the 256-bit divstep inversion -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.Impl.Weierstrass.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure WorkLay (P : InvCfg) (size : Nat) : Prop where
  n4 : P.M.n = 4
  tbl_bound : P.tbl + 320 ≤ size
  mod_bound : P.M.mo + 32 ≤ size
  tmp_bound : P.M.tmp + 32 ≤ size
  tbl_mod : P.tbl + 320 ≤ P.M.mo ∨ P.M.mo + 32 ≤ P.tbl
  tbl_tmp : P.tbl + 320 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.tbl
  mod_tmp : P.M.mo + 32 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.M.mo

structure InvLay (P : InvCfg) (size : Nat) : Prop extends WorkLay P size where
  base_bound : P.base + 32 ≤ size
  base_tbl : P.base + 32 ≤ P.tbl ∨ P.tbl + 320 ≤ P.base
  out_bound : P.out + 32 ≤ size
  out_tmp : P.out + 32 ≤ P.M.tmp ∨ P.M.tmp + 32 ≤ P.out
  size_eq : size = 8192
  tbl_own : P.tbl + 320 ≤ Mont.own 4
  out_own : P.out + 32 ≤ Mont.own 4

structure StateAt (P : InvCfg) (base : Addr) (I : Divstep.W32.IState) (s : State) : Prop where
  d : s.mem.readW (off base P.sW) 32 = BitVec.ofInt 32 I.d
  f : (val32 s.mem base P.sF 9 : Int) % 2 ^ 288 = I.f % 2 ^ 288
  g : (val32 s.mem base P.sG 9 : Int) % 2 ^ 288 = I.g % 2 ^ 288
  a : (val32 s.mem base P.sA 8 : Int) = I.a
  b : (val32 s.mem base P.sB 8 : Int) = I.b

structure MatrixAt (P : InvCfg) (base : Addr) (T : Divstep.MSt) (s : State) : Prop where
  d : s.mem.readW (off base P.sW) 32 = BitVec.ofInt 32 T.d
  u : s.mem.readW (off base (P.sW + 12)) 32 = BitVec.ofInt 32 T.u
  v : s.mem.readW (off base (P.sW + 16)) 32 = BitVec.ofInt 32 T.v
  q : s.mem.readW (off base (P.sW + 20)) 32 = BitVec.ofInt 32 T.q
  r : s.mem.readW (off base (P.sW + 24)) 32 = BitVec.ofInt 32 T.r

/-- The mathematical bounds and exact divisions required by one batch. -/
structure BatchFacts (I : Divstep.W32.IState) (p : Nat) : Prop where
  delta : |I.d| + 64 < 2 ^ 30
  odd : I.f % 2 = 1
  f : |I.f| ≤ p
  g : |I.g| ≤ p
  a : |I.a| ≤ p
  b : |I.b| ≤ p
  matrix : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
    |T.u| + |T.v| ≤ 2 ^ 30 ∧ |T.q| + |T.r| ≤ 2 ^ 30
  division : let T := Divstep.msteps 30 (Divstep.MSt.init I.d I.f I.g)
    2 ^ 30 ∣ T.u * I.f + T.v * I.g ∧ 2 ^ 30 ∣ T.q * I.f + T.r * I.g

end VG.Proof.Weierstrass.X86.Inv
