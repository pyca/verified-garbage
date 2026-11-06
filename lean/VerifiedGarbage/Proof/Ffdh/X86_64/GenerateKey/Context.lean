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

end VG.Proof.Ffdh.X86_64.GenerateKey
