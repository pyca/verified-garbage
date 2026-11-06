module

public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset

/-! # Stable resources for all eighteen private CRT arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.Crt VG.Proof.Dsa.X86

def componentArguments : List Nat := [2, 4, 6, 8, 10, 12, 14]

structure Inputs (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  scratch : Scr s base bytes
  lower : 64 ≤ len
  upper : len ≤ 1024
  space : size (Spec.Rsa.modulusWords len) ≤ bytes
  stack : ∀ i, i < 18 → CallArgument s base bytes i (args i)
  outLen : args 1 = BitVec.ofNat 32 len
  nLen : args 3 = BitVec.ofNat 32 len
  inLen : args 5 = BitVec.ofNat 32 len
  pShort : (args 7).toNat < len
  qShort : (args 9).toNat < len
  dpLen : args 11 = args 7
  dqLen : args 13 = args 9
  qiLen : args 15 = args 7
  outFit : (args 0).toNat + len ≤ 2 ^ 32
  outWrite : InRegions s.wr (byteAddr (args 0)) len
  outApart : Region.Disjoint ⟨base, bytes⟩ ⟨byteAddr (args 0), len⟩
  positive : ∀ i ∈ componentArguments, 0 < (args (i + 1)).toNat
  bounded : ∀ i ∈ componentArguments, (args (i + 1)).toNat ≤ len
  fits : ∀ i ∈ componentArguments, (args i).toNat + (args (i + 1)).toNat ≤ 2 ^ 32
  readable : ∀ i ∈ componentArguments,
    InRegions (s.rd ++ s.wr) (byteAddr (args i)) (args (i + 1)).toNat
  apart : ∀ i ∈ componentArguments,
    Region.Disjoint ⟨byteAddr (args i), (args (i + 1)).toNat⟩ ⟨base, bytes⟩
  room : VG.Proof.Mont.X86.CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32

end VG.Proof.Bignum.X86.Crt
