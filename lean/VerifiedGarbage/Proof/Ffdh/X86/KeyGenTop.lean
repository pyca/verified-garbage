module

public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
public import VerifiedGarbage.Proof.Ffdh.X86.Ops

/-! # `vg_ffdh_generate_key` on i686 against its contract: the key pair -/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeyGen

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In safeM safeM_of)
open VG.Proof.Ffdh.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)

/-- The outputs. -/
abbrev xR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat⟩
abbrev yR (s : State) : Region := ⟨argumentPointer s 2, (arg s 3).toNat⟩

/-- The inputs and the outputs, as the synthetic arguments give them. -/
structure Geo (args : Nat → BitVec 32) (base : Addr) (bytes len dlen : Nat) (sp : BitVec 32) (rd wr : List Region) :
    Prop where
  dom : DomGeo args base bytes len dlen rd wr
  dom40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96)
  cut : KeyCut.CutGeo base bytes len (args 10) (args 0) sp rd wr
  rWs : Region.Disjoint ⟨byteAddr (args 10), len⟩ ⟨base, bytes⟩
  r40 : Region.Disjoint ⟨byteAddr (args 10), len⟩ (below sp 96)
  domX : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ ⟨byteAddr (args 0), len⟩
  ox : OutAt args base bytes len 0 sp wr
  oy : OutAt args base bytes len 8 sp wr
  e9 : args 9 = BitVec.ofNat 32 len
  xy : Region.Disjoint ⟨byteAddr (args 0), len⟩ ⟨byteAddr (args 8), len⟩

theorem keyStatus_le (a : Spec.Ffdh.Parameters) (x : Nat) : Spec.Ffdh.keyStatus a x ≤ 3 := by
  unfold Spec.Ffdh.keyStatus; split
  · decide
  · split <;> decide

end VG.Proof.Ffdh.X86.KeyGen
