module

public import VerifiedGarbage.Proof.Bignum.Arm.PcBody
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Native AAPCS assumptions for public RSA precomputation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

structure PcBuffers (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.scratchWords k ≤ len
  sourceFits : src.toNat + k ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) k
  sourceSeparate : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩
  outputFits : dst.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32
  writable : InRegions s.wr (State.addr dst) (16 * Spec.Rsa.modulusWords k)
  outputSeparate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩

structure PcBodyInput (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop extends
    PcBuffers base dst src len k s where
  stack : PcStack base dst src len k s
  ptr : s.gpr .r0 = base
  source : s.gpr .r4 = src
  count : s.gpr .r6 = BitVec.ofNat 32 k

structure PcFnInput (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop extends
    PcBuffers base dst src len k s where
  output : s.gpr .r0 = dst
  source : s.gpr .r2 = src
  count : s.gpr .r3 = BitVec.ofNat 32 k
  stackFit : 56 ≤ s.sp.toNat
  argFit : s.sp.toNat + 8 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 8
  workspaceArg : s.mem.readW (State.addr s.sp) 32 = base
  stackWorkspace : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * len⟩
  stackInput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr src, k⟩
  stackOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr dst, 16 * Spec.Rsa.modulusWords k⟩
  stackArgs : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr s.sp, 8⟩

end VG.Proof.Bignum.Arm
