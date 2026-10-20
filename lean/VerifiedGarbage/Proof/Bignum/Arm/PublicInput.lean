module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Native AAPCS assumptions for checked public RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

structure PublicFnInput (base dst np ep xp : BitVec 32) (len k eLen : Nat)
    (nb eb xb : List Byte) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ len
  exponentPositive : 0 < eLen
  exponentFits : eLen ≤ k
  modulus : PublicBytes np k nb s
  exponent : PublicBytes ep eLen eb s
  input : PublicBytes xp k xb s
  outputFit : dst.toNat + k ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  modulusSeparate : Region.Disjoint ⟨State.addr np, k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  outputSeparate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩
  output : s.gpr .r0 = dst
  source : s.gpr .r2 = np
  count : s.gpr .r3 = BitVec.ofNat 32 k
  stackFit : 56 ≤ s.sp.toNat
  argFit : s.sp.toNat + 24 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 24
  workspaceArg : s.mem.readW (off (State.addr s.sp) 16) 32 = base
  exponentArg : s.mem.readW (State.addr s.sp) 32 = ep
  exponentCountArg : s.mem.readW (off (State.addr s.sp) 4) 32 = BitVec.ofNat 32 eLen
  inputArg : s.mem.readW (off (State.addr s.sp) 8) 32 = xp
  stackWorkspace : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * len⟩
  argsWorkspace : (⟨State.addr s.sp, 24⟩ : Region).Disjoint ⟨State.addr base, 8 * len⟩
  stackModulus : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr np, k⟩
  stackExponent : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr ep, eLen⟩
  stackInput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr xp, k⟩
  stackOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr dst, k⟩
  stackArgs : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr s.sp, 24⟩

end VG.Proof.Bignum.Arm
