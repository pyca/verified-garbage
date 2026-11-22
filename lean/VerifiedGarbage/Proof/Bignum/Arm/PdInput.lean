module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # Native AAPCS assumptions for checked public RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

structure PdFnInput (base dst np ep xp : BitVec 32) (len k eLen N R : Nat)
    (eb xb : List Byte) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ len
  exponentPositive : 0 < eLen
  exponentFits : eLen ≤ k
  sourceFit : np.toNat + 16 * Spec.Rsa.modulusWords k ≤ 2 ^ 32
  preRead : InRegions (s.rd ++ s.wr) (State.addr np) (16 * Spec.Rsa.modulusWords k)
  modulus : (s.mem.read (State.addr np) (8 * Spec.Rsa.modulusWords k)).toNat = N
  r2 : (s.mem.read (off (State.addr np) (8 * Spec.Rsa.modulusWords k)) (8 * Spec.Rsa.modulusWords k)).toNat = R
  exponent : PublicBytes ep eLen eb s
  input : PublicBytes xp k xb s
  outputFit : dst.toNat + k ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  modulusSeparate : Region.Disjoint ⟨State.addr np, 16 * Spec.Rsa.modulusWords k⟩ ⟨State.addr base, 8 * len⟩
  exponentSeparate : Region.Disjoint ⟨State.addr ep, eLen⟩ ⟨State.addr base, 8 * len⟩
  inputSeparate : Region.Disjoint ⟨State.addr xp, k⟩ ⟨State.addr base, 8 * len⟩
  outputSeparate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩
  output : s.gpr .r0 = dst
  source : s.gpr .r2 = np
  count : s.gpr .r1 = BitVec.ofNat 32 k
  stackFit : 56 ≤ s.sp.toNat
  argFit : s.sp.toNat + 24 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 24
  workspaceArg : s.mem.readW (off (State.addr s.sp) 16) 32 = base
  exponentArg : s.mem.readW (State.addr s.sp) 32 = ep
  exponentCountArg : s.mem.readW (off (State.addr s.sp) 4) 32 = BitVec.ofNat 32 eLen
  inputArg : s.mem.readW (off (State.addr s.sp) 8) 32 = xp
  stackWorkspace : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr base, 8 * len⟩
  argsWorkspace : (⟨State.addr s.sp, 24⟩ : Region).Disjoint ⟨State.addr base, 8 * len⟩
  stackModulus : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr np, 16 * Spec.Rsa.modulusWords k⟩
  stackExponent : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr ep, eLen⟩
  stackInput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr xp, k⟩
  stackOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr dst, k⟩
  stackArgs : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr s.sp, 24⟩
  /-- The stack a call of the shared product needs below the frame. -/
  callFit : 104 ≤ s.sp.toNat
  callWorkspace : (FrameStack.belowA s.sp 104).Disjoint ⟨State.addr base, 8 * len⟩
  callExponent : (FrameStack.belowA s.sp 104).Disjoint ⟨State.addr ep, eLen⟩
  callInput : (FrameStack.belowA s.sp 104).Disjoint ⟨State.addr xp, k⟩

/-- The stack a call of the shared product needs, below the 56-byte frame. -/
theorem PdFnInput.callStack {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {s u : State} (h : PdFnInput base dst np ep xp len k eLen N R eb xb s)
    (sp : u.sp = s.sp - BitVec.ofNat 32 56) : CallStack base len u :=
  ⟨by rw [sp, FrameStack.sub_toNat' h.stackFit]; have := h.callFit; omega,
    by rw [sp]; exact h.callWorkspace.sub_left (FrameStack.belowA_inner (k := 56) (by decide) h.callFit)⟩

theorem PdFnInput.callApart {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {s u : State} (h : PdFnInput base dst np ep xp len k eLen N R eb xb s)
    (sp : u.sp = s.sp - BitVec.ofNat 32 56) :
    Region.Disjoint ⟨State.addr ep, eLen⟩ (FrameStack.belowA u.sp 48) ∧
      Region.Disjoint ⟨State.addr xp, k⟩ (FrameStack.belowA u.sp 48) := by
  have sub := FrameStack.belowA_inner (k := 56) (a := 48) (by decide) h.callFit
  rw [sp]
  exact ⟨(h.callExponent.sub_left sub).symm, (h.callInput.sub_left sub).symm⟩

end VG.Proof.Bignum.Arm
