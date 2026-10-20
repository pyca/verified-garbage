module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBuffers
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Arm.CallF


/-! # Native ARM arguments and buffers for private RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

structure CrtFnInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  workspace : Workspace s g.base g.size
  lengthValid : Spec.Rsa.lenValid g.length
  storageFits : VG.Impl.Bignum.Arm.Crt.totalBytes g.words ≤ g.size
  pPositive : 0 < g.pLength
  pShort : g.pLength < g.length
  qPositive : 0 < g.qLength
  qShort : g.qLength < g.length
  source : ∀ i, PublicBytes (g.source i) (g.sourceLength i) (bs i) s
  sourceSeparate : ∀ i, Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr g.base, g.size⟩
  outputFits : g.output.toNat + g.length ≤ 2 ^ 32
  write : InRegions s.wr (State.addr g.output) g.length
  outputSeparate : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr g.output, g.length⟩
  output : s.gpr .r0 = g.output
  modulus : s.gpr .r2 = g.modulus
  count : s.gpr .r3 = BitVec.ofNat 32 g.length
  stackFit : 56 ≤ s.sp.toNat
  argFit : s.sp.toNat + 56 ≤ 2 ^ 32
  argRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 56
  pointer : ∀ i : Fin 6, s.mem.readW (off (State.addr s.sp) (8 * i.val)) 32 = g.source i.succ
  length : ∀ i : Fin 6, s.mem.readW (off (State.addr s.sp) (4 + 8 * i.val)) 32 = BitVec.ofNat 32 (g.sourceLength i.succ)
  workspaceArg : s.mem.readW (off (State.addr s.sp) 48) 32 = g.base
  stackWorkspace : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr g.base, g.size⟩
  argsWorkspace : (⟨State.addr s.sp, 56⟩ : Region).Disjoint ⟨State.addr g.base, g.size⟩
  stackSource : ∀ i, (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩
  stackOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr g.output, g.length⟩
  stackArgs : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr s.sp, 56⟩

end VG.Proof.Bignum.Arm
