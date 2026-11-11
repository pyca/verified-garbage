module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBuffers
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Arm.CallF


/-! # Native ARM arguments and buffers for private RSA -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

/-- At entry: `R² mod p` and `R² mod q` at `a`, the incoming argument 14. -/
structure CrtR2In (g : CrtGeometry) (bs : Fin 7 → List Byte) (a : BitVec 32) (s : State) : Prop where
  slotFit : s.sp.toNat + 60 ≤ 2 ^ 32
  slotRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 56) 4
  slot : s.mem.readW (off (State.addr s.sp) 56) 32 = a
  slotSeparate : Region.Disjoint ⟨off (State.addr s.sp) 56, 4⟩ ⟨State.addr g.base, g.size⟩
  slotOutput : Region.Disjoint ⟨off (State.addr s.sp) 56, 4⟩ ⟨State.addr g.output, g.length⟩
  slotStack : (FrameStack.belowA s.sp 56).Disjoint ⟨off (State.addr s.sp) 56, 4⟩
  fit : a.toNat + 8 * g.r2Words ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr a) (8 * g.r2Words)
  separate : Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ ⟨State.addr g.base, g.size⟩
  stack : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr a, 8 * g.r2Words⟩
  output : Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ ⟨State.addr g.output, g.length⟩
  words : Spec.Rsa.wordsAt s.mem (State.addr a) g.r2Words = Spec.Rsa.primeR2 (bs 2) ++ Spec.Rsa.primeR2 (bs 3)

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
  r2 : ∀ a, g.r2 = some a → CrtR2In g bs a s

end VG.Proof.Bignum.Arm
