module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.GeneratorStageContract

/-! # The generator stage's arguments, from its contract's precondition

The stage's contract asks for 288 bytes of stack: its 272-byte frame and
the 16 bytes below it, which the generation's frame layout (`Lay`) keeps
apart from the working space for the calls of the hash functions; the stage
makes no calls, and writes only its frame. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generator
open VG VG.AArch64

/-- The widths of p parameter generation produces. -/
def Supported (pLen : Nat) : Prop := pLen = 128 ∨ pLen = 256 ∨ pLen = 384

theorem Supported.of_mem {pLen : Nat} (h : pLen ∈ ([128, 256, 384] : List Nat)) : Supported pLen := by
  simpa only [Supported, List.mem_cons, List.not_mem_nil, or_false] using h

/-- The stack the stage's contract asks for. -/
abbrev stack : Nat := 288

/-- The stage's contract on AArch64. -/
abbrev contract (pLen : Nat) : Contract isa :=
  Proof.Dsa.GeneratorStage.contract (Impl.Dsa.AArch64.Generator.layout pLen) abi stack

/-- p, q and the exponent, in memory `m` of the working space `ws`. -/
abbrev pOf (pLen : Nat) (m : Mem) (ws : Addr) : Nat :=
  Proof.Dsa.GeneratorStage.pAt (Impl.Dsa.AArch64.Generator.layout pLen) m ws

abbrev qOf (pLen : Nat) (m : Mem) (ws : Addr) : Nat :=
  Proof.Dsa.GeneratorStage.qAt (Impl.Dsa.AArch64.Generator.layout pLen) m ws

structure StageABI (pLen : Nat) (s : State) : Prop where
  stackLower : stack ≤ s.sp.toNat
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩]
  wsTape : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  stackWs : (below s.sp stack : Region).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
  stackTape : (below s.sp stack : Region).Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
  wsBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64
  tapeBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  size : Impl.Dsa.Generation.Layout.usedBytes pLen ≤ 8 * (s.gpr .x1).toNat
  chunks : (s.gpr .x3).toNat % pLen = 0
  odd : pOf pLen s.mem (s.gpr .x0) % 2 = 1
  bits : Spec.Dsa.bitLength (pOf pLen s.mem (s.gpr .x0)) = 8 * pLen
  qPos : 0 < qOf pLen s.mem (s.gpr .x0)
  exponent : Spec.Rsa.bytesAt s.mem (s.gpr .x0 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.exponent) pLen =
    Spec.Dsa.encodeBE pLen ((pOf pLen s.mem (s.gpr .x0) - 1) / qOf pLen s.mem (s.gpr .x0))

theorem stageABI_of {pLen : Nat} {s : State} (h : (contract pLen).pre s) : StageABI pLen s := by
  sig_pre [contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64.Generator
