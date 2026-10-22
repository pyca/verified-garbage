module

public import VerifiedGarbage.Proof.MillerRabin.X86.Prepared
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset

/-! # Resources supplied by the shared cdecl primality-round contract -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev bytesOf (s : State) : Nat := (arg s 1).toNat * 8
abbrev stackBytes : Nat := VG.Impl.MillerRabin.X86.frameBytes + 40

structure RoundABI (s : State) : Prop where
  stackLow : stackBytes ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨wsOf s, bytesOf s⟩]
  argScratch : (⟨argAddr s 0, 8⟩ : Region).Disjoint ⟨wsOf s, bytesOf s⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, bytesOf s⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨wsOf s, bytesOf s⟩
  bound : (arg s 0).toNat + bytesOf s ≤ 2 ^ 32
  layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (wsOf s) (arg s 1).toNat
  prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (wsOf s)

theorem roundAbi_of {s : State}
    (h : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).pre s) : RoundABI s := by
  sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  · exact Region.Disjoint.symm (by with_reducible assumption)
  · change (⟨(s.gpr .esp).setWidth 64 - 1172#64, 1172⟩ : Region).Disjoint ⟨wsOf s, bytesOf s⟩
    assumption
  · unfold Spec.MillerRabin.Prepared
    exact ⟨by with_reducible assumption, by with_reducible assumption, by with_reducible assumption,
      by with_reducible assumption, by with_reducible assumption, by with_reducible assumption,
      by with_reducible assumption, by with_reducible assumption⟩

end VG.Proof.MillerRabin.X86
