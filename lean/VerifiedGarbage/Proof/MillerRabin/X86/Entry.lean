module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Offset

/-! # The reviewed prepared-round contract at the i686 ABI boundary -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Spec.Rsa.Mont

abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev lenOf (s : State) : Nat := (arg s 1).toNat * 8

def geometry (s : State) : Geometry := ⟨wsOf s, lenOf s, wOf s.mem (wsOf s)⟩

structure Entry (s : State) : Prop where
  stackFit : 56 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  stackSeparate : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  stackArgsSeparate : (⟨(s.gpr .esp).setWidth 64 - 56#64, 56⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  argSeparate : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  returnSeparate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (wsOf s) (arg s 1).toNat
  prepared : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (wsOf s)

theorem entry_of {s : State} (h : (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56).pre s) : Entry s := by
  sig_pre [Spec.MillerRabin.roundContract, Spec.MillerRabin.roundSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> first
    | with_reducible assumption
    | (unfold Spec.MillerRabin.Prepared; sig_and_intros <;> with_reducible assumption)

theorem Entry.valid {s : State} (E : Entry s) : (geometry s).Valid := by
  obtain ⟨_, _, lo, hi, fit, _⟩ := E.layout
  refine ⟨lo, hi, ?_⟩
  change arrAt (wOf s.mem (wsOf s)) 28 ≤ 8 * (arg s 1).toNat at fit
  simpa only [geometry, lenOf, Nat.mul_comm] using fit

theorem Entry.ws_toNat {s : State} (_ : Entry s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

end VG.Proof.MillerRabin.X86
