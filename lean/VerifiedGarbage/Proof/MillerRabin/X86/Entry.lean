module

public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Offset

/-! # The reviewed prepared-round contract at the i686 ABI boundary -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Rsa.Mont

abbrev wsOf (s : State) : Addr := (arg s 0).setWidth 64
abbrev lenOf (s : State) : Nat := (arg s 1).toNat * 8

def geometry (s : State) : Geometry := ⟨wsOf s, lenOf s, wOf s.mem (wsOf s)⟩

structure Entry (s : State) : Prop where
  stackFit : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨wsOf s, lenOf s⟩]
  bound : (arg s 0).toNat + lenOf s ≤ 2 ^ 32
  stackSeparate : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  stackArgsSeparate : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  argSeparate : (⟨wsOf s, lenOf s⟩ : Region).Disjoint ⟨argAddr s 0, 8⟩
  returnSeparate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨wsOf s, lenOf s⟩
  layout : Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact s.mem (wsOf s) (arg s 1).toNat
  prepared : Proof.MillerRabin.Round.Prepared Proof.MillerRabin.Round.compact s.mem (wsOf s)

theorem entry_of {s : State} (h : (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96).pre s) : Entry s := by
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> first
    | with_reducible assumption
    | (unfold Proof.MillerRabin.Round.Prepared; sig_and_intros <;> with_reducible assumption)

theorem Entry.valid {s : State} (E : Entry s) : (geometry s).Valid := by
  obtain ⟨_, _, lo, hi, fit, _⟩ := E.layout
  refine ⟨lo, hi, ?_⟩
  change arrAt (wOf s.mem (wsOf s)) 28 ≤ 8 * (arg s 1).toNat at fit
  simpa only [geometry, lenOf, Nat.mul_comm] using fit

theorem Entry.ws_toNat {s : State} (_ : Entry s) : (wsOf s).toNat = (arg s 0).toNat := by
  simp only [wsOf, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))]

end VG.Proof.MillerRabin.X86
