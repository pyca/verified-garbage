module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
public import VerifiedGarbage.TCB.X86.Target

/-! ### `MillerRabin.X86.Entry`, which this module and modules that import it used -/

section

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

end

end

/-! # Saving the round's registers preserves its prepared workspace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

abbrev entered (s : State) : State := Compact.entered s

theorem Entry.stackSeparate' {s : State} (E : Entry s) :
    (below (s.gpr .esp) 96).Disjoint ⟨wsOf s, lenOf s⟩ := by
  unfold below
  rw [Taint.sub_setWidth E.stackFit]
  exact E.stackSeparate

theorem Entry.stackArgsSeparate' {s : State} (E : Entry s) :
    (below (s.gpr .esp) 96).Disjoint ⟨argAddr s 0, 8⟩ := by
  unfold below
  rw [Taint.sub_setWidth E.stackFit]
  exact E.stackArgsSeparate

theorem Entry.savedSeparate {s : State} (E : Entry s) :
    (below (s.gpr .esp) 16).Disjoint ⟨wsOf s, lenOf s⟩ :=
  E.stackSeparate'.sub_left (below_sub (by decide) E.stackFit)

theorem Entry.pushed_read {s : State} (E : Entry s) {d bits : Nat}
    (fit : d + bits / 8 ≤ lenOf s) :
    (entered s).mem.readW (off (wsOf s) d) bits = s.mem.readW (off (wsOf s) d) bits := by
  have bound := E.bound
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ (s.gpr .esp).toNat; have := E.stackFit; omega_using [this])
  exact saved.readW (r := ⟨wsOf s, lenOf s⟩) (Offset.contains_base _ fit (by omega_using [fit, bound]))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact E.savedSeparate.symm) (by omega_using [fit, bound])

theorem Entry.pushed_w32 {s : State} (E : Entry s) {d : Nat} (fit : d + 4 ≤ lenOf s) :
    w32 (entered s).mem (wsOf s) d = w32 s.mem (wsOf s) d :=
  congrArg BitVec.toNat (E.pushed_read (bits := 32) fit)

theorem Entry.pushed_val32 {s : State} (E : Entry s) {d n : Nat}
    (fit : d + 4 * n ≤ lenOf s) :
    val32 (entered s).mem (wsOf s) d n = val32 s.mem (wsOf s) d n := by
  apply val32_congr
  intro i index
  exact E.pushed_w32 (by omega_using [fit, index])

end VG.Proof.MillerRabin.X86
