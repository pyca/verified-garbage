module

import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Frame
public import VerifiedGarbage.Proof.Ffdh.X86.Entry
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainTop
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Geometry
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! Reuse the original verified register-save prefix before recognizing standard domains. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

structure EntryPost (s t : State) : Prop where
  base : t.gpr .ebx = arg s 3
  saved : Saved t.mem (addr (arg s 3)) s.gpr saved
  frame : Frame [scratch s] s.mem t.mem
  keep : Keeps [.eax, .edi, .ebx] s t
  syms : t.syms = s.syms

theorem wrapper {s : State} (h : contract.pre s) : WrapABI VG.Impl.Ffdh.X86.CheckDomain.args 5 s := by
  have old := CheckDomain.wrapABI (geometry h)
  exact ⟨old.below, old.stackLow, old.stackBound, old.argsIn, old.wsIn, old.scratchArgs,
    old.retScratch, old.belowScratch, old.scratchBound, old.lower, old.upper, old.scratchLength⟩

theorem entry_ok {s : State} (h : contract.pre s) :
    WP isa (.block VG.Impl.Ffdh.X86.VettedValidation.entry) s (EntryPost s) := by
  have wrap := wrapper h
  rw [VG.Impl.Ffdh.X86.VettedValidation.entry, WP.block_append_iff]
  refine WP.mono_syms (VG.Proof.Ffdh.X86.entry_ok wrap) ?_
  rintro u ⟨buffer, savedU, keepU, outside⟩ symsU
  have pointer : u.gpr .edi = arg s 3 := by
    have value := congrArg BitVec.toNat buffer.edi
    change ((u.gpr .edi).setWidth 64).toNat = ((arg s 3).setWidth 64).toNat at value
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (Nat.lt_trans (u.gpr .edi).isLt (by decide : 2 ^ 32 < 2 ^ 64)), Nat.mod_eq_of_lt
      (Nat.lt_trans (arg s 3).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using value
  refine wp_mov fun t T => WP.block_nil ⟨T.gpr.trans pointer, ?_, ?_,
    (keepU.mono (by decide)).widen T.keeps, T.syms.trans symsU⟩
  · intro p hp
    have member : p ∈ VG.Impl.Bignum.X86.Crt.savedRegisters := by
      revert p
      decide
    have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
    have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
    have po : p.2 + 4 ≤ 48 := by revert p; decide
    rw [T.mem, addr_eq (by omega)]
    exact savedU p member
  · rw [T.mem]
    have fit : (arg s 4).toNat * 8 < 2 ^ 64 := by have := (arg s 4).isLt; omega
    have F := VG.Proof.Bignum.outside_frame outside
      (by change 0 + (arg s 4).toNat * 8 ≤ 2 ^ 64; omega)
    change Frame [⟨byteAddr (arg s 3) + BitVec.ofNat 64 0, (arg s 4).toNat * 8⟩] s.mem u.mem at F
    change Frame [⟨byteAddr (arg s 3), (arg s 4).toNat * 8⟩] s.mem u.mem
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using F


end VG.Proof.Ffdh.X86.VettedValidation
