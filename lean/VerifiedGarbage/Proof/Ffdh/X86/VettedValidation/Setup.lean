module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Tracking
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive

/-! Saving the static table address establishes the read-only scan context. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation

def setup : Prog isa := .seq (.block VG.Impl.Ffdh.X86.VettedValidation.entry)
  (.seq tableAddress (.block saveTable))

structure Ready (s t : State) : Prop where
  tracking : Tracking s t
  context : Context (arg s 3) (arg s 0) (s.gpr .esp) (s.syms tableSym) (arg s 2).toNat (domain s) t
  saved : Saved t.mem (addr (arg s 3)) s.gpr saved

theorem setup_ok {s : State} (h : contract.pre s) : WP isa setup s (Ready s) := by
  rw [setup, WP.seq_iff]
  refine WP.mono (entry_ok h) ?_
  intro u entry
  have spU : u.gpr .esp = s.gpr .esp := entry.keep.1 _ (by decide)
  rw [WP.seq_iff]
  refine WP.mono (symFrame_ok tableSym u (by rw [spU]; have := stack_low h; omega_arith)) ?_
  intro v R
  have spV : v.gpr .esp = s.gpr .esp := (R.gpr _ (by decide)).trans spU
  have baseV : v.gpr .ebx = arg s 3 := (R.gpr _ (by decide)).trans entry.base
  have F1 : Frame (writes s) s.mem u.mem := entry.frame.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_self, fun _ h => h⟩)
  have symbolFrame : Frame [below (s.gpr .esp) 4] u.mem v.mem := by
    simpa only [spU] using R.frame
  have F2 : Frame (writes s) u.mem v.mem := symbolFrame.sub (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  have F : Frame (writes s) s.mem v.mem := F1.trans F2
  have trackV : Tracking s v := ⟨spV, R.rd.trans entry.keep.2.1, R.wr.trans entry.keep.2.2, F⟩
  have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
  have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
  have fits : Fits ((arg s 4).toNat * 8) saved := by
    have small : Fits 48 saved := by decide
    exact ⟨fun p hp => Nat.le_trans (small.1 p hp) room, small.2⟩
  have savedV : Saved v.mem (addr (arg s 3)) s.gpr saved :=
    entry.saved.of_frame R.frame (R := scratch s) (contains_of_fits bound fits) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [spU]
      have sep : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint (scratch s) :=
        (geometry h).belowScratch
      exact (sep.sub_left (symbol_sub h)).symm)
  have writable : InRegions v.wr (addr (v.gpr .ebx) 16) 4 := by
    rw [baseV, trackV.wr, addr_eq (by omega_arith)]
    exact ⟨scratch s, by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self,
      Offset.contains_base _ (by omega_arith) (by decide)⟩
  have tableValue : v.gpr .eax = s.syms tableSym := by rw [R.addr, entry.syms]
  unfold saveTable
  refine wp_stm rfl writable fun t T => WP.block_nil ?_
  have frameT : Frame (writes s) s.mem t.mem := by
    rw [T.mem, baseV, addr_eq (by omega_arith)]
    exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by decide))
  have trackT : Tracking s t := ⟨by rw [T.gpr]; exact spV, T.rd.trans trackV.rd,
    T.wr.trans trackV.wr, frameT⟩
  refine ⟨trackT, ?_, ?_⟩
  · have length : (domain s).length = (arg s 1).toNat := by
      simp only [domain, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    refine ⟨by rw [T.gpr]; exact baseV, trackT.stack, trackT.args h 0 (by decide), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, table_fit h, by have := stack_bound h; omega_arith, ?_, (geometry h).pLen.1, (geometry h).pLen.2⟩
    · rw [trackT.args h 1 (by decide), length, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [trackT.args h 2 (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have read := CallLay.inRegions_sub (read_args h) (off := 0) (l := 12) (by decide) (by decide)
      simp only [BitVec.add_zero] at read
      rw [trackT.rd, trackT.wr, argAddr, trackT.stack]
      exact read
    · rw [trackT.rd, trackT.wr]
      exact ⟨scratch s, List.mem_append_right _ (by
        have wr := (geometry h).wr
        change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
        rw [wr]; exact List.mem_cons_self), by
        rw [addr_eq (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by decide)⟩
    · rw [T.mem, baseV, Mem.readW_writeW_self32, tableValue]
    · rw [trackT.rd, trackT.wr, length]
      exact read_domain h
    · have dom := trackT.domain_eq h
      unfold domain at dom
      rw [trackT.args h 0 (by decide), trackT.args h 1 (by decide)] at dom
      rw [length]
      exact dom
    · rw [length]; exact (geometry h).domBound
    · rw [length]; exact (geometry h).dLen
  · rw [T.mem, baseV]
    exact savedV.writeW_addr bound (fun p hp => fits.1 p hp) (by omega_arith)
      (by decide) _

end VG.Proof.Ffdh.X86.VettedValidation
