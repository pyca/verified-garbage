module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Setup
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive

/-! The exact-recognition prefix restores every nonvolatile register and the original stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

def recognized (s : State) : BitVec 32 := BitVec.ofNat 32 (recognizeList groups (arg s 2).toNat (domain s))

structure Result (s t : State) : Prop where
  tracking : Tracking s t
  value : t.gpr .eax = recognized s
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r

theorem Result.abi {s t : State} (result : Result s t) (h : contract.pre s) : abiPreserved s t :=
  ⟨result.regs, result.tracking.frame.readW (Region.contains_self _ _) (return_separate h) (by decide)⟩

theorem restore_ok {s u : State} (h : contract.pre s) (ready : Ready s u)
    (value : u.gpr .eax = recognized s) : WP isa (.block restore) u (Result s) := by
  have bound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32 := (geometry h).scratchBound
  have room : 48 ≤ (arg s 4).toNat * 8 := scratch_room h
  have base := ready.context.baseReg
  have read : ∀ p ∈ saved, InRegions (u.rd ++ u.wr) (addr (u.gpr .ebx) p.2) 4 := by
    intro p hp
    have fit : p.2 + 4 ≤ 48 := by revert p; decide
    rw [base, ready.tracking.rd, ready.tracking.wr, addr_eq (by omega)]
    exact ⟨scratch s, List.mem_append_right _ (by
      have wr := (geometry h).wr
      change s.wr = [scratch s, ⟨argAddr s 0, 20⟩] at wr
      rw [wr]; exact List.mem_cons_self), Offset.contains_base _ (by omega) (by omega)⟩
  change WP isa (.block (restoreCode .ebx ([(.ebp, 36), (.esi, 40), (.edi, 44)] ++ [(.ebx, 32)]) ++ [])) u _
  refine restoreBase_ok _ (by decide) read (by rw [base]; exact ready.saved) fun t R => WP.block_nil ?_
  have stack : t.gpr .esp = s.gpr .esp :=
    (R.other _ (by decide)).trans ready.tracking.stack
  exact ⟨⟨stack, R.rd.trans ready.tracking.rd, R.wr.trans ready.tracking.wr,
    by rw [R.mem]; exact ready.tracking.frame⟩,
    (R.other _ (by decide)).trans value,
    R.abi (by decide) (by decide) ready.tracking.stack⟩

theorem recognize_ok {s : State} (h : contract.pre s) : WP isa recognize s (Result s) := by
  rw [recognize, WP.seq_iff]
  refine WP.mono (setup_ok h) ?_
  intro t ready
  rw [WP.seq_iff]
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  refine WP.mono (scan_ok groups 0 t ready.context
    (by simpa only [BitVec.add_zero, byteAddr, symAddr] using ready.tracking.table h) fit) ?_
  rintro u ⟨value, mem, rest⟩
  exact restore_ok h ⟨ready.tracking.after mem rest (by decide), ready.context.after mem rest,
    by rw [mem]; exact ready.saved⟩ value

end VG.Proof.Ffdh.X86.VettedValidation
