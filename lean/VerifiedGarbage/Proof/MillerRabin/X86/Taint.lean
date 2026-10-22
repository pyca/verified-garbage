module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.MillerRabin.X86.Round
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Timing certificates for the round's arithmetic pieces

Only the workspace address, stack address, width and saved workspace length
are public here. A correctness invariant reestablishes these facts between
pieces after a borrowed arithmetic routine has written through pointers.
-/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Impl.Mont.X86

def pieceTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false, lens := [1132, 1600],
    bases := [(.esp, 0, 0), (.edi, 1, 0)],
    slots := ((Slots.empty.add 1 48 4).add 0 savedLength 4) }

def entryTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, argLen := 12, stk := [some 1132] }

theorem entry_cert : ∃ hc, (VG.Taint.check VG.X86.taint entryTaint (.block entry) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem finish_cert : ∃ hc, (VG.Taint.check VG.X86.taint (τr [.esp, .edi]) (.block finish) hc).isSome = true :=
  ⟨_, by taint_decide⟩

def argsTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false, lens := [36, 1132, 1600],
    bases := [(.esp, 0, 0), (.esp, 1, 36), (.edi, 2, 0)],
    slots := (Slots.empty.add 2 48 4).add 1 savedLength 4 }

def wordTaint (rs : List Reg) (i d : Nat) : VG.X86.Taint.T :=
  { pieceTaint with regs := .ofList ([.edi, .esp] ++ rs), slots := pieceTaint.slots.add i d 4 }

abbrev PieceCert (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.X86.taint pieceTaint c hc).isSome = true

theorem copy_one_cert : PieceCert (copy 11 9) := ⟨_, by taint_decide⟩
theorem copy_witness_cert : PieceCert (copy 12 5) := ⟨_, by taint_decide⟩
theorem copy_accumulator_cert : PieceCert (copy 6 5) := ⟨_, by taint_decide⟩
theorem copy_minus_cert : PieceCert (copy 8 10) := ⟨_, by taint_decide⟩
theorem copy_start_cert : PieceCert (copy 6 11) := ⟨_, by taint_decide⟩
theorem copy_scan_cert : PieceCert (copy 5 11) := ⟨_, by taint_decide⟩
theorem equal_one_cert : PieceCert (equal sE1 6 11) := ⟨_, by taint_decide⟩
theorem equal_minus_cert : PieceCert (equal sE2 6 8) := ⟨_, by taint_decide⟩

theorem table_count_cert : PieceCert (.block (arrayPointer .eax (aT0 + 2) .edx ++
    [.store (sp tableCursor) .eax, .mov .eax (.imm 14), .store (sc sK) .eax])) :=
  ⟨_, by taint_decide⟩

theorem square_args_cert : ∃ hc, (VG.Taint.check VG.X86.taint argsTaint
    (.block (productArgs 6 6 6)) hc).isSome = true := ⟨_, by taint_decide⟩
theorem digit_args_cert : ∃ hc, (VG.Taint.check VG.X86.taint argsTaint
    (.block (productArgs 6 6 5)) hc).isSome = true := ⟨_, by taint_decide⟩
theorem save_tail_cert : PieceCert saveTail := ⟨_, by taint_decide⟩
theorem save_array_cert : PieceCert saveArray := ⟨_, by taint_decide⟩
theorem restore_tail_cert : PieceCert restoreTail := ⟨_, by taint_decide⟩
theorem restore_array_cert : PieceCert restoreArray := ⟨_, by taint_decide⟩
theorem low_bits_cert : PieceCert (.block lowBits) := ⟨_, by taint_decide⟩
theorem window_counters_cert : PieceCert (.block winCounters) := ⟨_, by taint_decide⟩
theorem square_four_cert : PieceCert (.block sqFour) := ⟨_, by taint_decide⟩

theorem word_load_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 1 sK)
    (.block wordLoad) hc).isSome = true := ⟨_, by taint_decide⟩
theorem word_test_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 1 sK)
    (.block [.mov .eax (.mem (sc sK)), .alu .cmp .eax (.imm 0)]) hc).isSome = true := ⟨_, by taint_decide⟩

theorem window_end_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 1 sK)
    (.block winEnd) hc).isSome = true := ⟨_, by taint_decide⟩
theorem square_flag_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 1 sQ)
    (.block sqFlag) hc).isSome = true := ⟨_, by taint_decide⟩
theorem table_transfer_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 0 tableCursor)
    tabTransfer hc).isSome = true := ⟨_, by taint_decide⟩
theorem table_end_cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [.ebx] 1 sK)
    (.block tabEnd) hc).isSome = true := ⟨_, by taint_decide⟩

theorem scan_entry_1_cert : PieceCert (.seq (.block (maskJ 1)) (select 5 12)) := ⟨_, by taint_decide⟩

theorem scan_entry_2_cert : PieceCert (.seq (.block (maskJ 2)) (select 5 13)) := ⟨_, by taint_decide⟩

theorem scan_entry_3_cert : PieceCert (.seq (.block (maskJ 3)) (select 5 14)) := ⟨_, by taint_decide⟩

theorem scan_entry_4_cert : PieceCert (.seq (.block (maskJ 4)) (select 5 15)) := ⟨_, by taint_decide⟩

theorem scan_entry_5_cert : PieceCert (.seq (.block (maskJ 5)) (select 5 16)) := ⟨_, by taint_decide⟩

theorem scan_entry_6_cert : PieceCert (.seq (.block (maskJ 6)) (select 5 17)) := ⟨_, by taint_decide⟩

theorem scan_entry_7_cert : PieceCert (.seq (.block (maskJ 7)) (select 5 18)) := ⟨_, by taint_decide⟩

theorem scan_entry_8_cert : PieceCert (.seq (.block (maskJ 8)) (select 5 19)) := ⟨_, by taint_decide⟩

theorem scan_entry_9_cert : PieceCert (.seq (.block (maskJ 9)) (select 5 20)) := ⟨_, by taint_decide⟩

theorem scan_entry_10_cert : PieceCert (.seq (.block (maskJ 10)) (select 5 21)) := ⟨_, by taint_decide⟩

theorem scan_entry_11_cert : PieceCert (.seq (.block (maskJ 11)) (select 5 22)) := ⟨_, by taint_decide⟩

theorem scan_entry_12_cert : PieceCert (.seq (.block (maskJ 12)) (select 5 23)) := ⟨_, by taint_decide⟩

theorem scan_entry_13_cert : PieceCert (.seq (.block (maskJ 13)) (select 5 24)) := ⟨_, by taint_decide⟩

theorem scan_entry_14_cert : PieceCert (.seq (.block (maskJ 14)) (select 5 25)) := ⟨_, by taint_decide⟩

theorem scan_entry_15_cert : PieceCert (.seq (.block (maskJ 15)) (select 5 26)) := ⟨_, by taint_decide⟩

theorem scan_entry_cert {j : Nat} (lo : 1 ≤ j) (hi : j < 16) :
    PieceCert (.seq (.block (maskJ j)) (select 5 (11 + j))) := by
  have cases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact scan_entry_1_cert
    | exact scan_entry_2_cert
    | exact scan_entry_3_cert
    | exact scan_entry_4_cert
    | exact scan_entry_5_cert
    | exact scan_entry_6_cert
    | exact scan_entry_7_cert
    | exact scan_entry_8_cert
    | exact scan_entry_9_cert
    | exact scan_entry_10_cert
    | exact scan_entry_11_cert
    | exact scan_entry_12_cert
    | exact scan_entry_13_cert
    | exact scan_entry_14_cert
    | exact scan_entry_15_cert

end VG.Proof.MillerRabin.X86
