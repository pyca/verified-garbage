module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.PublicState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Impl.Ffdh.X86_64.VettedValidation
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Table

/-! Saving arguments and scanning the table depends only on the original public domain. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem recognize_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) recognizeCode (fun _ _ => True) := by
  let Q := fun s : State => Context (a.gpr .rcx) (a.gpr .rdi) (a.gpr .rdx).toNat
    (CheckDomain.cdDom a) s ∧ s.syms tableSym = a.syms tableSym ∧ TableAt (a.syms tableSym) groups s
  have entryCT : RelCT isa (fun s t => Start a s ∧ Start a t) (.block entry) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.rcx]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.1.regs .rcx (by decide)).trans (h.2.regs .rcx (by decide)).symm
  have entryWP (s : State) (h : Start a s) : WP isa (.block entry) s Q := by
    have g := geometry h.pre
    refine WP.mono_syms (entry_ok g) ?_
    rintro t ⟨base, mem, rest⟩ sym
    have context := entry_context g base mem rest
    rw [h.regs .rcx (by decide), h.regs .rdi (by decide), h.regs .rdx (by decide), h.domain] at context
    have frame : Frame [⟨s.gpr .rcx, (s.gpr .r8).toNat * 8⟩] s.mem t.mem := by
      rw [mem]; exact entryMem_frame g
    have table := consts_table_after g.consts frame rest g.writable
    rw [h.symbol] at table
    exact ⟨context, (congrFun sym tableSym).trans h.symbol, table⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 31 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (base := a.gpr .rcx) (src := a.gpr .rdi) (table := a.syms tableSym)
    (k := (a.gpr .rdx).toNat) (dom := CheckDomain.cdDom a) groups 0 fit valid).mono
    (P' := fun s t => Q s ∧ Q t)
    (fun _ _ h => by simpa only [BitVec.add_zero] using h) (fun _ _ h => h)
  unfold recognizeCode
  exact ((entryCT.wp (fun s t h => ⟨entryWP s h.1, entryWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq scanning

end VG.Proof.Ffdh.X86_64.VettedValidation
