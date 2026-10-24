module

public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.PublicState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Ffdh.X86.VettedValidation

/-! Setup, exact scanning, and restoration address only the original public buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86.VettedValidation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Ffdh.X86.VettedValidation VG.Impl.Ffdh.VettedGroups

def EntryAt (a t : State) : Prop := ∃ s, Start a s ∧ EntryPost s t

theorem EntryAt.stack {a t : State} (h : EntryAt a t) : t.gpr .esp = a.gpr .esp := by
  obtain ⟨s, start, entry⟩ := h
  exact (entry.keep.1 _ (by decide)).trans start.stack

theorem EntryAt.low {a t : State} (h : EntryAt a t) : 4 ≤ (t.gpr .esp).toNat := by
  obtain ⟨s, start, entry⟩ := h
  rw [entry.keep.1 .esp (by decide)]
  have := stack_low start.pre
  omega

def SymbolAt (a t : State) : Prop := ∃ s u, Start a s ∧ EntryPost s u ∧ SymAddrPost tableSym u t

theorem SymbolAt.base {a t : State} (h : SymbolAt a t) : t.gpr .ebx = arg a 3 := by
  obtain ⟨s, u, start, entry, symbol⟩ := h
  exact (symbol.gpr _ (by decide)).trans (entry.base.trans (start.args 3 (by decide)))

theorem setup_ct (a : State) : RelCT isa (fun s t => Start a s ∧ Start a t)
    VG.Impl.Ffdh.X86.VettedValidation.setup (fun _ _ => True) := by
  have first : RelCT isa (fun s t => Start a s ∧ Start a t)
      (.block (VG.Impl.Ffdh.X86.entry VG.Impl.Ffdh.X86.CheckDomain.args))
      (VG.X86.Taint.Agree argumentTaint) :=
    (entry_relCT VG.Impl.Ffdh.X86.CheckDomain.args).mono (fun s t h =>
      ⟨h.1.stack.trans h.2.stack.symm,
        by change arg s 3 = arg t 3; rw [h.1.args 3 (by decide), h.2.args 3 (by decide)],
        ((wrapper h.1.pre).argument (i := 3) (by decide)).readSrc,
        ((wrapper h.2.pre).argument (i := 3) (by decide)).readSrc⟩) (fun _ _ h => h)
  have move : RelCT isa (VG.X86.Taint.Agree argumentTaint) (.block [.mov .ebx (.reg .edi)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) argumentTaint _ (hc := .block []) (by rfl)
    intro _ _ h
    exact h
  have entryCT : RelCT isa (fun s t => Start a s ∧ Start a t)
      (.block VG.Impl.Ffdh.X86.VettedValidation.entry) (fun _ _ => True) :=
    RelCT.block_append (first.seq move)
  have entryWP (s : State) (h : Start a s) :
      WP isa (.block VG.Impl.Ffdh.X86.VettedValidation.entry) s (EntryAt a) :=
    WP.mono (entry_ok h.pre) (fun _ entry => ⟨s, h, entry⟩)
  have entryStage : RelCT isa (fun s t => Start a s ∧ Start a t)
      (.block VG.Impl.Ffdh.X86.VettedValidation.entry) (fun s t => EntryAt a s ∧ EntryAt a t) :=
    ((entryCT.wp (fun s t h => ⟨entryWP s h.1, entryWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩))
  have symbolCT : RelCT isa (fun s t => EntryAt a s ∧ EntryAt a t) tableAddress (fun _ _ => True) := by
    intro s t ts tt u v h es et
    rw [symFrame_trace h.1.low es, symFrame_trace h.2.low et, h.1.stack, h.2.stack]
    exact ⟨rfl, trivial⟩
  have symbolWP (s : State) (h : EntryAt a s) : WP isa tableAddress s (SymbolAt a) := by
    obtain ⟨origin, start, entry⟩ := h
    exact WP.mono (symFrame_ok tableSym s (EntryAt.low ⟨origin, start, entry⟩))
      (fun _ symbol => ⟨origin, s, start, entry, symbol⟩)
  have symbolStage : RelCT isa (fun s t => EntryAt a s ∧ EntryAt a t) tableAddress
      (fun s t => SymbolAt a s ∧ SymbolAt a t) :=
    ((symbolCT.wp (fun s t h => ⟨symbolWP s h.1, symbolWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩))
  have tableCT : RelCT isa (fun s t => SymbolAt a s ∧ SymbolAt a t) (.block saveTable) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.ebx]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.base.trans h.2.base.symm
  exact entryStage.seq (symbolStage.seq tableCT)

def ScanAt (a t : State) : Prop :=
  Context (arg a 3) (arg a 0) (a.gpr .esp) (a.syms tableSym) (arg a 2).toNat (domain a) t ∧
    TableAt (byteAddr (a.syms tableSym)) groups t

theorem recognize_ct (a : State) : RelCT isa (fun s t => Start a s ∧ Start a t) recognize (fun _ _ => True) := by
  have setupWP (s : State) (h : Start a s) : WP isa VG.Impl.Ffdh.X86.VettedValidation.setup s (ScanAt a) := by
    refine WP.mono (setup_ok h.pre) ?_
    intro t ready
    have ctx := ready.context
    rw [h.args 3 (by decide), h.args 0 (by decide), h.stack, h.symbol, h.args 2 (by decide), h.domain] at ctx
    have table := ready.tracking.table h.pre
    change TableAt (byteAddr (s.syms tableSym)) groups t at table
    rw [h.symbol] at table
    exact ⟨ctx, table⟩
  have setupStage : RelCT isa (fun s t => Start a s ∧ Start a t) VG.Impl.Ffdh.X86.VettedValidation.setup
      (fun s t => ScanAt a s ∧ ScanAt a t) :=
    (((setup_ct a).wp (fun s t h => ⟨setupWP s h.1, setupWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩))
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  have valid : ∀ g ∈ groups, g.len < 2 ^ 32 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanCT : RelCT isa (fun s t => ScanAt a s ∧ ScanAt a t) (scan groups 0) (fun _ _ => True) :=
    (scan_ct (base := arg a 3) (src := arg a 0) (sp := a.gpr .esp) (table := a.syms tableSym)
      (k := (arg a 2).toNat) (dom := domain a) groups 0 fit valid).mono
      (fun _ _ h => by simpa only [BitVec.add_zero, ScanAt] using h) (fun _ _ h => h)
  have scanWP (s : State) (h : ScanAt a s) : WP isa (scan groups 0) s (ScanAt a) :=
    WP.mono (scan_ok groups 0 s h.1 (by simpa only [BitVec.add_zero] using h.2) fit)
      (fun t ⟨_, mem, rest⟩ => ⟨h.1.after mem rest, h.2.after mem rest⟩)
  have scanStage : RelCT isa (fun s t => ScanAt a s ∧ ScanAt a t) (scan groups 0)
      (fun s t => ScanAt a s ∧ ScanAt a t) :=
    ((scanCT.wp (fun s t h => ⟨scanWP s h.1, scanWP t h.2⟩)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩))
  have restoreCT : RelCT isa (fun s t => ScanAt a s ∧ ScanAt a t) (.block restore) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.ebx]) _ (hc := .block []) (by rfl)
    intro s t h
    apply agree_regs
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact h.1.1.baseReg.trans h.2.1.baseReg.symm
  exact setupStage.seq (scanStage.seq restoreCT)

end VG.Proof.Ffdh.X86.VettedValidation
