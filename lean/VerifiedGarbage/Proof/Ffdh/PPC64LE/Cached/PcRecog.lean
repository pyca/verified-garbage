module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Table
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation

/-! # The vetted groups' recognition on PPC64LE, from its context and table

`recognize_ok` and `recognize_ct` of `VettedValidation` with what they read
of `vg_ffdh_check_domain`'s precondition as hypotheses: the domain's context
(`Context`) and the table, for a caller other than `vg_ffdh_check_domain`. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

/-- `recognize`: `r8 :=` the domain's recognized width. -/
theorem recognize_ok' {s : State} {src : Addr} {k : Nat} {dom : List Byte} (input : Context src k dom s)
    (table : TableAt (s.syms tableSym) groups s) :
    WP isa recognize s fun t =>
      t.gpr .r8 = BitVec.ofNat 64 (recognizeList groups k dom) ∧ t.mem = s.mem ∧ Keep allClobbers s t ∧
        t.lr = s.lr := by
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  rw [recognize, WP.seq_iff]
  refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
    (Q := fun u : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s u ∧ u.gpr .r12 = s.lr)
    (fun u o saved => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨o, saved⟩)) ?_
  rintro u ⟨only, saved⟩ symU
  rw [WP.seq_iff]
  refine WP.mono (scan_ok (src := src) (table := s.syms tableSym) (k := k) (dom := dom) groups 0 u ?_ ?_ ?_ fit) ?_
  · exact ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
      (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
      by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
  · rw [symU]
  · have after := table.after only.mem (show Keep [.r12] s u from ⟨only.gpr, only.rd, only.wr⟩)
    rw [symU] at *
    simpa only [BitVec.add_zero] using after
  · rintro v ⟨value, memV, restV⟩
    refine VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mtlr fun w regs memW rdW wrW spW lrW =>
      VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil ⟨by rw [regs, value], memW.trans (memV.trans only.mem), ?_,
        by rw [lrW, restV.gpr (by decide), saved]⟩
    refine ⟨?_, rdW.trans (restV.2.1.trans only.rd), wrW.trans (restV.2.2.trans only.wr)⟩
    intro r hr
    rw [regs, restV.gpr (by intro hc; exact hr (List.mem_cons_of_mem _ hc)),
      only.gpr r (by simpa only [allClobbers, List.mem_cons, List.not_mem_nil, or_false] using
        (fun eq : r = .r12 => hr (by rw [eq]; exact List.mem_cons_self))) ]

/-- What `recognize`'s timing depends on. -/
def RI (src : Addr) (k : Nat) (dom : List Byte) (tbl stack : Addr) (s : State) : Prop :=
  Context src k dom s ∧ s.syms tableSym = tbl ∧ TableAt tbl groups s ∧ s.sp = stack

theorem recognize_ct' (src : Addr) (k : Nat) (dom : List Byte) (tbl stack : Addr) :
    RelCT isa (fun s t => RI src k dom tbl stack s ∧ RI src k dom tbl stack t) recognize (fun _ _ => True) := by
  let Q := fun s : State => Context src k dom s ∧ s.syms tableSym = tbl ∧ TableAt tbl groups s ∧ s.sp = stack
  have entryCT : RelCT isa (fun s t => RI src k dom tbl stack s ∧ RI src k dom tbl stack t)
      (.block [.mflr .r12]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t h
    exact ⟨h.1.2.2.2.trans h.2.2.2.2.symm, by simp [Taint.ofRegs]⟩
  have entryWP (s : State) (h : RI src k dom tbl stack s) : WP isa (.block [.mflr .r12]) s Q := by
    refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
      (Q := fun t : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s t)
      (fun t only _ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil only)) ?_
    intro t only sym
    obtain ⟨input, hsym, table, hsp⟩ := h
    have ctx : Context src k dom t :=
      ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
        (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
        by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
    exact ⟨ctx, (congrFun sym tableSym).trans hsym,
      table.after only.mem (show Keep [.r12] s t from ⟨only.gpr, only.rd, only.wr⟩), only.sp.trans hsp⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 15 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (src := src) (table := tbl)
    (stack := stack) (k := k) (dom := dom) groups 0 fit valid).mono
    (P' := fun s t => Q s ∧ Q t)
    (fun _ _ h => by simpa only [BitVec.add_zero] using h) (fun _ _ h => h)
  have scanStage := ((entryCT.wp (fun s t h => ⟨entryWP s h.1, entryWP t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2⟩)).seq scanning
  have restoreCT : RelCT isa (fun _ _ => True) (.block [.mtlr .r12]) (fun _ _ => True) := by
    intro s t ts tt u v _ es et
    have niltrace {s t : State} {tr : List Leak} (e : Exec isa (.block [.mtlr .r12]) s tr t) : tr = [] := by
      cases e with
      | block e =>
        simp only [execBlock, isa, exec, addrs, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at e
        exact e.2.symm
    exact ⟨(niltrace es).trans (niltrace et).symm, trivial⟩
  unfold recognize
  exact (scanStage.seq restoreCT).assoc

end VG.Proof.Ffdh.PPC64LE.VettedValidation
