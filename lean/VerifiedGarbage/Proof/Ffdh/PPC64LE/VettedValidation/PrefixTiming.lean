module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.PublicState
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Ffdh.PPC64LE.VettedValidation

/-! Link-register preservation adds no secret-dependent trace to the public scan. -/

@[expose] public section
namespace VG.Proof.Ffdh.PPC64LE.VettedValidation
open VG VG.PPC64LE
open VG.Impl.Ffdh.PPC64LE.VettedValidation VG.Impl.Ffdh.VettedGroups

theorem recognize_ct (a : State) :
    RelCT isa (fun s t => Start a s ∧ Start a t) recognize (fun _ _ => True) := by
  let Q := fun s : State => Context (a.gpr .r3) (a.gpr .r5).toNat (domain a) s ∧
    s.syms tableSym = a.syms tableSym ∧ TableAt (a.syms tableSym) groups s ∧ s.sp = a.sp
  have entryCT : RelCT isa (fun s t => Start a s ∧ Start a t)
      (.block [.mflr .r12]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t h
    exact ⟨h.1.sp.trans h.2.sp.symm, by simp [Taint.ofRegs]⟩
  have entryWP (s : State) (h : Start a s) : WP isa (.block [.mflr .r12]) s Q := by
    refine WP.mono_syms (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_mflr
      (Q := fun t : State => VG.Proof.RsaPkcs1Sig.PPC64LE.Only [.r12] s t)
      (fun t only _ => VG.Proof.RsaPkcs1Sig.PPC64LE.wp_nil only)) ?_
    intro t only sym
    have input := context h.pre
    have ctx : Context (s.gpr .r3) (s.gpr .r5).toNat (domain s) t :=
      ⟨(only.get .r3).trans input.source, (only.get .r4).trans input.length,
        (only.get .r5).trans input.width, by rw [only.rd, only.wr]; exact input.read,
        by rw [only.mem]; exact input.bytes, input.shape, input.lower, input.upper⟩
    rw [h.regs .r3 (by decide), h.regs .r5 (by decide), h.domain] at ctx
    have table := (consts_table (pre_plain h.pre).2).after only.mem
      (show Keep [.r12] s t from ⟨only.gpr, only.rd, only.wr⟩)
    rw [h.symbol] at table
    exact ⟨ctx, (congrFun sym tableSym).trans h.symbol, table, only.sp.trans h.sp⟩
  have fit : 0 + (groups.flatMap Group.bytes).length ≤ 17744 := by
    simpa only [Nat.zero_add, tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length)
  have valid : ∀ g ∈ groups, g.len < 2 ^ 15 := by
    intro g hg
    simp only [groups, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have scanning := (scan_ct (src := a.gpr .r3) (table := a.syms tableSym)
    (stack := a.sp) (k := (a.gpr .r5).toNat) (dom := domain a) groups 0 fit valid).mono
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
