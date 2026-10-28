module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClose
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveGeometry
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateCloseTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieveInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput

/-! # Live candidate inputs satisfy the timing preconditions of every prefilter -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem load_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (InputPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateLoad.code E.width) (fun _ _ => True) := by
  have space : 32 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  exact (CandidateLoad.code_trace space E.width).mono (fun _ _ P =>
    ⟨P.left.scratch, P.right.scratch, P.left.stack.trans P.right.stack.symm,
      P.left.rand_eq.trans P.right.rand_eq.symm⟩) (fun _ _ _ => trivial)

theorem close_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateClose.code E.width) (fun _ _ => True) := by
  have space : 28 ≤ E.size := by have H : 256 ≤ E.size := v.geometry.headerFit; omega
  refine (CandidateClose.code_trace (base := E.base) space E.width).mono (fun _ _ P => ?_) (fun _ _ _ => trivial)
  exact ⟨⟨P.left.input.scratch, P.right.input.scratch, P.left.input.stack.trans P.right.input.stack.symm,
    P.left.input.other_eq.trans P.right.input.other_eq.symm⟩,
    (P.left.input.header 6 (by decide)).trans (P.right.input.header 6 (by decide)).symm⟩

theorem exponent_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code (fun _ _ => True) :=
  CandidateExponent.code_trace.mono (fun _ _ P => ⟨P.left.exponentInitial v, P.right.exponentInitial v⟩) (fun _ _ _ => trivial)

theorem Drawn.sieveEntry {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) : CandidateSieve.Entry E.sieveGeometry (candidateValue E entropy) (allocFrame 20 s) := by
  refine ⟨sieve_context v D, ?_, D.input.memory.symbol⟩
  rw [allocFrame_gpr _ _ (by decide)]
  change s.gpr .edi + 256#32 = E.workspace + 256#32
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [D.input.scratch.edi_toNat]
  change (E.workspace.setWidth 64).toNat = E.workspace.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans E.workspace.isLt (by decide))]

theorem sieve_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (pattern : Sieve.SamePattern E.sieveGeometry (candidateValue E rBytes) (candidateValue E sBytes)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width) (fun _ _ => True) := by
  have privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar E.workspaceRegion
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar E.tableRegion
    (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact (CandidateSieve.code_trace v.sieve_valid pattern rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega)]; have := v.low; omega)
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)).mono
    (fun _ _ P => ⟨P.left.sieveEntry v, P.right.sieveEntry v⟩) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.Candidate
