module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.RandomContext
meta import VerifiedGarbage.Impl.Dsa.X86.Comb
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint

/-! The private comb scan body's addresses and branches depend only on public pointers
and fixed counts. All workspace values, including the exponent, are secret here. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

def privateInputs : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp, .esi], flags := false }

theorem private_scan_check {n e : Nat} (h : Supported n e) :
    (VG.Taint.check taint privateInputs (VG.Impl.Mont.X86.Comb.wordSelectBody n (context n+16*n)
        (VG.Impl.Mont.X86.Dynamic.slot n 7) 32)
      (VG.Taint.hintOf taint privateInputs (VG.Impl.Mont.X86.Comb.wordSelectBody n (context n+16*n)
        (VG.Impl.Mont.X86.Dynamic.slot n 7) 32))).map (taint.le privateInputs) = some true := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> taint_decide


theorem private_scan_body_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (VG.X86.Taint.Agree privateInputs)
      (VG.Impl.Mont.X86.Comb.wordSelectBody n (context n+16*n)
        (VG.Impl.Mont.X86.Dynamic.slot n 7) 32)
      (VG.X86.Taint.Agree privateInputs) := by
  obtain ⟨τ, checked, retained⟩ := Option.map_eq_some_iff.mp (private_scan_check h)
  exact VG.Proof.Dsa.X86.checkedProgramChange checked retained

private theorem allocated_state {bytes : Nat} {s a : State}
    (h : isa.push (.alloc bytes) s = some a) :
    a = VG.Proof.Dsa.X86.allocated bytes s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

private theorem freed_state {bytes : Nat} {s t a : State}
    (h : isa.pop (.free bytes) s t = some a) :
    a = VG.Proof.Dsa.X86.freed bytes t := by
  simp only [isa, pop] at h
  split at h <;> cases h
  rfl

/-- Allocation and release are handled by the ISA semantics: the checker
above covers the scan body without assuming support for alloc/free hooks. -/
theorem private_scan_relCT {n e : Nat} (h : Supported n e) :
    RelCT isa (VG.X86.Taint.Agree privateInputs)
      (VG.Impl.Mont.X86.Comb.wordSelect n (context n+16*n)
        (VG.Impl.Mont.X86.Dynamic.slot n 7) 32)
      (VG.X86.Taint.Agree privateInputs) := by
  intro s t ts tt s' t' agree es et
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have as := allocated_state ps
      have atEq := allocated_state pt
      subst as atEq
      have input : VG.X86.Taint.Agree privateInputs
          (VG.Proof.Dsa.X86.allocated 128 s) (VG.Proof.Dsa.X86.allocated 128 t) := by
        apply agree_regs
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact agree.rf.1 .edi (by decide)
        · simp only [VG.Proof.Dsa.X86.allocated_esp, agree.rf.1 .esp (by decide)]
        · exact agree.rf.1 .esi (by decide)
      obtain ⟨trace, output⟩ := private_scan_body_relCT h _ _ _ _ _ _ input bs bt
      have fs := freed_state qs
      have ft := freed_state qt
      subst fs ft
      refine ⟨?_, ?_⟩
      · rw [trace]; rfl
      · apply agree_regs
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact output.rf.1 .edi (by decide)
        · simp only [VG.Proof.Dsa.X86.freed_esp, output.rf.1 .esp (by decide)]
        · exact output.rf.1 .esi (by decide)

end VG.Proof.Dsa.X86.Comb
