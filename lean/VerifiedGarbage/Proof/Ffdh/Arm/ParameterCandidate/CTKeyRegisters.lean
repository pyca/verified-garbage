module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
public import VerifiedGarbage.Proof.Ffdh.Arm.RegistersCT

/-! RSA's compact array operations retain the three public workspace-view registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

def keyRegs : List Reg := [.r7, .r8, .r9]
def KeyRegEq (s t : State) : Prop := RegistersEqual keyRegs s t ∧ s.sp = t.sp

def keepsKeyRegs (code : Prog isa) : Bool :=
  (instrs code).all fun op => !(clobbers op .r7 || clobbers op .r8 || clobbers op .r9)

private theorem keyRegs_untouched {code : Prog isa} (kept : keepsKeyRegs code = true) :
    ∀ r ∈ keyRegs, ∀ op ∈ instrs code, clobbers op r = false := by
  intro r hr op hop
  have valid := List.all_eq_true.mp kept op hop
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at valid
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact valid.1.1
  · exact valid.1.2
  · exact valid.2

theorem keyRegs_keep_ct {P : State → State → Prop} {code : Prog isa}
    (trace : RelCT isa P code (fun _ _ => True))
    (publicRegs : ∀ s t, P s t → KeyRegEq s t)
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) :
    RelCT isa P code KeyRegEq :=
  registers_keep_ct keyRegs trace (fun s t h => (publicRegs s t h).1)
    (fun s t h => (publicRegs s t h).2) (keyRegs_untouched kept) noCalls

theorem keyRegs_stack_ct {code : Prog isa}
    (trace : RelCT isa (fun s t => s.sp = t.sp) code (fun s t => s.sp = t.sp))
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) : RelCT isa KeyRegEq code KeyRegEq :=
  registers_keep_ct keyRegs (trace.mono (fun _ _ h => h.2) (fun _ _ _ => trivial))
    (fun _ _ h => h.1) (fun _ _ h => h.2) (keyRegs_untouched kept) noCalls

theorem keyRegs_taint_ct {code : Prog isa} (cert : CandidateCert keyRegs code)
    (kept : keepsKeyRegs code = true) (noCalls : code.noCalls = true) : RelCT isa KeyRegEq code KeyRegEq := by
  obtain ⟨hint, checked⟩ := cert
  have trace : RelCT isa KeyRegEq code (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs keyRegs) (fun _ _ h => Taint.agree_ofRegs h.1) checked
  exact registers_keep_ct keyRegs trace (fun _ _ h => h.1) (fun _ _ h => h.2) (keyRegs_untouched kept) noCalls

end VG.Proof.Ffdh.Arm.ParameterCandidate
