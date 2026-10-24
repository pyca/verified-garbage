module

public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
import VerifiedGarbage.Proof.Framework.X86_64.CallBody
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # Share the domain checker without changing its arithmetic -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Layout

abbrev domainReturn (s : State) : Region := below (s.gpr .rsp) 8

theorem domainEntry_frame (s : State) : Frame [domainReturn s] s.mem s.callEntry.mem := by
  exact (Frame.refl _ _).writeW (r := domainReturn s) (by simp) _ (below_call _ (by decide) (by decide))

theorem parameters_callEntry {p : ParametersInput} {s : State} (h : ParametersPre p s)
    (hp : (domainReturn s).Disjoint ⟨s.gpr .rdi, p.params.length⟩) :
    ParametersPre p s.callEntry := by
  have hlen : p.params.length < 2 ^ 64 := by
    rw [p.paramsLength]
    have hl := p.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  refine ⟨h.scratch.congr rfl, ?_, ?_, ?_, ?_⟩
  · exact (State.callEntry_gpr s (by decide)).trans h.base
  · exact (State.callEntry_gpr s (by decide)).trans h.pLength
  · exact (State.callEntry_gpr s (by decide)).trans h.qLength
  · rw [State.callEntry_gpr s (by decide)]
    refine ⟨h.paramsSource.rd, ?_, h.paramsSource.out⟩
    intro i hi
    rw [domainEntry_frame s _ (by
      intro r hr hrx
      obtain rfl := List.mem_singleton.mp hr
      exact hp _ hrx (Offset.contains_base _ (by omega) (by omega))) ]
    exact h.paramsSource.val i hi

theorem domainCall_ok (M : Mont) (Sq : MontS) {name : String} {p : ParametersInput} {s : State}
    (h : ParametersPre p s)
    (hs : (domainReturn s).Disjoint ⟨p.base, usedBytes⟩)
    (hp : (domainReturn s).Disjoint ⟨s.gpr .rdi, p.params.length⟩) :
    WP isa (.call name (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm)) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 0) ∧
      Frame [⟨p.base, usedBytes⟩, domainReturn s] s.mem t.mem ∧ Keep coreRegs s t := by
  apply WP.callBody
  refine WP.mono (parametersMain_ok M Sq (parameters_callEntry h hp)) ?_
  intro u ⟨result, _, frame, keep⟩
  have hsp := keep.gpr (r := .rsp) (by decide)
  have fr : Frame [⟨p.base, usedBytes⟩] s.callEntry.mem u.mem := by
    intro a ha
    apply frame a
    have hn := ha ⟨p.base, usedBytes⟩ (by simp)
    change ¬ ofs p.base a < usedBytes at hn
    omega
  have hr : u.mem.readW (s.gpr .rsp - 8) 64 = s.unknowns 0 := by
    rw [fr.readW (r := domainReturn s) (below_call _ (by decide) (by decide))
      (by intro r h; obtain rfl := List.mem_singleton.mp h; exact hs) (by decide),
      State.callEntry_mem, Mem.readW_writeW_self64]
  refine ⟨hsp, hr, ?_, ?_, ?_⟩
  · simpa only [State.setReg, reduceCtorEq, ite_false] using result
  · exact (domainEntry_frame s |>.mono (by simp)).trans (fr.mono (by simp))
  · refine ⟨?_, keep.2.1, keep.2.2⟩
    intro r hr
    by_cases h : r = .rsp
    · subst r; simp [State.setReg]
    · simp only [State.setReg, h, ite_false]
      exact (keep.gpr hr).trans (State.callEntry_gpr s h)

end VG.Proof.Dsa.X86_64.Generation
