module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Unsigned length comparisons for entropy requests. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)

theorem less_ok (s : State) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.less) s fun t =>
      (t.z = decide ((s.gpr .r9).toNat < (s.gpr .r10).toNat) ∧ t.mem = s.mem) ∧
        Rest [.r11] s t := by
  refine withRest [.r11] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterSearch.less : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.less
  by_cases ge : (s.gpr .r10).toNat ≤ (s.gpr .r9).toNat
  · have lt : ¬ (s.gpr .r9).toNat < (s.gpr .r10).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]
  · have lt : (s.gpr .r9).toNat < (s.gpr .r10).toNat := by omega
    ffrun [ge, lt, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add]

end VG.Proof.Ffdh.Arm.ParameterSearch
