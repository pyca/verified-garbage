module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.Accepted

import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.X86.GenerateSubgroup
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The generation checks implement the shared domain predicate -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem generationChecks_spec {p q g : Nat} (H : shapeValid p q) :
    ((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ↔
      Spec.Dsa.parametersValid ⟨p, q, g⟩ := by
  have B := supported_bounds H.1
  simp only [Spec.Dsa.parametersValid, powMod_eq]
  constructor
  · rintro ⟨G, D, P⟩
    exact ⟨H.1, H.2.2, H.2.1, B.2.2, D, G.1, G.2, P⟩
  · rintro ⟨_, _, _, _, D, Glo, Ghi, P⟩
    exact ⟨⟨Glo, Ghi⟩, D, P⟩

theorem generateParameters_ok {base : Addr} {size pLen qLen p q g : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g) :
    WP isa (Generate.parameters pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 ((1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1) ∧
      Execution base s0 sf := by
  unfold Generate.parameters
  refine WP.seq (WP.mono (generateDomain_ok M G hg) fun s1 ⟨M1, F1, E1⟩ => ?_)
  refine WP.mono (generateSubgroup_ok M1 (E1.buffer G (by decide))
    ((E1.value G (by decide) M.extent).trans hg)) fun sf ⟨Mf, Ff, Ef⟩ => ?_
  refine ⟨Mf, ?_, E1.trans Ef⟩
  rw [Ff, F1]
  simp only [BitVec.and_assoc, mask32_and, and_assoc]

end VG.Proof.Dsa.X86
