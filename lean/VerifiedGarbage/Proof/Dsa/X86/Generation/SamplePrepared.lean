module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.MillerRabin.Workspace
public import VerifiedGarbage.Proof.MillerRabin.ReusableKeeps
import VerifiedGarbage.Proof.Framework.Offset

/-! Sampling leaves every byte of the shared round workspace unchanged. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont

theorem sample_keeps {s t : State} {base : Addr} (F : SampleFrame base s t) (n : Nat) :
    Spec.MillerRabin.Keeps Spec.MillerRabin.compact (off base Layout.arithmetic) 1536 n s.mem t.mem := by
  intro i hi _ _ _
  exact F.bytes (R := ⟨off base Layout.arithmetic, 12288⟩)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base base (by omega) (by decide)) (by change 12288 ≤ 2 ^ 64; decide) hi

theorem sample_prepared {s t : State} {base : Addr}
    (F : SampleFrame base s t)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic)) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) 1536 ∧
      Spec.MillerRabin.Prepared Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) =
        Spec.Rsa.Mont.wOf s.mem (off base Layout.arithmetic) := by
  apply VG.Proof.MillerRabin.Workspace.workspace_congr ?_ L P
  intro i hi
  exact F.bytes (R := ⟨off base Layout.arithmetic, 12288⟩)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base base (by omega) (by decide)) (by change 12288 ≤ 2 ^ 64; decide) hi

theorem sample_core {s t : State} {base : Addr}
    (F : SampleFrame base s t)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : VG.Proof.MillerRabin.PreparedCore s.mem (off base Layout.arithmetic)) :
    Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) 1536 ∧
      VG.Proof.MillerRabin.PreparedCore t.mem (off base Layout.arithmetic) := by
  exact P.kept L (sample_keeps F _)

end VG.Proof.Dsa.X86.Generation
