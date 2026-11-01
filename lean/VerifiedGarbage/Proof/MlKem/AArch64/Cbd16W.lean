module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Step
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16W.Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-!
# `vg_mlkem16_cbd2` on AArch64

`Impl.MlKem.AArch64.Cbd16.code16` meets `Proof.MlKem.cbd2_16Contract`: the
loop writes the two bytes of each coefficient (`Inv.out`), which are the
coefficient stored with 16 bits (`polyIsW16_of_bytes`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16W

open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Cbd16 (code16)

theorem correct (s : State) (hs : cbd2_16AArch64.pre s) :
    ∃ t s', Exec isa code16 s t s' ∧ abiPreserved s s' ∧ cbd2_16AArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, hi⟩ := loop_ok (s₀ := s) ⟨h1, h2, h3⟩
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, polyIsW16_of_bytes' hi.out⟩

theorem ct : ConstantTime isa cbd2_16AArch64.pre cbd2_16AArch64.pub code16 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 512⟩]

theorem verified : Verified AArch64.target code16 (Proof.MlKem.cbd2_16Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Proof.MlKem.cbd2_16Contract, Proof.MlKem.cbd2_16Sig, cbd2_16AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Cbd16W
