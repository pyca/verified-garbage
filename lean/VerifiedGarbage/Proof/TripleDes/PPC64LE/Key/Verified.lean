module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.ConstantTime
public import VerifiedGarbage.Spec.TripleDes.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Body
import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Lit

/-!
# Triple DES key expansion on PPC64LE, verified

The code writes only volatile registers and needs no working space, so it is
verified against `expandKeyContract` with no stack.
-/

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE

def contract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let output : Region := ⟨s.gpr .r5, 384⟩
    s.rd = [key] ∧ s.wr = [output] ∧ key.Disjoint output ∧
      Spec.TripleDes.validKey (s.gpr .r4).toNat
  post s s' := Spec.TripleDes.scheduleAt s'.mem (s.gpr .r5) =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub := PublicRegs [.r3, .r4, .r5]

/-- The registers the code writes: all volatile. -/
def written : List Reg := [.r0, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem expand_correct (s : State) (hs : contract.pre s) :
    WP isa Impl.TripleDes.PPC64LE.Key.expandKey s (contract.post s) := by
  obtain ⟨hrd, hwr, keyOutput, valid⟩ := hs
  have hp : Permissions s := by
    constructor
    · intro offset hoff
      rw [hrd, hwr]
      exact ⟨⟨s.gpr .r3, (s.gpr .r4).toNat⟩, by simp,
        Offset.contains_base _ hoff (by
          have bound := BitVec.isLt (s.gpr .r4)
          omega_using [hoff, bound])⟩
    · intro offset hoff
      rw [hwr]
      exact ⟨⟨s.gpr .r5, 384⟩, by simp, Offset.contains_base _ hoff (by omega_using [hoff])⟩
    · exact keyOutput
    · exact valid
  apply WP.mono (body_ok s s hp ⟨fun _ h => by omega, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩)
  intro s₂ h₂
  have result := h₂.schedule
  rw [← VG.Proof.TripleDes.expandKey_memory s.mem (s.gpr .r3) (s.gpr .r4).toNat valid] at result
  exact result

theorem correct (s : State) (hs : contract.pre s) :
    ∃ t s', Exec isa Impl.TripleDes.PPC64LE.Key.expandKey s t s' ∧ abiPreserved s s' ∧
      contract.post s s' := by
  obtain ⟨t, s', he, hpost, hkeep⟩ :=
    WP.keep written (expand_correct s hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, abiPreserved_of_keep he hkeep (by decide) (by lit_decide)
    (by rw [← Code.allInstrs_eq]; lit_decide), hpost⟩

def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 16 | .r5 => 0x2000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 384⟩]

theorem publicRegs_three (s₁ s₂ : State) : PublicRegs [.r3, .r4, .r5] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 := by simp [PublicRegs]

theorem verified : Verified target Impl.TripleDes.PPC64LE.Key.expandKey
    (Spec.TripleDes.expandKeyContract abi) := by
  refine Verified.of_correct correct (expandKey_constantTime _) ?_
  sig_implies [Spec.TripleDes.expandKeyContract, Spec.TripleDes.expandKeySig,
    Spec.TripleDes.expandKeyPre, Spec.TripleDes.expandKeyPost, abi, argRegs,
    contract, publicRegs_three] [satState] using satState

end VG.Proof.TripleDes.PPC64LE.Key
