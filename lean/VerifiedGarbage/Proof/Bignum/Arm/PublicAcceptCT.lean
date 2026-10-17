module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicAccept
public import VerifiedGarbage.Proof.Bignum.Arm.InputCompareCT
public import VerifiedGarbage.Proof.Bignum.Arm.SaveAcceptanceCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Comparing and saving secret input acceptance reveals no acceptance decision -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicAccept_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} :
    RelCT isa (fun s t => PublicOperand base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicOperand base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.acceptInput (fun _ _ => True) := by
  let P := fun (s t : State) => PublicOperand base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicOperand base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have compare := relCT_keep_sp (inputCompare_ct.mono (P' := P)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)) (fun _ _ h => h.2.2)
  exact compare.seq saveAcceptance_ct

end VG.Proof.Bignum.Arm
