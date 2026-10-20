module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Result

/-! # Paired sampler outcomes stated using the existing public specification -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure PairOutcomeW (w16 : Bool) (A B : List Byte) (p a b : Addr) (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (stepWrites p a b) s.mem t.mem
  reducedLeft : ReducedW (cw w16) t.mem a
  reducedRight : ReducedW (cw w16) t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAtW (cw w16) t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)

theorem PairPostW.outcome {w16 : Bool} {s t : State} {p seed a b : Addr} {i j k : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairPostW w16 (seedState s.mem seed i k) (seedState s.mem seed j k) p a b s t) :
    PairOutcomeW w16 (seedBytes s.mem seed i k) (seedBytes s.mem seed j k) p a b s t := by
  have ra := accepted_result hk hk256 h.left
  have rb := accepted_result hk hk256 h.right
  refine ⟨h.keep,h.frame,h.reducedLeft,h.reducedRight,?_,?_,?_⟩
  · rcases ra with ⟨_,ha⟩|⟨_,ha⟩
    · exact Or.inr ha
    · exact Or.inl ha
  · rcases rb with ⟨_,hb⟩|⟨_,hb⟩
    · exact Or.inr hb
    · exact Or.inl hb
  · rw [h.status]
    rcases ra with ⟨la,ha⟩|⟨la,ha⟩ <;> rcases rb with ⟨lb,hb⟩|⟨lb,hb⟩ <;>
      simp [ha,hb,la,lb]

end VG.Proof.MlKem.AArch64.Paired
