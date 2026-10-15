module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Pair
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Paired sampler outcomes stated using the existing public specification -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure PairOutcome (A B : List Byte) (p a b : Addr) (s t : State) : Prop where
  keep : Keep pairRegs s t
  frame : Frame (stepWrites p a b) s.mem t.mem
  reducedLeft : Reduced t.mem a
  reducedRight : Reduced t.mem b
  left : sampleNTT 280 A=none ∨ sampleNTT 280 A=some (polyAt t.mem a)
  right : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAt t.mem b)
  status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64
    (if (sampleNTT 280 A).isSome ∧ (sampleNTT 280 B).isSome then 1 else 0)

theorem PairPost.outcome {s t : State} {p seed a b : Addr} {i j k : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : PairPost (seedState s.mem seed i k) (seedState s.mem seed j k) p a b s t) :
    PairOutcome (seedBytes s.mem seed i k) (seedBytes s.mem seed j k) p a b s t := by
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
