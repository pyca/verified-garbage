module

public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA's probable-prime test on ARMv7: the stack it uses

The 32-byte allocation and the 56 bytes of registers pushed, then the round's
own stack (`code_stack`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Impl.Dsa.Arm.ProbablePrime
open VG.Impl.Rsa.Arm.Keys (seqs)
open VG.Arm.FrameStack (armStack)

theorem seqs_le {B : Nat} : ∀ l : List (Prog isa), (∀ c ∈ l, armStack c ≤ B) → armStack (seqs l) ≤ B
  | [], _ => Nat.zero_le _
  | [c], h => h c (by simp)
  | c :: d :: l, h => by
    simp only [seqs, armStack]
    exact Nat.max_le.mpr ⟨h c (by simp), seqs_le (d :: l) fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

theorem z_loadC : ∀ c ∈ loadC, armStack c = 0 := by decide
theorem z_trial : ∀ c ∈ VG.Impl.RsaKeyGen.Arm.Candidate.trial, armStack c = 0 := by decide
theorem z_exp : ∀ c ∈ VG.Impl.RsaKeyGen.Arm.Candidate.expSetup, armStack c = 0 := by decide
theorem z_wl : ∀ c ∈ witnessLoad ++ witnessFix, armStack c = 0 := by decide

theorem z_le {c : Prog isa} {B : Nat} (h : armStack c = 0) : armStack c ≤ B := h ▸ Nat.zero_le _

theorem body_stack (name : String) (round : Prog isa) : armStack (body name round) ≤ armStack round := by
  unfold body
  refine seqs_le _ fun c hc => ?_
  simp only [List.mem_append, List.mem_singleton] at hc
  rcases hc with (hc | hc) | rfl
  · exact z_le (z_loadC c hc)
  · exact z_le (z_trial c hc)
  refine Nat.max_le.mpr ⟨?_, Nat.zero_le _⟩
  unfold mrPart
  refine seqs_le _ fun c hc => ?_
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, false_or] at hc
  rcases hc with rfl | hc | rfl | rfl | rfl | rfl
  · exact z_le (by decide)
  · exact z_le (z_exp c hc)
  · exact z_le (by decide)
  · exact z_le (by decide)
  · unfold millerRabin mrBody
    simp only [armStack, seqs, Nat.zero_max, Nat.max_zero]
    refine seqs_le _ fun c hc => ?_
    simp only [List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · exact z_le (z_wl c (List.mem_append_left _ hc))
    · exact z_le (z_wl c (List.mem_append_right _ hc))
    · simp only [VG.Impl.RsaKeyGen.Arm.Candidate.mrCall, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact z_le (by decide)
      · exact Nat.le_refl _
      · exact z_le (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact z_le (by decide)
      · exact z_le (by decide)
  · exact z_le (by decide)

theorem code_stack (name : String) (round : Prog isa) :
    armStack (code name round) ≤ 88 + armStack round := by
  have := body_stack name round
  simp only [code, armStack, List.length_cons, List.length_nil, Nat.zero_max, Nat.max_zero]
  omega

end VG.Proof.Dsa.Arm.Prime
