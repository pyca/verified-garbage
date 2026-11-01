module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.At
import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified

/-! # `vg_rsa_mont_mul_at` on x86 with SSE2: verified

Two runs from states with the same public arguments compute the same
numbers (`atReady`), so `body_relCT` makes them leak the same; the witness of
the scalar function's precondition, whose stack is far from its working
space, meets this one's too.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Rsa.MontMul (Apart numAt scratchBytes)

theorem at_publicArgs {s t : State} (H : (Proof.Rsa.MontMul.mulContract abi 56).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 9, arg s i = arg t i := by
  sig_pub [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  refine ⟨by with_reducible assumption, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => with_reducible assumption
  | 1, _ => with_reducible assumption
  | 2, _ => with_reducible assumption
  | 3, _ => with_reducible assumption
  | 4, _ => with_reducible assumption
  | 5, _ => with_reducible assumption
  | 6, _ => with_reducible assumption
  | 7, _ => with_reducible assumption
  | 8, _ => with_reducible assumption

theorem at_constantTime :
    ConstantTime isa (Proof.Rsa.MontMul.mulContract abi 56).pre (Proof.Rsa.MontMul.mulContract abi 56).pub atBody := by
  apply RelCT.constantTime
  refine RelCT.mono (P := fun s₁ s₂ => ∃ W L N S mo inv o a b, BPair atParams W L N S mo inv o a b s₁ s₂)
    (RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ => RelCT.exists_ fun _ =>
      RelCT.exists_ fun _ => body_relCT (fun _ _ h => h) (atParams_relCT.mono (fun _ _ ⟨_, _, B, ex, ey⟩ => by
        rw [ex, ey, pushed_esp, pushed_esp, B.2.2]) fun _ _ _ => trivial)) ?_ fun _ _ _ => trivial
  rintro s₁ s₂ ⟨h₁, h₂, hp⟩
  obtain ⟨sp, args⟩ := at_publicArgs hp
  have R := atReady (atAbi_of h₂)
  simp only [wsOf, lenOf, nAt, ← args 0 (by decide), ← args 1 (by decide), ← args 2 (by decide),
    ← args 3 (by decide), ← args 4 (by decide), ← args 5 (by decide), ← args 6 (by decide),
    ← args 7 (by decide), ← args 8 (by decide)] at R
  exact ⟨_, _, _, _, _, _, _, _, _, atReady (atAbi_of h₁), R, sp⟩

theorem at_satisfiable : ∃ s, (Proof.Rsa.MontMul.mulContract abi 56).pre s := by
  refine ⟨satState, ?_⟩
  have a : ∀ i, i < 9 → arg satState i = satArg i := satArg_eq
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  have a6 := a 6 (by decide); have a7 := a 7 (by decide); have a8 := a 8 (by decide)
  simp only [satArg, List.getD_cons_succ, List.getD_cons_zero] at a0 a1 a2 a3 a4 a5 a6 a7 a8
  have e0 : argAddr satState 0 = 0xf0000004 := by decide
  have hw : BitVec.setWidth 64 (4096 : BitVec 32) = 4096 := by decide
  have hsp : BitVec.setWidth 64 (0xf0000000 : BitVec 32) = 0xf0000000 := by decide
  sig_pre [Proof.Rsa.MontMul.mulContract, Proof.Rsa.MontMul.sig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, e0, hw, hsp]
  sig_and_intros
  all_goals try decide
  all_goals try exact Region.disjoint_of_sep (by decide)
  all_goals try (simp only [Apart, scratchBytes]; decide)
  all_goals try (rw [show (4096 : Addr) = 0x1000 from rfl, satModulus, satInv]; decide)
  all_goals try (rw [show (4096 : Addr) = 0x1000 from rfl, satModulus, satB]; decide)

theorem at_verified : Verified target atBody (Proof.Rsa.MontMul.mulContract abi 56) :=
  ⟨at_correct, at_constantTime, at_satisfiable⟩

end VG.Proof.Mont.X86.Sse2
