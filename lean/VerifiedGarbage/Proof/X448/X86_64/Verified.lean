import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# X448 on x86-64: `Verified`

Correct as its code with `vg_gf448_r64_pow223`'s inlined (`correct_inline`),
constant time (by taint tracking, which follows the call: the only branches
are on the loop counters, and every address is an argument plus a constant or
a counter), satisfiability, and the shared contract of `Spec/` with 8 bytes
of stack, for the call's return address (`Verified.of_inline_ct`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_inlineOk : Impl.X448.X86_64.x448.InlineOk = true := by lit_decide

theorem x448_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448.inline s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_inline (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448_implies : Proof.X448.x448X86_64.Implies (Spec.X448.x448Contract X86_64.abi) := by
  sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs,
    Proof.X448.x448X86_64] [satState] using satState

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem x448_implies8 : Proof.X448.x448X86_64.Implies (Spec.X448.x448Contract X86_64.abi 8) :=
  x448_implies.stack8_abi (by
    sig_implies_sat [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs, satState]
      [satState] using satState)

/-- The output is apart from the call's return address. -/
theorem x448_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.X448.x448Contract X86_64.abi 8).pre s) (hp : Proof.X448.x448X86_64.post s b) :
    Proof.X448.x448X86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := x448_implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 56)
    (by rw [hwr]; simp) (by decide)
  show Spec.X448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 56 = _
  rw [show Spec.X448.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 56 = Spec.X448.bytesAt b.mem (s.gpr .rdi) 56
    from bytes_patch hb]
  exact hp

theorem x448_verified :
    Verified X86_64.target Impl.X448.X86_64.x448 (Spec.X448.x448Contract X86_64.abi 8) :=
  Verified.of_inline_ct x448_inlineOk x448_ok x448_ct x448_implies8 (fun _ h => Sig.clear_of_pre h)
    x448_patch

end VG.Proof.X448.X86_64
