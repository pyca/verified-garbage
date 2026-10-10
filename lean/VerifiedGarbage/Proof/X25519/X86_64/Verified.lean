import VerifiedGarbage.Proof.X25519.X86_64.Main
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# X25519 on x86-64: `Verified`

Correct as its code with `vg_gf25519_r64_invert`'s inlined, constant time (by
taint tracking, which follows the call: the only branches are on the loop
counters, and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/` with 8 bytes of stack, for
the call's return address (`Verified.of_inline_ct`).
-/

namespace VG.Proof.X25519.X86_64

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
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_implies : Proof.X25519.x25519X86_64.Implies (Spec.X25519.x25519Contract X86_64.abi) := by
  sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
    Proof.X25519.x25519X86_64] [satState] using satState

/-- The contract with 8 bytes of stack, for the call's return address. -/
theorem x25519_implies8 : Proof.X25519.x25519X86_64.Implies (Spec.X25519.x25519Contract X86_64.abi 8) :=
  x25519_implies.stack8_abi (by
    sig_implies_sat [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      satState] [satState] using satState)

/-- The output is apart from the call's return address. -/
theorem x25519_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.X25519.x25519Contract X86_64.abi 8).pre s) (hp : Proof.X25519.x25519X86_64.post s b) :
    Proof.X25519.x25519X86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := x25519_implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 32)
    (by rw [hwr]; simp) (by decide)
  show Spec.X25519.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 32 = _
  rw [show Spec.X25519.bytesAt (b.patch _ hv u).mem (s.gpr .rdi) 32 =
    Spec.X25519.bytesAt b.mem (s.gpr .rdi) 32 from bytes_patch hb]
  exact hp

/-- The arguments and `rsp` are public. -/
theorem x25519_agree (s₁ s₂ : State) (hp : Proof.X25519.x25519X86_64.pub s₁ s₂) :
    X86_64.Taint.Agree (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) s₁ s₂ := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hp
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519_inlineOk : Impl.X25519.X86_64.x25519.InlineOk = true := by lit_decide

theorem x25519_ok [DivstepInv] (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519.inline s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct baseline_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre Proof.X25519.x25519X86_64.pub
    Impl.X25519.X86_64.x25519 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun s₁ s₂ _ _ hp => x25519_agree s₁ s₂ hp) (by taint_decide)

theorem x25519_verified [DivstepInv] :
    Verified X86_64.target Impl.X25519.X86_64.x25519 (Spec.X25519.x25519Contract X86_64.abi 8) :=
  Verified.of_inline_ct x25519_inlineOk x25519_ok x25519_ct x25519_implies8
    (fun _ h => Sig.clear_of_pre h) x25519_patch

end VG.Proof.X25519.X86_64
