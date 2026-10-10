import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Verified

/-!
# X25519 on x86-64 with BMI2 and ADX: `Verified`

The proof of `vg_x25519` (`Proof/X25519/X86_64/Verified.lean`) for the field
multiplications `adx` (`adx_ok`): correctness from `correct`, constant time by
taint tracking (the only branches are on the loop counters, and every address
is an argument plus a constant or a counter), satisfiability, and the shared
contract.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem x25519Adx_inlineOk : Impl.X25519.X86_64.x25519Adx.InlineOk = true := by lit_decide

theorem x25519Adx_ok [DivstepInv] (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Adx.inline s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct adx_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by rw [Code.allInstrs_inline]; lit_decide) he h.1, h.2⟩

theorem x25519Adx_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Adx :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun s₁ s₂ _ _ hp => x25519_agree s₁ s₂ hp) (by taint_decide)

theorem x25519Adx_verified [DivstepInv] :
    Verified X86_64.target Impl.X25519.X86_64.x25519Adx (Spec.X25519.x25519Contract X86_64.abi 8) :=
  Verified.of_inline_ct x25519Adx_inlineOk x25519Adx_ok x25519Adx_ct x25519_implies8
    (fun _ h => Sig.clear_of_pre h) x25519_patch

end VG.Proof.X25519.X86_64
