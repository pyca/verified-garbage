import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Ladder
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr

/-!
# X25519 on x86-64 with AVX512_IFMA: `Verified`

The proof of `vg_x25519` (`Proof/X25519/X86_64/Main.lean`) with the ladder
`vladder` (`vladder_ok`) and the field multiplications `adx` for the
inversion's last product: correctness of the code with
`vg_gf25519_r64_invert`'s inlined from `correct_of`; MXCSR's control bits kept,
as the ladder loads MXCSR only between saving it in `r11` and loading it back
(`ctlOk`); constant time by taint tracking, which follows the call (the only
branches are on the loop counters, and every address is an argument plus a
constant or a counter); satisfiability, and the shared contract with 8 bytes
of stack, for the call's return address.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem vladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X25519.Fe} (h : LPre base k u s) :
    WP isa Impl.X25519.X86_64.Ifma.vladder s (LPost base k u s) :=
  Ifma.vladder_ok h.scr h.bits h.x1 h.swap

theorem x25519Ifma_inlineOk : Impl.X25519.X86_64.x25519Ifma.InlineOk = true := by lit_decide

theorem x25519Ifma_ok [DivstepInv] (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Ifma.inline s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct_of adx_ok (Code.inline_of_noCalls (by lit_decide)) vladder_post
    (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he h.1, h.2⟩

theorem x25519Ifma_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Ifma :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
    (fun s₁ s₂ _ _ hp => x25519_agree s₁ s₂ hp) (by taint_decide)

theorem x25519Ifma_verified [DivstepInv] :
    Verified X86_64.target Impl.X25519.X86_64.x25519Ifma (Spec.X25519.x25519Contract X86_64.abi 8) :=
  Verified.of_inline_ct x25519Ifma_inlineOk x25519Ifma_ok x25519Ifma_ct x25519_implies8
    (fun _ h => Sig.clear_of_pre h) x25519_patch

end VG.Proof.X25519.X86_64
