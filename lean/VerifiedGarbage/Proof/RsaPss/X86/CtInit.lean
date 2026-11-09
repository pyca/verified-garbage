module

public import VerifiedGarbage.Proof.RsaPss.X86.CtBase
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, the callees' stack

The 48 bytes below the stack pointer, where the calls of the hash
function's code put their frames, are in our callees' stack (`stk_low`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.Pbkdf2.Stream.X86 (InitArgs After init_frame init_rel stk)

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- The 48 bytes below the stack pointer, where a call's frame goes, are in
our callees' stack. -/
theorem stk_low (hg : Geo L scr) {σ s : State} (hc : Ctx L scr σ s) : Region.Sub (stk s) L.LOW := by
  have hC := hg.C48
  have ok := hc.st.ok
  rw [stk, hc.st.sp, ← ok.low_eq]
  exact below_sub hC ok.BC

/-- `esp` and `ebp` agree in two states of the body. -/
theorem sp_bp {F : State → State → Prop} (hF : ∀ σ s, F σ s → Ctx L scr σ s) :
    ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → ∀ r ∈ [Reg.esp, .ebp], s₁.gpr r = s₂.gpr r :=
  fun _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hF _ _ h₁).st.sp, (hF _ _ h₂).st.sp]
    · rw [(hF _ _ h₁).ebp, (hF _ _ h₂).ebp]

end VG.Proof.RsaPss.X86
