import VerifiedGarbage.Proof.Blowfish.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym

/-!
# Constant time

The pointers and the count of blocks are public, and so is everything the
code computes from them (the batches, the round counts, the addresses of the
P-array entries and of the S-boxes' planes): every address and branch. The
S-box indices are only ever `tbl`/`tbx` operands.
-/

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64

/-- Only the argument pointers and public integers agree. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.Blowfish.AArch64.encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decrypt_constantTime (pre : State → Prop) :
    ConstantTime isa pre (PublicRegs [.x0, .x1, .x2, .x3]) Impl.Blowfish.AArch64.decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

/-- The key's length and the pointers are public, and so is the table's
address; the key's bytes and everything computed from them are not. -/
theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (fun s₁ s₂ => PublicRegs [.x0, .x1, .x2] s₁ s₂ ∧
      s₁.syms Impl.Blowfish.AArch64.initSym = s₂.syms Impl.Blowfish.AArch64.initSym)
      Impl.Blowfish.AArch64.expandKey := by
  refine VG.Taint.constantTime (A := taintS [Impl.Blowfish.AArch64.initSym])
    (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hp, hs⟩
  exact ⟨⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩, fun n hn => by
    simp only [List.mem_singleton] at hn; subst hn; exact hs⟩

end VG.Proof.Blowfish.AArch64
