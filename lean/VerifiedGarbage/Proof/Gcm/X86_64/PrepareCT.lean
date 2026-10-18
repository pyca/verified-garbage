module

public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare
meta import VerifiedGarbage.Impl.Gcm.X86_64.Prepare
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# Preparing a key context's powers in place: the contract on the registers

`prepareX86_64`, `vg_aes_gcm_prepare`'s contract on the registers, and its
constant time (`prepare_ct`): only the context's address affects timing. The
field, where the powers are proven, is in `Stitch/Ok.lean`, so that its
algebra reaches no new module.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepare

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Prepare (prepare)

/-- `vg_aes_gcm_prepare`'s contract, on the registers. -/
def prepareX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1024⟩] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem prepare_ct : ConstantTime isa prepareX86_64.pre prepareX86_64.pub prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

end VG.Proof.Gcm.X86_64.Prepare
