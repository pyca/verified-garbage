import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Impl.AesSiv.X86_64
import VerifiedGarbage.Spec.Siv

/-!
# AES-SIV on x86-64: `vg_aes_siv_init`'s contract for its proof

The artifact's contract is the shared one of `Spec/Siv/Contract.lean`, which
implies this (`Verified.lean`). The function calls functions that call
`vg_aes_ctr32`: the two return addresses are in the 16 bytes below the stack
pointer, which may not overlap any buffer. `encrypt`'s and `decrypt`'s proofs
are against `EPre` instead (`Enc.lean`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64

/-- `vg_aes_siv_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 512⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 32 ∨ (s.gpr .rsi).toNat = 48 ∨ (s.gpr .rsi).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (s.gpr .rdx) (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.AesSiv.X86_64
