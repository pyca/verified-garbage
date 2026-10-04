import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Siv/Contract.lean` (with `init`'s working space as
an argument, `Proof/AesSiv/Scratch.lean`), which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl); the shared contracts let the functions overwrite them
(`writeArgs`), which they do not: the proofs are on states where they are
read-only (`Verified.of_narrow`), so that the taint analysis knows they are
public.
-/

namespace VG.Proof.AesSiv.X86

open VG VG.X86

/-- `initCore(key, key_len, ctx, scratch)`: its calls push their four
arguments and the return address, and `vg_cmac_aes_subkeys`'s own calls
theirs, 48 bytes below `esp`. -/
def initX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let ctx : Region := ⟨(arg s 2).setWidth 64, 512⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 2560⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 48, 48⟩
    s.rd = [key, args] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ key.Disjoint args ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
      scr.Disjoint args ∧ ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 512 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 32 ∨ (arg s 1).toNat = 48 ∨ (arg s 1).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem ((arg s 2).setWidth 64) (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.AesSiv.X86
