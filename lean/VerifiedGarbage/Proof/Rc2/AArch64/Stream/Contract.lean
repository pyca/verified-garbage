module

public import VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime
public import VerifiedGarbage.Spec.Rc2.Contract

/-! # Streaming RC2-CBC on AArch64: the contracts the proofs use

`Spec.Rc2.cbcInitContract` spelled out for AArch64 (the arguments in
`x0`–`x6`), with the 16-byte frame below the stack pointer that saves `x30`
around the call. -/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Stream

open VG VG.AArch64

/-- `init(key = x0, key_len = x1, effective_bits = x2, iv = x3, iv_len = x4,
ctx = x5, scratch = x6)`. -/
def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let iv : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let ctx : Region := ⟨s.gpr .x5, 144⟩
    let scr : Region := ⟨s.gpr .x6, 576⟩
    let stk : Region := ⟨s.sp - 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.rd = [key, iv] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      stk.Disjoint key ∧ stk.Disjoint iv ∧ stk.Disjoint ctx ∧ stk.Disjoint scr ∧
      (s.gpr .x5).toNat + 144 ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + 576 ≤ 2 ^ 64
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
        (Spec.Rc2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) direction (s.gpr .x2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .x0) = 0 ∧ Spec.Rc2.contextAt s'.mem (s.gpr .x5) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .x0)).toNat = e.code
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6]

end VG.Proof.Rc2.AArch64.Stream
