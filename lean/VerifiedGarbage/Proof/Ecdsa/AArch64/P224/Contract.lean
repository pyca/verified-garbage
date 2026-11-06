module

public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P224.Tables
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-224 on AArch64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P224.inst` for AArch64, under the
calling convention with the comb's tables (`Abi.withConsts p224.combConsts`),
by name: `vg_ecdsa_p224_sign(out = x0, d = x1, digest = x2, k = x3,
scratch = x4)`, the result in `w0`, and the tables at the address of the
static `p224.tsym`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.P224

open VG VG.AArch64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.AArch64 (p224)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P224.curve (ofBytes (bytesAt m d 28)) (hashToInt Spec.P224.curve (bytesAt m digest 28))
    (ofBytes (bytesAt m k 28))

def signAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 56⟩
    let d : Region := ⟨s.gpr .x1, 28⟩
    let digest : Region := ⟨s.gpr .x2, 28⟩
    let k : Region := ⟨s.gpr .x3, 28⟩
    let scratch : Region := ⟨s.gpr .x4, 8192⟩
    s.rd = [d, digest, k, ⟨s.syms p224.tsym, 8 * p224.combWords.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      (s.gpr .x0).toNat + 56 ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch]
  post s s' :=
    match sig s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 56 = encode Spec.P224.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 56 = List.replicate 56 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    s₁.syms p224.tsym = s₂.syms p224.tsym

end VG.Proof.Ecdsa.AArch64.P224
