module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Impl.Rc2.X86.Stream
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

section

/-! # Streaming RC2-CBC on x86 (32-bit): prefixes of a region -/

namespace VG.Proof.Rc2.X86.Stream

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

end VG.Proof.Rc2.X86.Stream

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the contracts the proofs use

`Spec.Rc2.cbcInitContract` spelled out for x86, with the arguments only
read (the taint analysis follows them in memory only while nothing that may
alias them is written): `Verified.lean` moves the
proofs to the shared contracts, which let the code write them.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let iv : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let ctx : Region := ⟨(arg s 5).setWidth 64, 144⟩
    let buf : Region := ⟨(arg s 6).setWidth 64, 576⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 24
    s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
        (Spec.Rc2.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) direction (arg s 2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Rc2.contextAt s'.mem ((arg s 5).setWidth 64) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax)).toNat = e.code
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

end VG.Proof.Rc2.X86.Stream
