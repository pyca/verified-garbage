module

public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-!
# ECDSA over P-256 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P256.inst` for x86-64, under the
calling convention with the comb's tables (`Abi.withConsts p256.combConsts`),
by name: `vg_ecdsa_p256_sign(out = rdi, d = rsi, digest = rdx, k = rcx,
scratch = r8)`, the result in `eax`, and the tables at the address of the
static `VG_P256_COMB`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa
open VG.Impl.Ecdsa.X86_64 (p256)

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P256.curve (ofBytes (bytesAt m d 32)) (hashToInt Spec.P256.curve (bytesAt m digest 32))
    (ofBytes (bytesAt m k 32))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 64⟩
    let d : Region := ⟨s.gpr .rsi, 32⟩
    let digest : Region := ⟨s.gpr .rdx, 32⟩
    let k : Region := ⟨s.gpr .rcx, 32⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k, ⟨s.syms "VG_P256_COMB", 8 * p256W.length⟩] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧ TblHeld s [out, scratch, ret]
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.syms "VG_P256_COMB" = s₂.syms "VG_P256_COMB"

end VG.Proof.Ecdsa.X86_64
