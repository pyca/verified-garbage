module

public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86_64

/-!
# ECDSA over brainpoolP512r1 on x86-64: the contract the proof is written against

The facts of `Proof.Ecdsa.Instance.signContract Spec.Ecdsa.BrainpoolP512r1.inst` for x86-64, by name:
`vg_ecdsa_brainpoolp512r1_sign(out = rdi, d = rsi, digest = rdx, k = rcx, scratch = r8)`,
the result in `eax`, with the comb's tables (`brainpoolp512r1S.combConsts`, the
static `VG_BRAINPOOLP512R1_COMB`) readable where the calling convention says.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.BrainpoolP512r1.curve (ofBytes (bytesAt m d 64)) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64))
    (ofBytes (bytesAt m k 64))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 128⟩
    let d : Region := ⟨s.gpr .rsi, 64⟩
    let digest : Region := ⟨s.gpr .rdx, 64⟩
    let k : Region := ⟨s.gpr .rcx, 64⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ++ Abi.constRegions (fun n => s.syms n) Impl.Ecdsa.X86_64.brainpoolp512r1S.combConsts ∧
      s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64 ∧
      TblsHeld Impl.Ecdsa.X86_64.brainpoolp512r1S s [out, scratch, ret]
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 128 = encode Spec.BrainpoolP512r1.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 128 = List.replicate 128 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    ∀ c ∈ Impl.Ecdsa.X86_64.brainpoolp512r1S.combConsts, s₁.syms c.1 = s₂.syms c.1

end VG.Proof.Ecdsa.X86_64.BrainpoolP512r1
