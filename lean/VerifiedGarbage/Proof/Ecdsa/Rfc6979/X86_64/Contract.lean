import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Generic
import VerifiedGarbage.Spec.Ecdsa.P256
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA over P-256 on x86-64: the contract the proof is written against

The facts of `I.signContract` for an instance `I` of P-256 with a hash of
`I.hashLen` bytes, for x86-64 and 224 bytes of stack, by name:
`vg_ecdsa_p256_<hash>_sign(out = rdi, d = rsi, digest = rdx, scratch = rcx)`,
the result in `eax`. Each instance's file shows `I.signContract` implies it.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- RFC 6979's signature of the arguments, and the number of candidates tried. -/
abbrev result (I : Spec.Ecdsa.Rfc6979.Instance) (m : Mem) (d digest : Addr) : Option (Nat × Nat) × Nat :=
  I.result m d digest

def rfcX86_64 (I : Spec.Ecdsa.Rfc6979.Instance) : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 64⟩
    let d : Region := ⟨s.gpr .rsi, 32⟩
    let digest : Region := ⟨s.gpr .rdx, I.hashLen⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 224, 224⟩
    224 ≤ (s.gpr .rsp).toNat ∧ s.rd = [d, digest] ∧ s.wr = [out, scratch] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint d ∧ ret.Disjoint digest ∧ ret.Disjoint scratch ∧
      stk.Disjoint out ∧ stk.Disjoint d ∧ stk.Disjoint digest ∧ stk.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + I.hashLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match (result I s.mem (s.gpr .rsi) (s.gpr .rdx)).1 with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = encode Spec.P256.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 64 = List.replicate 64 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    (result I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result I s₂.mem (s₂.gpr .rsi) (s₂.gpr .rdx)).2

/-- A state satisfying the precondition, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

end VG.Proof.Ecdsa.Rfc6979.X86_64
