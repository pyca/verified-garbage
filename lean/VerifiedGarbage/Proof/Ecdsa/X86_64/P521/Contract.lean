import VerifiedGarbage.Spec.Ecdsa.P521
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA over P-521 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.P521.inst.signContract` for x86-64, by name:
`vg_ecdsa_p521_sign(out = rdi, d = rsi, digest = rdx, k = rcx, scratch = r8)`,
the result in `eax`.
-/

namespace VG.Proof.Ecdsa.X86_64.P521

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- The signature of the arguments, as the specification computes it. -/
abbrev sig (m : Mem) (d digest k : Addr) : Option (Nat × Nat) :=
  signWith Spec.P521.curve (ofBytes (bytesAt m d 66)) (hashToInt Spec.P521.curve (bytesAt m digest 66))
    (ofBytes (bytesAt m k 66))

def signX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 132⟩
    let d : Region := ⟨s.gpr .rsi, 66⟩
    let digest : Region := ⟨s.gpr .rdx, 66⟩
    let k : Region := ⟨s.gpr .rcx, 66⟩
    let scratch : Region := ⟨s.gpr .r8, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 132 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match sig s.mem (s.gpr .rsi) (s.gpr .rdx) (s.gpr .rcx) with
    | some rs => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 132 = encode Spec.P521.curve rs
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 132 = List.replicate 132 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 66⟩, ⟨0x3000, 66⟩, ⟨0x4000, 66⟩]
  wr := [⟨0x1000, 132⟩, ⟨0x8000, 8192⟩]

theorem implies : signX86_64.Implies (Spec.Ecdsa.P521.inst.signContract X86_64.abi) := by
  sig_implies [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, signX86_64, sig]
    [satState] using satState

end VG.Proof.Ecdsa.X86_64.P521
