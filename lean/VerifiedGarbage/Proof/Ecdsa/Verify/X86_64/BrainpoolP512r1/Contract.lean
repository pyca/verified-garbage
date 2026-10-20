module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic

/-!
# ECDSA verification over brainpoolP512r1 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract` for x86-64, by name:
`vg_ecdsa_brainpoolp512r1_verify(public = rdi, digest = rsi, sig = rdx, scratch = rcx)`,
the result in `eax`. Only the pointers are public here: the proof shows that
nothing else affects timing, although the contract would let the contents of
the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1

open VG VG.X86_64 Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.BrainpoolP512r1.curve (bytesAt m pk 129) (hashToInt Spec.BrainpoolP512r1.curve (bytesAt m digest 64)) (bytesAt m sig 128)

def verifyX86_64 : Contract X86_64.isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 129⟩
    let digest : Region := ⟨s.gpr .rsi, 64⟩
    let sig : Region := ⟨s.gpr .rdx, 128⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ ret.Disjoint scratch ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' := (s'.gpr .rax).setWidth 32 = if vf s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 129⟩, ⟨0x2000, 64⟩, ⟨0x3000, 128⟩]
  wr := [⟨0x8000, 8192⟩]

theorem implies : verifyX86_64.Implies (Spec.Ecdsa.BrainpoolP512r1.inst.verifyContract X86_64.abi) := by
  sig_implies [Spec.Ecdsa.BrainpoolP512r1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, verifyX86_64, vf]
    [satState] using satState

end VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1
