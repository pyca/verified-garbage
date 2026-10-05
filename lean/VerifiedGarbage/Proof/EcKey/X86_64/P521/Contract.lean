import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-521 public keys on x86-64: the contract the proof is written against

The facts of `Spec.EcKey.P521.inst.publicKeyContract` for x86-64, by name:
`vg_ec_p521_public_key(out = rdi, d = rsi, scratch = rdx)`, the result in
`eax`.
-/

namespace VG.Proof.EcKey.X86_64.P521

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point Spec.P521.curve) :=
  publicKey Spec.P521.curve (ofBytes (bytesAt m d 66))

def pkX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 133⟩
    let d : Region := ⟨s.gpr .rsi, 66⟩
    let scratch : Region := ⟨s.gpr .rdx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 133 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 133 = encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 133 = List.replicate 133 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x8000
    | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 66⟩]
  wr := [⟨0x1000, 133⟩, ⟨0x8000, 8192⟩]

theorem implies : pkX86_64.Implies (Spec.EcKey.P521.inst.publicKeyContract X86_64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
        simp only [pkX86_64, pk, Spec.P521.curve] at h
        revert h
        generalize publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, pkX86_64, pk]
      sat := by
        sig_implies_sat [Spec.EcKey.P521.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P521.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, satState] [satState] using satState }

end VG.Proof.EcKey.X86_64.P521
