import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over p192 on x86-64: the contract the proof is written against

The facts of `Spec.Ecdh.P192.exchangeApi`'s contract for x86-64, by name:
`vg_ecdh_p192(out = rdi, d = rsi, peer = rdx, scratch = rcx)`, the result
in `eax`.
-/

namespace VG.Proof.Ecdh.X86_64.P192

open VG VG.X86_64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.P192.curve (ofBytes (bytesAt m d 24)) (bytesAt m peer 49)

def ecdhX86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 24⟩
    let d : Region := ⟨s.gpr .rsi, 24⟩
    let peer : Region := ⟨s.gpr .rdx, 49⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rdi).toNat + 24 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rdi) 24 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .rdi) 24 = List.replicate 24 0
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
  rd := [⟨0x2000, 24⟩, ⟨0x3000, 49⟩]
  wr := [⟨0x1000, 24⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhX86_64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst X86_64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.P192.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P192.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P192.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P192.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
        simp only [ecdhX86_64, ex, Spec.P192.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.P192.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P192.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, ecdhX86_64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.P192.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P192.curve, Spec.EcKey.scratchWords, X86_64.abi,
          X86_64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.X86_64.P192
