module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.EcKey.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1

/-!
# ECDH over brainpoolP384r1 on AArch64: the contract the proof is written against

The facts of `Spec.Ecdh.BrainpoolP384r1.exchangeApi`'s contract for AArch64, by name:
`vg_ecdh_brainpoolp384r1(out = x0, d = x1, peer = x2, scratch = x3)`, the result in
`w0`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.BrainpoolP384r1

open VG VG.AArch64 Spec.Weierstrass Spec.EcKey

/-- The shared secret of the private key at `d` and the public key at
`peer`, as the specification computes it. -/
abbrev ex (m : Mem) (d peer : Addr) : Option (List Byte) :=
  Spec.Ecdh.exchange Spec.BrainpoolP384r1.curve (ofBytes (bytesAt m d 48)) (bytesAt m peer 97)

def ecdhAArch64 : Contract AArch64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, 48⟩
    let d : Region := ⟨s.gpr .x1, 48⟩
    let peer : Region := ⟨s.gpr .x2, 97⟩
    let scratch : Region := ⟨s.gpr .x3, 8192⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      (s.gpr .x0).toNat + 48 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x0) 48 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .x0) 48 = List.replicate 48 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 97⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem implies :
    ecdhAArch64.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP384r1.inst AArch64.abi) := by
  exact
    { pre := by
        sig_implies_pre [Spec.EcKey.BrainpoolP384r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP384r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.BrainpoolP384r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP384r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
        simp only [ecdhAArch64, ex, Spec.BrainpoolP384r1.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact id
      pub := by
        sig_implies_pub [Spec.EcKey.BrainpoolP384r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP384r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, ecdhAArch64, ex]
      sat := by
        sig_implies_sat [Spec.EcKey.BrainpoolP384r1.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.BrainpoolP384r1.curve, Spec.EcKey.scratchWords, AArch64.abi,
          AArch64.argRegs, satState] [satState] using satState }

end VG.Proof.Ecdh.AArch64.BrainpoolP384r1
