module

public import VerifiedGarbage.Spec.EcKey.Validate
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem

/-! # The standalone validation contract on x86-64, by name -/

@[expose] public section

namespace VG.Proof.EcKey.Validate.X86_64

open VG VG.X86_64

/-- The signature's obligations needed by the correctness proof. -/
def keyContract (C : Spec.Weierstrass.Curve) : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .rdi, 2 * C.len + 1⟩
    let ws : Region := ⟨s.gpr .rsi, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [pk] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ ret.Disjoint ws ∧
      (s.gpr .rsi).toNat + 8192 ≤ 2 ^ 64
  post s s' := (s'.gpr .rax).setWidth 32 =
    if (Spec.EcKey.decodePublicKey C (Spec.EcKey.bytesAt s.mem (s.gpr .rdi) (2 * C.len + 1))).isSome
      then 1 else 0
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

/-- The exported contract requires all of these facts and nothing about
initial workspace contents or caller-provided curve constants. -/
theorem implies (I : Spec.EcKey.Instance)
    (hsat : ∃ s, (I.validatePublicKeyContract abi 8).pre s) :
    (keyContract I.curve).Implies (I.validatePublicKeyContract abi 8) where
  pre := by
    sig_implies_pre [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
  post := by
    intro s s' _ h
    sig_post [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
    exact h
  pub := by
    sig_implies_pub [Spec.EcKey.Instance.validatePublicKeyContract,
      Spec.EcKey.Instance.validatePublicKeySig, Spec.EcKey.scratchWords,
      abi, argRegs, keyContract]
  sat := hsat

/-- A witness used to check each curve's exported precondition. -/
def satState (len : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x8000 | .rsp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 2 * len + 1⟩]
  wr := [⟨0x8000, 8192⟩]

end VG.Proof.EcKey.Validate.X86_64
