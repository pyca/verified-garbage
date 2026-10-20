module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_ffdh_check_domain` on AArch64: the contract the proofs use

`cdContract` states `Spec.Ffdh.checkDomainContract` on the registers:
`vg_ffdh_check_domain(domain = x0, domain_len = x1, p_len = x2, scratch = x3,
scratch_len = x4)`; the shared contract implies it (`cd_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckDomain

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def cdPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let scr : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat * 8⟩
  s.rd = [dom] ∧ s.wr = [scr] ∧ dom.Disjoint scr ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat * 8 ≤ 2 ^ 64 ∧
    pLenValid (s.gpr .x2).toNat ∧ domainLenValid (s.gpr .x2).toNat (s.gpr .x1).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x4).toNat

/-- The domain on entry. -/
abbrev cdDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat

def cdPost (s s' : State) : Prop :=
  ((s'.gpr .x0).setWidth 32).toNat = if domainValid (s.gpr .x2).toNat (cdDom s) then 1 else 0

def cdPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ (cdDom s₁).map (·.toNat) = (cdDom s₂).map (·.toNat) ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧
    s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4

def cdContract : Contract isa where
  pre := cdPre
  post := cdPost
  pub := cdPub

/-- A state meeting the precondition: a 64-byte p, no q. -/
def cdSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 64 | .x3 => 0x4000 | .x4 => 1056 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cd_implies : cdContract.Implies (checkDomainContract abi) := by
  sig_implies [checkDomainContract, checkDomainSig, abi, argRegs, cdContract, cdPre, cdPost, cdPub,
    pLenValid, domainLenValid] [cdSat] using cdSat

end VG.Proof.Ffdh.AArch64.CheckDomain
