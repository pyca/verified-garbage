module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# `vg_ffdh_check_public` on AArch64: the contract the proofs use

`cpContract` states `Spec.Ffdh.checkPublicContract` on the registers:
`vg_ffdh_check_public(domain = x0, domain_len = x1, p_len = x2, y = x3,
y_len = x4, scratch = x5, scratch_len = x6)`; the shared contract implies it
(`cp_implies`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.CheckPublic

open VG VG.AArch64 VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt os2ip)

def cpPre (s : State) : Prop :=
  let dom : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  let y : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  let scr : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 8⟩
  s.rd = [dom, y] ∧ s.wr = [scr] ∧ dom.Disjoint scr ∧ y.Disjoint scr ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat * 8 ≤ 2 ^ 64 ∧ pLenValid (s.gpr .x2).toNat ∧
    domainLenValid (s.gpr .x2).toNat (s.gpr .x1).toNat ∧ (s.gpr .x4).toNat = (s.gpr .x2).toNat ∧
    Spec.Rsa.scratchWords (s.gpr .x2).toNat ≤ (s.gpr .x6).toNat

/-- The domain on entry. -/
abbrev cpDom (s : State) : List Byte := bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat

def cpPost (s s' : State) : Prop :=
  domainValid (s.gpr .x2).toNat (cpDom s) →
    ((s'.gpr .x0).setWidth 32).toNat =
      if publicValid ⟨domainOf (s.gpr .x2).toNat (cpDom s), os2ip (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)⟩
      then 1 else 0

/-- What timing may depend on, beyond the arguments: the domain and y. -/
def cpLeak (s : State) : List Nat :=
  (cpDom s).map (·.toNat) ++ (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat).map (·.toNat)

def cpPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ cpLeak s₁ = cpLeak s₂ ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6

def cpContract : Contract isa where
  pre := cpPre
  post := cpPost
  pub := cpPub

/-- A state meeting the precondition: a 64-byte p, no q. -/
def cpSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 128 | .x2 => 64 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x4000 | .x6 => 1056 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cp_implies : cpContract.Implies (checkPublicContract abi) := by
  sig_implies [checkPublicContract, checkPublicSig, abi, argRegs, cpContract, cpPre, cpPost, cpPub, cpLeak,
    pLenValid, domainLenValid] [cpSat] using cpSat

end VG.Proof.Ffdh.AArch64.CheckPublic
