module

public import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public meta import VerifiedGarbage.Impl.Cast5.AArch64.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Cast5.AArch64.TblEcbVerified
public meta import VerifiedGarbage.Proof.Cast5.AArch64.TblEcbVerified
public import VerifiedGarbage.Proof.Cast5.Rounds
public meta import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Impl.Scrub.AArch64
public meta import VerifiedGarbage.Impl.Scrub.AArch64
public import VerifiedGarbage.TCB.AArch64.Residue
public meta import VerifiedGarbage.TCB.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.Clears
meta import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
import VerifiedGarbage.Proof.Framework.AArch64.ResidueFrame
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueCT
meta import VerifiedGarbage.Proof.Framework.AArch64.ResidueFrame
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

-- separate module: only the registration needs it, and it imports the proof of ECB, which the residue analysis would otherwise be built with

/-!
# CAST5-ECB on AArch64 returns without secret residue

`ecbEncryptCleared` and `ecbDecryptCleared` are `ecbEncrypt` and
`ecbDecrypt`, then what they leave secret cleared: the registers that held
the halves of the block and the S-box lookups, the vector registers the
calling convention does not preserve, the high halves of `v8`–`v15`, whose
low halves they restore, from `x6`, zeroed first, and the flags, from `x6`.
The residue analysis for two runs that leak the same
(`RTaintCT.noResidue_of_verified`) proves they leave nothing secret.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64

/-- `c`, then the clears of what both directions leave. -/
abbrev ecbCleared (c : Prog isa) : Prog isa := Impl.Cast5.AArch64.Fn.ecbCleared c

abbrev ecbEncryptCleared : Prog isa := Impl.Cast5.AArch64.Fn.ecbEncrypt
abbrev ecbDecryptCleared : Prog isa := Impl.Cast5.AArch64.Fn.ecbDecrypt

theorem ecbEncryptCleared_verified :
    Verified AArch64.target ecbEncryptCleared (Spec.Cast5.ecbEncryptContract AArch64.abi) :=
  Proof.Cast5.ecbEncrypt_keyed (show Verified AArch64.target ecbEncryptCleared
    (Proof.Cast5.ecbRoundsContract AArch64.abi .encrypt) from
    Clears.Verified.withClears (sig := Spec.Cast5.ecbSig) ecbEncrypt_verified (by decide))

theorem ecbDecryptCleared_verified :
    Verified AArch64.target ecbDecryptCleared (Spec.Cast5.ecbDecryptContract AArch64.abi) :=
  Proof.Cast5.ecbDecrypt_keyed (show Verified AArch64.target ecbDecryptCleared
    (Proof.Cast5.ecbRoundsContract AArch64.abi .decrypt) from
    Clears.Verified.withClears (sig := Spec.Cast5.ecbSig) ecbDecrypt_verified (by decide))

/-- The existing residue analysis with the proved call transfer of
`RTaintF`: calls keep memory and vectors and install public unknowns in
`x16`, `x17`, `x30`, and the flags. ECB has no stack frames. -/
private def callResidue : VG.TaintCT isa :=
  { rtaintCT with
    call := fun τ => some (RTaintF.callT (τ, [])).1
    call_sound := by
      intro τ τ' s₁ s₂ t₁ t₂ ha hs e₁ e₂ _
      obtain rfl := Option.some.inj hs
      exact (RTaintF.agree_call
        (show RTaintB.Agree (τ, []) s₁ s₂ from
          ⟨ha, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩) e₁ e₂).1
    ret := fun τ => some τ
    ret_sound := by
      intro τ τ' a₁ a₂ b₁ b₂ c₁ c₂ ha hs e₁ e₂ _
      obtain rfl := Option.some.inj hs
      obtain rfl := ret_eq e₁
      obtain rfl := ret_eq e₂
      exact ha }

private theorem noResidue_calls {c : Prog isa} {k : Contract isa} {r : Nat}
    (hv : Verified target c k)
    (h : ∃ hc, (callResidue.check RTaintL.init c hc).any (RTaintCT.donePres r) = true) :
    NoResidue c k r := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hu e₁ e₂
  obtain ⟨hc, h⟩ := h
  cases hτ : callResidue.check RTaintL.init c hc with
  | none => rw [hτ] at h; cases h
  | some τ' =>
    rw [hτ] at h
    obtain ⟨_, u₁, f₁, hp₁, -⟩ := hv.1 s₁ h₁
    obtain ⟨_, u₂, f₂, hp₂, -⟩ := hv.1 s₂ h₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
    exact RTaintCT.outside_of_donePres
      (TaintCT.agree_of_check hv.2.1 hτ h₁ h₂ hp (RTaintL.agree_init ho hu) e₁ e₂) h ho hp₁ hp₂

theorem ecbEncryptCleared_noResidue :
    NoResidue ecbEncryptCleared (Spec.Cast5.ecbEncryptContract AArch64.abi) 0 :=
  noResidue_calls ecbEncryptCleared_verified ⟨_, by taint_decide_ct⟩

theorem ecbDecryptCleared_noResidue :
    NoResidue ecbDecryptCleared (Spec.Cast5.ecbDecryptContract AArch64.abi) 0 :=
  noResidue_calls ecbDecryptCleared_verified ⟨_, by taint_decide_ct⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.ecbEncrypt
      (Spec.Cast5.ecbEncryptContract AArch64.abi) 0 :=
  ⟨Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_verified,
    Proof.Cast5.AArch64.Tbl.ecbEncryptCleared_noResidue, fun ty _ h => by cases ty <;> cases h⟩

/-- The function as its registration binds it: it meets its contract in constant time and returns
without secret residue. -/
theorem _root_.VG.Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_scrubbed :
    VerifiedScrubbed AArch64.target Impl.Cast5.AArch64.Fn.ecbDecrypt
      (Spec.Cast5.ecbDecryptContract AArch64.abi) 0 :=
  ⟨Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_verified,
    Proof.Cast5.AArch64.Tbl.ecbDecryptCleared_noResidue, fun ty _ h => by cases ty <;> cases h⟩

end VG.Proof.Cast5.AArch64.Tbl
