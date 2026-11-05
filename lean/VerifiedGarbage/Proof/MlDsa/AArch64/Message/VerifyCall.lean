module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall

/-!
# ML-DSA on AArch64, `verify_message_cached`: the verification function on `μ`

Untrusted: everything here is checked by Lean. The functions on `μ` that the
cached message verifier can call: any code verified against
`verifyContract p AArch64.abi 16` whose frames nest at most once
(`VerifyFn`); the precondition of that contract from its facts
(`verifyC_pre`); and the arguments of the call, `pk`, `μ` at `X + 840`,
`sig` and `scratch` (`verifyArgs`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- A verification function on `μ` that `verify_message_cached` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified AArch64.target c (verifyContract p AArch64.abi 16)
  dle : DLe 1 c

/-- The precondition of `verifyContract p AArch64.abi 16`, from its facts. -/
theorem verifyC_pre {p : Params} {s : State} (sp : 16 ≤ s.sp.toNat)
    (rd : s.rd = [⟨s.gpr .x0, p.pkLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, p.sigLen⟩])
    (wr : s.wr = [⟨s.gpr .x3, sScr p⟩])
    (d03 : Region.Disjoint ⟨s.gpr .x0, p.pkLen⟩ ⟨s.gpr .x3, sScr p⟩)
    (d13 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, sScr p⟩)
    (d23 : Region.Disjoint ⟨s.gpr .x2, p.sigLen⟩ ⟨s.gpr .x3, sScr p⟩)
    (k0 : (rStk s).Disjoint ⟨s.gpr .x0, p.pkLen⟩) (k1 : (rStk s).Disjoint ⟨s.gpr .x1, 64⟩)
    (k2 : (rStk s).Disjoint ⟨s.gpr .x2, p.sigLen⟩) (k3 : (rStk s).Disjoint ⟨s.gpr .x3, sScr p⟩)
    (n0 : (s.gpr .x0).toNat + p.pkLen ≤ 2 ^ 64) (n1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (n2 : (s.gpr .x2).toNat + p.sigLen ≤ 2 ^ 64) (n3 : (s.gpr .x3).toNat + sScr p ≤ 2 ^ 64) :
    (verifyContract p AArch64.abi 16).pre s := by
  sig_pre [verifyContract, verifySig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
  exact ⟨sp, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fSig), (.x3, .slot fScr)]

end VG.Proof.MlDsa.AArch64.Message
