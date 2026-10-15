/-
Development tooling only: nothing imports this file, and it is not built.

The taint at each call of a function in code, as the constant-time analysis
computes it: the `pre` to give `taint_summary` for that call, so that
`taint_decide_sum` can use the summary in place of analysing the callee at
every call.

Usage (from `lean/`, the module and its imports built):
  lake env lean ../tools-taint/CallTaints.lean
after replacing the import, the domain (`A`), the code and the entry taint in
the `#eval`s at the bottom. Each call prints `name: taint`; if every call of a
function prints the same taint, one summary from it covers them all, and from a
smaller set of public registers (with the same memory knowledge) it covers
calls with more. `Mono.R` compares the memory knowledge (lens, bases, slots,
...) exactly on x86 and x86-64.

It walks the hint the analysis builds (`Taint.hintSum` with no summaries):
`seq mid` is the taint after the first part, `loop inv` the loop's invariant.
A `frame` pushes before its body (`A.push`): x86's modes call the block
function inside one, so the taint at the call is the pushed one.

Then: `def τCall : T := { … }` (write the slots' masks compactly, e.g.
`⟨[0xFFF, 0, 0, 0xFF <<< 920]⟩`), `taint_summary encSum : A τCall (.call "name" code)`,
and `taint_decide_sum [encSum]` in the checks (on x86-64, the `taintS` domain).
Example: `Proof/TripleDes/{X86,X86_64}/BlockSum.lean` (PR #2371).
-/
import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
import Lean
open VG Lean Meta

/-- The taints at the calls in `c`, from the hint `h` of its analysis from `τ`. -/
def callTaints {M : ISA} (A : VG.Taint M) : A.T → Prog M → VG.Taint.SHint A.T → List (String × A.T)
  | τ, .seq c₁ c₂, .seq mid h₁ h₂ => callTaints A τ c₁ h₁ ++ callTaints A mid c₂ h₂
  | τ, .ite _ t e, .ite h₁ h₂ => callTaints A τ t h₁ ++ callTaints A τ e h₂
  | _, .loop b _, .loop inv h => callTaints A inv b h
  | τ, .call n _, _ => [(n, τ)]
  | τ, .frame i b _, .frame h => match A.push τ i with
    | some τ' => callTaints A τ' b h
    | none => []
  | _, _, _ => []

/-- Print the taint at each call in `c`, analysed from `τ`, with `pp`. -/
def printCallTaints {M : ISA} (A : VG.Taint M) [VG.Taint.Frame A] (pp : A.T → Expr) (τ : A.T)
    (c : Prog M) : MetaM Unit := do
  match VG.Taint.hintSum (A := A) [] (fun _ _ => false) τ c with
  | none => IO.println "the analysis fails"
  | some (_, h) =>
    for (n, t) in callTaints A τ c h do
      IO.println s!"{n}: {← Meta.ppExpr (pp t)}"

-- x86 (the plain `taint` domain has summaries):
#eval printCallTaints VG.X86.taint (toExpr (α := VG.X86.Taint.T)) VG.Proof.TripleDes.X86.Fb.fbTaint VG.Impl.TripleDes.X86.ofb
-- x86-64 (summaries need `VG.X86_64.taintS`; import the module of the code and its taint):
-- #eval printCallTaints VG.X86_64.taintS (toExpr (α := VG.X86_64.Taint.T)) VG.Proof.TripleDes.X86_64.fbTaint VG.Impl.TripleDes.X86_64.ofb
