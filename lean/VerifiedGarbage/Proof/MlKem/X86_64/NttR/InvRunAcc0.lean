module

import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Fast
import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.ZmLit
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

/-! ### `MlKem.X86_64.NttR.InvRun`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the run of its terms

Pass B reads the input at `rdi` and writes `S`, in the regions `rsA` of
`NTT`; pass A reads `S` and writes the output to `rdi`, in the regions
`rsB .rdi`. Pass B starts from the terms of the input (`initIB`): the
accumulator's words, coefficient `accIdx w` in word `w` (`accTerms`);
`checkI` says the output's terms are
`out p`, in the low words of their `u32`s.

The kernel checks the run in two parts, each in a module of its own
(`InvRunAcc0.lean`, …): the first half of pass B (`stIAcc0`), then the
second half (`stIAcc1`), and pass A (`stIAccA`), each from the literal of the
part before.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

/-- The accumulator's words, sixteen at a time, then words not followed. -/
def accTerms : List Y :=
  (List.range 16).map (fun c => (List.range 16).map fun e => .lv 0 (accIdx (16 * c + e))) ++ junks 16

def srcTerms : InvIn → List Y
  | .acc => accTerms

def initIB (src : InvIn) : St :=
  ⟨(List.range 16).map (fun r => if r = 15 then List.replicate 16 (.c qN) else List.replicate 16 .junk),
   [junks 16, srcTerms src]⟩

/-- The run of pass B `pb` and of pass A, and whether it leaves `NTT⁻¹` in the output. -/
def checkI (src : InvIn) (pb : List Instr) : Bool :=
  match (initIB src).run invRules rsA pb with
  | some σ =>
    match (toB σ).run invRules (rsB .rdi) passIA with
    | some σ' => outOk σ'
    | none => false
  | none => false

/-! ## The run in parts -/

/-- The state after half 0 of pass B. -/
def stI0 (src : InvIn) (p₀ : List Instr) : Option St := (initIB src).run invRules rsA p₀

/-- The state after half 1 of pass B. -/
def stI1 (σ₀ : Option St) (p₁ : List Instr) : Option St := σ₀.bind fun σ => σ.run invRules rsA p₁

/-- The state after pass A. -/
def stIA (σ₁ : Option St) : Option St := σ₁.bind fun σ => (toB σ).run invRules (rsB .rdi) passIA

def stIAcc0 : Option St := stI0 .acc passIBAcc0
def stIAcc1 : Option St := stI1 stIAcc0 passIBAcc1
def stIAccA : Option St := stIA stIAcc1

/-- `checkI` from the state after both parts. -/
theorem checkI_of {src : InvIn} {p₀ p₁ : List Instr}
    (ho : (stIA (stI1 (stI0 src p₀) p₁)).any outOk = true) : checkI src (p₀ ++ p₁) = true := by
  unfold checkI
  rw [stIA, stI1, stI0] at ho
  split
  · rename_i σB hB
    rw [St.run_append] at hB
    rw [hB, Option.bind_some] at ho
    split
    · rename_i σ' h'
      rw [h', Option.any_some] at ho
      exact ho
    · rename_i h'
      rw [h', Option.any_none] at ho
      exact ho
  · rename_i hB
    rw [St.run_append] at hB
    rw [hB, Option.bind_none, Option.any_none] at ho
    exact ho

end VG.Proof.MlKem.X86_64.NttR

end

end

/-!
# ML-KEM on x86-64: `NTT⁻¹` on registers, the first half of pass B from an accumulator

The state after half 0 of pass B reading an accumulator, for the functions that inline `NTT⁻¹`, as a literal.
The kernel evaluates the run by `St.runF` (`Fast.lean`): `stIAcc0F`, which is `stIAcc0` (`stIAcc0_eq`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64 (zmTab)
open VG.Impl.MlKem.X86_64.NttR

/-- `stIAcc0`, run by `St.runF`. -/
def stIAcc0F : Option St := (initIB .acc).runF zmTab invRules (St.step invRules rsA) passIBAcc0

theorem stIAcc0_eq : stIAcc0 = stIAcc0F := by
  simp only [stIAcc0, stI0, stIAcc0F, St.runF_eq]

materialize_value stIAcc0F

end VG.Proof.MlKem.X86_64.NttR
