module

public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
public import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Weierstrass.X86.TComb
meta import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
meta import VerifiedGarbage.Impl.Ecdsa.P256.X86Comb
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Ecdsa.X86.CombLit
meta import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
meta import VerifiedGarbage.Proof.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# ECDSA over P-256 on x86 (32-bit): the comb's code and the taints of its constant-time checks

The checks of the comb's iteration (`CombStepCT`) and of its last step
(`CombFinishCT`) are each in a module of their own, checked in parallel;
`CombCT` composes them.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

def p256d : CombData := ⟨7, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB"⟩
abbrev p256K := p256Comb.combCfg p256d

def combStep : Prog isa := p256K.stepJ
materialize_code combStep

def combFirst : Prog isa := p256K.first
materialize_code combFirst

/-- No instruction of an iteration writes `esp`, and its calls use 20 bytes of stack. -/
theorem combStep_sp : SpOk combStep 20 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩
theorem combFirst_sp : SpOk combFirst 20 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

def combRegion (scratchSecond : Bool) : Nat := if scratchSecond then 1 else 0

def combτAt (scratchSecond : Bool) : VG.X86.Taint.T :=
  { regs := .ofList [.esi, .edi, .esp], flags := false,
    lens := if scratchSecond then [0, 8192] else [8192],
    bases := [(.edi, combRegion scratchSecond, 0)],
    slots := [(combRegion scratchSecond, 60, 4)], room := 20 }

abbrev combτ := combτAt true

variable {scratchSecond : Bool}

/-- The hints forget the public slots and base words outside the calls of the
field arithmetic; inside them they keep everything (the functions read their
pointers from the call's frame). -/
def combWeak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with slots := .empty, wbases := [] } else τ

end VG.Proof.Ecdsa.X86
