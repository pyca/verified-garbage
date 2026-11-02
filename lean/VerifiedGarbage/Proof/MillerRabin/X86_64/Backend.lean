module

public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCorrect
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallTemplate
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel

/-! # Shared round implementations for generic RSA and FFDH callers -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

structure RoundImpl where
  mont : Mont
  /-- Arithmetic specialized for callers that inline their multiplication.
  The callable kernel may dispatch on operand indices at run time; this
  form can select that operation while constructing the caller. -/
  inlineMont : Mont := mont
  inlineDepth : ∀ o a b, (inlineMont.mm o a b).x86_64Depth = 0
  inlineSafe : ∀ o a b, (inlineMont.mm o a b).allInstrs
    (fun i => !loadsMxcsr i && !isa.writesSp i) = true
  /-- Montgomery multiplication as the round and its callers emit it: calls
  of a function, which inline to `mont.mm` (`Verified.of_inline`), or
  `mont.mm`. -/
  mm : Nat → Nat → Nat → Prog isa
  mmOk : ∀ o a b, (mm o a b).InlineOk = true
  mmInline : ∀ o a b, (mm o a b).inline = mont.mm o a b
  mxSafe : (round mm).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : (round mm).all (fun i => !isa.writesSp i) = true
  depth : (round mm).x86_64Depth ≤ 120
  arithDepth : ∀ o a b, (mont.mm o a b).x86_64Depth = 0
  arithSafe : ∀ o a b, (mont.mm o a b).allInstrs (fun i => !loadsMxcsr i && !isa.writesSp i) = true
  suffix : String
  features : List String

def RoundImpl.name (v : RoundImpl) : String :=
  "vg_miller_rabin_round" ++ v.suffix

/-- The round, multiplying by `mm`. -/
def RoundImpl.code (v : RoundImpl) : Prog isa := round v.mm

theorem RoundImpl.body_inlineOk (v : RoundImpl) : (body v.mm).InlineOk = true :=
  VG.Proof.MillerRabin.X86_64.body_inlineOk v.mm v.mmOk

theorem RoundImpl.body_inline (v : RoundImpl) : (body v.mm).inline = body v.mont.mm := by
  rw [VG.Proof.MillerRabin.X86_64.body_inline]
  simp only [v.mmInline]

theorem RoundImpl.no_mx_load (v : RoundImpl) : ∀ i ∈ instrs v.code, loadsMxcsr i = false := by
  have h := v.mxSafe
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simpa only [Bool.not_eq_true'] using this

theorem RoundImpl.correct (v : RoundImpl) (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa v.code s tr t ∧ abiPreserved s t ∧ roundPost s t :=
  round_call_correct v.mont v.body_inlineOk v.body_inline v.no_mx_load s h

theorem RoundImpl.ct (v : RoundImpl) : ConstantTime isa roundPre roundPub v.code :=
  round_call_ct v.mont v.body_inlineOk v.body_inline

theorem RoundImpl.verified (v : RoundImpl) : Verified target v.code
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.extended 120) :=
  Verified.of_correct v.correct v.ct round_implies

end VG.Proof.MillerRabin.X86_64
