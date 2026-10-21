module

import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTCore
public import VerifiedGarbage.Proof.Bignum.Arm.MontBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.MontInitCT
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.MontPipelineCTRounds
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! Reuse the original public initialization for any scanning-round implementation. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem body_ct (round : Prog isa) (law : RoundLaw round) (ctLaw : RoundCTLaw round) {base : BitVec 32} {size out tmp a b mod acc n : Nat} (even : n % 2 = 0) (ht : tmp + 32 ≤ size) :
    RelCT isa (fun s t => InitReady base size out tmp a b mod acc n s ∧
      InitReady base size out tmp a b mod acc n t) (VG.Impl.Bignum.Arm.MontPipeline.body round) (fun _ _ => True) := by
  let P := InitReady base size out tmp a b mod acc n
  have ct : RelCT isa (fun s t => P s ∧ P t) montInit (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    obtain ⟨is, rs, _⟩ := h.1.secret
    obtain ⟨it, rt, _⟩ := h.2.secret
    exact ⟨montInit_ct s t tr1 tr2 u v trivial trivial
      ⟨rs.tmpPtr.trans rt.tmpPtr.symm, rs.accPtr.trans rt.accPtr.symm, rs.count.trans rt.count.symm⟩ e1 e2, trivial⟩
  have wp (s : State) (h : P s) : WP isa montInit s (CoreReady base size out tmp a b mod acc n) := by
    obtain ⟨inv, regs, inverse⟩ := h.secret
    exact WP.mono (montInit_ok s h.ctx regs h.operand inverse) (fun _ h => h.1)
  exact (pair_posts ct wp).seq (core_ct round law ctLaw even ht)


end VG.Proof.Bignum.Arm.MontPipeline
