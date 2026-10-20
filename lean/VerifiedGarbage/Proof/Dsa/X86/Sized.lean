module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Proof.Dsa.Accepted

import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli

/-! # Public shape rejection before the arithmetic body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Ecdsa.X86
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem sized_ok (signing : Bool) {s : State} {base : Addr} {size pLen qLen p q : Nat}
    {post : State → Prop}
    (hs : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen) (Q : CallerBuffer s base size (.input .q) qLen)
    (hp : operandValue s base (.input .p) pLen = p) (hq : operandValue s base (.input .q) qLen = q)
    (failure : ∀ t, ¬ shapeValid p q → Keeps shapeClob s t →
      Outs base shapeRanges s.mem t.mem → WP isa (Entry.failure signing) t post)
    (body : ∀ t, shapeValid p q → Moduli base size pLen qLen p q t →
      (pointerValue base t (.input .digestPrefixLen)).toNat =
        min (pointerValue base s (.input .digestLen)).toNat (Spec.Dsa.bitLength q / 8) →
      flagW base (Layout.field .mask) t = BitVec.allOnes 32 →
      Keeps shapeClob s t → Outs base shapeRanges s.mem t.mem →
      WP isa (if signing then SignVerify.signBody pLen qLen else SignVerify.verifyBody pLen qLen) t post) :
    WP isa (Entry.sized signing pLen qLen) s post := by
  unfold Entry.sized
  refine WP.seq (WP.mono (shapeModuli_ok hs extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, D⟩ := M valid
    exact body t valid Mt D (by simpa only [flagW, mask32, valid, decide_true, ite_true] using F) K O
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => failure t valid K O) (fun h => Bool.noConfusion h)

end VG.Proof.Dsa.X86
