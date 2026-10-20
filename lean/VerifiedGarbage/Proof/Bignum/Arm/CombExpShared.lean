module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

/-! Read-only context and exponent facts persist through the shared arithmetic calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def withInvariant {base : BitVec 32} {len w : Nat} {P : State→Prop} {regions : List Region}
    (A : TwoExp.Montgomery base len w P regions) (Q : State→Prop)
    (stableQ : ∀ {s t : State}, Frame regions s.mem t.mem → Rest roundClobbers s t → Q s → Q t) :
    TwoExp.Montgomery base len w (fun s=>P s ∧ Q s) regions where
  op := A.op
  workspace := A.workspace
  stable := by
    intro s t frame rest h
    exact ⟨A.stable frame rest h.1,stableQ (frame.mono (by simpa using A.workspace)) rest h.2⟩
  op_ok := by
    intro s o a b ready h ho ha hb ho0 operand
    refine WP.mono (A.op_ok s o a b ready h.1 ho ha hb ho0 operand) ?_
    rintro t ⟨readyT,modulus,bound,value,keeps,pt,frame,rest⟩
    exact ⟨readyT,modulus,bound,value,keeps,⟨pt,stableQ frame rest h.2⟩,frame,rest⟩

end VG.Proof.Bignum.Arm.CombExp
