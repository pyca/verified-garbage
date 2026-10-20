module

public import VerifiedGarbage.Proof.Bignum.Arm.CombExpReadOnly
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpShared

/-! Every callable RSA Montgomery backend supports the same immutable comb context. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombExp
open VG VG.Arm VG.Arm.FrameStack

def writeRegions (base sp : BitVec 32) (len : Nat) : List Region :=
  [⟨State.addr base,8*len⟩,belowA sp 48]

abbrev Persistent (base source table sp : BitVec 32) (len w M g N : Nat) (bs : List Byte) (s : State) : Prop :=
  TwoExp.CallReady base sp len s ∧ ReadOnly source table w M g N bs (writeRegions base sp len) s

def arithmetic (backend : MontBackend) (base source table sp : BitVec 32)
    (len w M g N : Nat) (bs : List Byte) :
    TwoExp.Montgomery base len w (Persistent base source table sp len w M g N bs)
      (writeRegions base sp len) :=
  withInvariant (TwoExp.sharedMontgomery base sp len w backend.name backend.mul
    (fun _ _ _ ho ha hb s h=>backend.correct s h ho ha hb) backend.stackOk)
    (ReadOnly source table w M g N bs (writeRegions base sp len))
    (by intro s t frame rest h; exact h.after_frame frame rest)

end VG.Proof.Bignum.Arm.CombExp
