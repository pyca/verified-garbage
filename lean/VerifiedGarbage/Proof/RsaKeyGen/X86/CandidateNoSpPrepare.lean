module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare
public import VerifiedGarbage.Impl.Mont.Mod
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-! # Prepared candidate calls and word arithmetic preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i mem
  rw [H i mem]
  rfl

theorem mulY {mont : Prog isa} (H : NoSp mont) (name : String) (array : Nat) :
    NoSp (VG.Impl.MillerRabin.X86.mulY name mont array) := by
  apply NoSp.of_all
  simp only [VG.Impl.MillerRabin.X86.mulY, Code.allInstrs, checked H]
  rfl

theorem r2_doubles (M : VG.Impl.Mont.Mod) (acc out : Nat) : NoSp (FastR2.doubles M acc out) := by
  unfold FastR2.doubles FastR2.seed
  exact sequence (constant _ _ _) (NoSp.of_all (by rfl))

theorem fastR2 {square : Prog isa} (H : NoSp square) (M : VG.Impl.Mont.Mod) (acc out : Nat) :
    NoSp (FastR2.code M acc out square) := by
  unfold FastR2.code
  apply sequence (r2_doubles M acc out)
  change NoSp (.seq square (.seq square (.seq square (.seq square (.seq square square)))))
  exact sequence H (sequence H (sequence H (sequence H (sequence H H))))

theorem r2 {mont : Prog isa} (H : NoSp mont) (w : Nat) (name : String) : NoSp (PreparedR2.code w name mont) := by
  unfold PreparedR2.code
  exact sequence (fastR2 (mulY H name 6) _ _ _) (NoSp.of_all (by rfl))

theorem constants {mont : Prog isa} (H : NoSp mont) (w : Nat) (name : String) : NoSp (Constants.code w name mont) := by
  unfold Constants.code
  exact sequence (NoSp.of_all (by rfl))
    (sequence (mulY H name 4) (sequence (NoSp.of_all (by rfl)) (NoSp.of_all (by rfl))))

theorem lowPairs (src start count : Nat) : NoSp (LowPair.steps src start count) := by
  induction count generalizing start with
  | zero => exact NoSp.of_all (by rfl)
  | succ count ih => exact sequence (NoSp.of_all (by rfl)) (ih _)

theorem exponent (w minusOne src out : Nat) : NoSp (Exponent.code w minusOne src out) := by
  unfold Exponent.code ExponentMarker.code LowPair.scan
  exact sequence (sequence (sequence (NoSp.of_all (by rfl)) (lowPairs minusOne 0 w))
    (NoSp.of_all (by rfl))) (NoSp.of_all (by rfl))

theorem prepare {mont : Prog isa} (H : NoSp mont) (w : Nat) (name : String) : NoSp (Prepare.code w name mont) := by
  unfold Prepare.code
  exact sequence (NoSp.of_all (by rfl)) (sequence (r2 H w name)
    (sequence (constants H w name) (exponent _ _ _ _)))

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
