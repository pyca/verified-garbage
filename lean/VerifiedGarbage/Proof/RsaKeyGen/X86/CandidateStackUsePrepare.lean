module

import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateTest
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Prepare

/-! # Prepared arithmetic reserves 40 bytes below its caller -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateStackUse
open VG VG.X86 VG.Impl.RsaKeyGen.X86

theorem mulY {mont : Prog isa} (bound : stackUse mont ≤ 16) (name : String) (array : Nat) :
    stackUse (VG.Impl.MillerRabin.X86.mulY name mont array) ≤ 40 := by
  change max 0 (stackUse mont + 4 + 20) ≤ 40
  omega

theorem six {square : Prog isa} {limit : Nat} (bound : stackUse square ≤ limit) :
    stackUse (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square)) ≤ limit := by
  change max (stackUse square) (max (stackUse square) (max (stackUse square)
    (max (stackUse square) (max (stackUse square) (stackUse square))))) ≤ limit
  omega

theorem fastR2 {square : Prog isa} {limit : Nat} (bound : stackUse square ≤ limit)
    (M : VG.Impl.Mont.Mod) (acc out : Nat) : stackUse (FastR2.code M acc out square) ≤ limit := by
  have doubles : stackUse (FastR2.doubles M acc out) = 0 := rfl
  have copies := six bound
  change max (stackUse (FastR2.doubles M acc out)) (stackUse (VG.Impl.Rsa.X86.Keys.seqs (List.replicate 6 square))) ≤ limit
  rw [doubles]
  omega

theorem r2 {mont : Prog isa} (bound : stackUse mont ≤ 16) (w : Nat) (name : String) :
    stackUse (PreparedR2.code w name mont) ≤ 40 := by
  have main := fastR2 (mulY bound name 6) (VG.Impl.Bignum.X86.PublicContext.modulus w)
    (VG.Impl.Bignum.X86.PublicContext.slot w 2) (VG.Impl.Bignum.X86.PublicContext.slot w 6)
  change max (stackUse (FastR2.code _ _ _ _)) 0 ≤ 40
  omega

theorem lowPairs (src start count : Nat) : stackUse (LowPair.steps src start count) = 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    change max 0 (stackUse (LowPair.steps src (start + 1) count)) = 0
    rw [ih]; rfl

theorem exponent (w minusOne src out : Nat) : stackUse (Exponent.code w minusOne src out) = 0 := by
  unfold Exponent.code ExponentMarker.code LowPair.scan
  simp only [stackUse, lowPairs]
  rfl

theorem constants {mont : Prog isa} (bound : stackUse mont ≤ 16) (w : Nat) (name : String) :
    stackUse (Constants.code w name mont) ≤ 40 := by
  have product := mulY bound name 4
  change max 0 (max (stackUse (VG.Impl.MillerRabin.X86.mulY name mont 4)) (max 0 0)) ≤ 40
  omega

theorem prepare {mont : Prog isa} (bound : stackUse mont ≤ 16) (w : Nat) (name : String) :
    stackUse (Prepare.code w name mont) ≤ 40 := by
  have r2bound := r2 bound w name
  have constantsBound := constants bound w name
  have exponentZero := exponent w (VG.Impl.Bignum.X86.PublicContext.slot w 5)
    (VG.Impl.Bignum.X86.PublicContext.slot w 0) (VG.Impl.Bignum.X86.PublicContext.slot w 27)
  change max 0 (max (stackUse (PreparedR2.code w name mont))
    (max (stackUse (Constants.code w name mont)) (stackUse (Exponent.code w _ _ _)))) ≤ 40
  rw [exponentZero]
  omega

end VG.Proof.RsaKeyGen.X86.CandidateStackUse
