module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Omega

/-! Montgomery one is prepared through the same constant-trace RSA operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand)
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure MontMathData where
  base : BitVec 32
  capacity : Nat
  words : Nat

def MontR2 (p : MontMathData) (s : State) : Prop := ArithmeticReady p.base p.capacity p.words s ∧
  numAt s.mem (State.addr p.base) p.words 4 < numAt s.mem (State.addr p.base) p.words 0

theorem smallOne_ready (p : MontMathData) (s : State) (h : MontR2 p s) :
    WP isa (VG.Impl.Bignum.Arm.smallConst 1 1) s (MontR2 p) := by
  refine WP.mono (smallConst_ok s 1 h.1 (o := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨ready, _, _, keeps, _, _⟩
  have fits : arrAt p.words 8 ≤ 8 * p.capacity := h.1.width ▸ h.1.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine ⟨ready, ?_⟩
  rw [keeps_array_num keeps fits op4 (by decide), keeps_array_num keeps fits op0 (by decide)]
  exact h.2

theorem montOne_ready (p : MontMathData) (s : State) (h : MontR2 p s) :
    WP isa (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) s
      (ArithmeticReady p.base p.capacity p.words) := by
  refine WP.seq (WP.mono (smallOne_ready p s h) ?_)
  intro u ready
  refine WP.mono (montOp_ok u ready.1 (o := 1) (a := 1) (b := 4)
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide) ready.2) ?_
  rintro t ⟨result, _, _, _, _, _, _⟩
  exact result

theorem montOne_ct : RelCT isa (Two MontR2)
    (.seq (VG.Impl.Bignum.Arm.smallConst 1 1) (VG.Impl.Bignum.Arm.montOp 1 1 4)) (fun _ _ => True) := by
  have smallTrace : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.smallConst 1 1) (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    exact smallConst_ct 1 (o := 1) (by decide) (by decide) (by decide) _ _ _ _ _ _ ⟨left.1, right.1, sp⟩ runS runT
  have small : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.smallConst 1 1) (Two MontR2) :=
    two_post smallTrace smallOne_ready
  have encode : RelCT isa (Two MontR2) (VG.Impl.Bignum.Arm.montOp 1 1 4) (fun _ _ => True) := by
    intro s t trS trT u v h runS runT
    obtain ⟨p, left, right, sp⟩ := h
    have fit : arrAt p.words 3 + 32 ≤ 8 * p.capacity := by
      have fits : arrAt p.words 8 ≤ 8 * p.capacity := left.1.width ▸ left.1.layout.2.2.1
      dsimp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits ⊢
      omega
    exact montOp_ct (o := 1) (a := 1) (b := 4)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) fit _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
  exact small.seq encode

end VG.Proof.Ffdh.Arm.ParameterCandidate
