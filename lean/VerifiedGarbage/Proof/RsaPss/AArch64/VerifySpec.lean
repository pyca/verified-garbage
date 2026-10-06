import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyMain
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec

/-!
# RSASSA-PSS verification on AArch64: the result, by cases

`verifyOut G s`: what the contract asks of a call from `s`. It is `false`
if the modulus' first byte is zero (`verifyOut_zero`) or the salt does not
fit (`verifyOut_short`), and otherwise the checks of the encoding in RSAVP1's
result (`verifyOut_iff`).
-/

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64 (loV maskV)
open VG.Proof.RsaPss.AArch64.Sgn (bytesAt_cons)

variable (G : Spec.Mgf1.Hash)

/-- The result `verifyContract.post` asks for. -/
def verifyOut (s : State) : Bool :=
  Spec.RsaPss.verify G G (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x1).toNat)
    (Spec.RsaPss.expectedSaltLen (s.gpr .x7) ((stackArg s 0).setWidth 32))

theorem anyV_eq (s : State) : anyV s = 0 ↔ (stackArg s 0).setWidth 32 = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [anyV, BitVec.toNat_setWidth] at this ⊢
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    rw [show (0 : BitVec 32).toNat = 0 from rfl]
    omega
  · intro h; unfold anyV; rw [h]; rfl

theorem expected_eq (s : State) :
    Spec.RsaPss.expectedSaltLen (s.gpr .x7) ((stackArg s 0).setWidth 32) = sLenV s := by
  unfold Spec.RsaPss.expectedSaltLen sLenV
  by_cases h : anyV s = 0
  · rw [ite_eq_left h, ite_eq_left ((anyV_eq s).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun e => h ((anyV_eq s).mpr e))]

theorem verifyOut_zero {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) = 0) :
    verifyOut G s = false := by
  unfold verifyOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.verify_zero G ..

theorem emLen_eq {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)) - 1) =
      (s.gpr .x1).toNat - loV (s.mem (s.gpr .x0)).toNat := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loV
  split <;> omega

theorem verifyOut_short {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) ≠ 0)
    (h : (s.gpr .x1).toNat - loV (s.mem (s.gpr .x0)).toNat < G.len + (sLenV s).getD 0 + 2) :
    verifyOut G s = false := by
  unfold verifyOut
  refine RsaPss.verify_short G _ _ _ ?_
  rw [emLen_eq hk h0, expected_eq]
  exact h

/-- The mask of `DB`'s top byte, `0xFF >>> z` for `z = 8 emLen - emBits`. -/
theorem mask_z {s : State} (hk : 1 ≤ (s.gpr .x1).toNat) (h0 : s.mem (s.gpr .x0) ≠ 0) :
    (maskV (s.mem (s.gpr .x0)).toNat).setWidth 8 = (0xFF : Byte) >>> (8 * ((s.gpr .x1).toNat -
      loV (s.mem (s.gpr .x0)).toNat) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
        (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)) - 1)) := by
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .x0 + 1) ((s.gpr .x1).toNat - 1)) h0
  rw [← bytesAt_cons _ _ hk, emLen_eq hk h0] at hc
  rw [hc]
  unfold maskV
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)

theorem verifyOut_iff (hG : Proof.Mgf1.Valid G) {s : State} (hk : 1 ≤ (s.gpr .x1).toNat)
    (h0 : s.mem (s.gpr .x0) ≠ 0)
    (hfit : G.len + (sLenV s).getD 0 + 2 ≤ (s.gpr .x1).toNat - loV (s.mem (s.gpr .x0)).toNat) :
    verifyOut G s = true ↔ (loV (s.mem (s.gpr .x0)).toNat = 1 → (pubX s).getD 0 0 = 0) ∧
      EncOk G (Spec.Rsa.bytesAt s.mem (s.gpr .x4) G.len) ((pubX s).drop (loV (s.mem (s.gpr .x0)).toNat))
        ((s.gpr .x1).toNat - loV (s.mem (s.gpr .x0)).toNat)
        (8 * ((s.gpr .x1).toNat - loV (s.mem (s.gpr .x0)).toNat) - (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
          (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)) - 1)) (sLenV s) := by
  have hel := emLen_eq hk h0
  unfold verifyOut pubX pubOut
  rw [expected_eq]
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat = nB at hel ⊢
  have hnl : nB.length = (s.gpr .x1).toNat := by rw [← hnB, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  have hlo : loV (s.mem (s.gpr .x0)).toNat ≤ 1 := by unfold loV; split <;> omega
  rw [RsaPss.verify_bytes G hG (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _)
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, hnl]) rfl hel (by rw [hnl]; omega) hlo hfit]
  rw [hnl]
  rfl

end VG.Proof.RsaPss.AArch64.Vfy
