import VerifiedGarbage.Proof.RsaPss.AArch64.SignMain
import VerifiedGarbage.Proof.RsaPss.SignCases

/-!
# RSASSA-PSS signing on AArch64: the outcome, by cases

`signOut G s`: what the contract asks of a call from `s`. It is `invalid`
if the modulus' first byte is zero (`signOut_zero`) or the salt does not fit
(`signOut_long`), and otherwise the private operation on the encoding
`signEnc` writes (`signOut_eq`).
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64 (loV maskV)

/-- The outcome `signContract.post` asks for. -/
def signOut (G : Spec.Mgf1.Hash) (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPss.sign G G (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 6) (s.gpr .x7).toNat)
    (digB G.len s) (saltB s)

theorem bytesAt_cons (m : Mem) (p : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.bytesAt m p k = m p :: Spec.Rsa.bytesAt m (p + 1) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ => ?_⟩
  simp only [Function.comp, BitVec.add_assoc]
  rw [show (1 : Addr) + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 1) by
    rw [BitVec.add_comm, ← BitVec.ofNat_add_ofNat]; rfl]

variable (G : Spec.Mgf1.Hash)

theorem signOut_zero {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) = 0) :
    signOut G s = .invalid := by
  unfold signOut
  rw [bytesAt_cons _ _ hk, h0]
  exact RsaPss.sign_zero G ..

theorem emLen_eq {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) ≠ 0) :
    Spec.RsaPss.emLength (Spec.RsaPss.bitLength (Spec.Rsa.os2ip
      (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) - 1) =
      (s.gpr .x3).toNat - loV (s.mem (s.gpr .x2)).toNat := by
  rw [bytesAt_cons _ _ hk, RsaPss.emLength_eq _ h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  unfold loV
  split <;> omega

theorem signOut_long {s : State} (hk : 1 ≤ (s.gpr .x3).toNat) (h0 : s.mem (s.gpr .x2) ≠ 0)
    (h : (s.gpr .x3).toNat - loV (s.mem (s.gpr .x2)).toNat < G.len + (stackArg s 10).toNat + 2) :
    signOut G s = .invalid := by
  unfold signOut
  refine RsaPss.sign_long G _ _ _ _ _ _ _ _ ?_
  rw [emLen_eq hk h0, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  exact h

theorem signOut_eq (hG : Proof.Mgf1.Valid G) {s : State} (hk : 1 ≤ (s.gpr .x3).toNat)
    (h0 : s.mem (s.gpr .x2) ≠ 0)
    (hfit : G.len + (stackArg s 10).toNat + 2 ≤ (s.gpr .x3).toNat - loV (s.mem (s.gpr .x2)).toNat) :
    signOut G s = privOut s (encEm G G.len s (loV (s.mem (s.gpr .x2)).toNat)
      ((maskV (s.mem (s.gpr .x2)).toNat).setWidth 8)) := by
  have hel := emLen_eq hk h0
  have hc := RsaPss.mask_eq (Spec.Rsa.bytesAt s.mem (s.gpr .x2 + 1) ((s.gpr .x3).toNat - 1)) h0
  unfold signOut privOut encEm
  generalize hnB : Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = nB at hel ⊢
  rw [bytesAt_cons _ _ hk] at hnB
  subst hnB
  rw [RsaPss.sign_eq G hG h0 (lo := loV (s.mem (s.gpr .x2)).toNat)
    (db := (s.gpr .x3).toNat - loV (s.mem (s.gpr .x2)).toNat - G.len - 1)
    (VG.Proof.RsaPkcs1Sig.bytesAt_length _ _ _) rfl hel
    (by rw [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]; unfold loV; split <;> omega) rfl
    (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact hfit)]
  rw [hel] at hc
  have hm8 : (maskV (s.mem (s.gpr .x2)).toNat).setWidth 8 = if (s.mem (s.gpr .x2)).toNat = 1 then 0xFF
      else BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .x2)).toNat - 1) := by
    unfold maskV
    split
    · rfl
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact Nat.mod_mod_of_dvd _ (by decide)
  rw [hc, ← hm8]
  simp only [List.length_cons, VG.Proof.RsaPkcs1Sig.bytesAt_length]
  rw [Nat.sub_add_cancel hk]

end VG.Proof.RsaPss.AArch64.Sgn
