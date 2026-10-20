module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI
import VerifiedGarbage.Proof.Framework.Offset

/-! Establish the supplied-nonce contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem random_call_pre {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : ∀ i < 3, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = s.gpr .x7) :
    (Spec.Dsa.signContract abi extra).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hE (i : Nat) (hi : i < 3) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ i).trans (hw i hi)
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide)]
  simp only [randomCallArg, randomCallRd, randomCallWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega
  have hk := randomStackBase_toNat h
  have hR : (randomBase s).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_frameBase extra s, randomStack_offset_toNat h (by omega)]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 200) := by
    rw [random_nonceBase extra s, randomStack_offset_toNat h (by omega)]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩
      (below (s.sp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega)
  have sA : Region.Sub ⟨randomBase s, 24⟩ (below (s.sp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega)
  have sK : Region.Sub (below (randomBase s) extra) (below (s.sp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega)
  have dKM : (below (randomBase s) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega) (by omega)
  have dKA : (below (randomBase s) extra).Disjoint ⟨randomBase s, 24⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega) (by omega)
  refine ⟨?_, by omega, trivial, trivial, h.outKey, (h.stackOut.sub_left sM).symm,
    h.outDigest, h.outScratch, (h.stackOut.sub_left sA).symm, h.keyScratch,
    h.stackScratch.sub_left sM, h.digestScratch, (h.stackScratch.sub_left sA).symm,
    ?_, h.outBound, h.keyBound, by omega, h.digestBound, h.scratchBound,
    h.lengths, h.outLength, h.keyLength, ?_⟩
  · cases extra <;> simp only <;> omega
  · cases extra with
    | zero => trivial
    | succ n => exact ⟨h.stackOut.sub_left sK, h.stackKey.sub_left sK, dKM,
        h.stackDigest.sub_left sK, h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.randomSignScratchWords at hh
    omega

end VG.Proof.Dsa.AArch64
