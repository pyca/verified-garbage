module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDerive
import VerifiedGarbage.Proof.Framework.Omega

/-! Establish the key-derivation contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1) :
    (Spec.Dsa.deriveKeyContract abi extra).pre (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  have hE : stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = stackArg s 2 :=
    (random_call_stackArg hsp _ _ 0).trans hw
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hsp,
    random_call_stackArgAddr hsp, hE]
  simp only [keygenDeriveRd, keygenDeriveWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_frameBase extra s, keygenStack_offset_toNat h (by omega)]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 200) := by
    rw [random_nonceBase extra s, keygenStack_offset_toNat h (by omega)]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩
      (below (s.sp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega)
  have sA : Region.Sub ⟨randomBase s, 8⟩ (below (s.sp) (extra + 256)) := by
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
  have dKA : (below (randomBase s) extra).Disjoint ⟨randomBase s, 8⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega) (by omega)
  refine ⟨?_, by omega, trivial, trivial, h.outParams, (h.stackOut.sub_left sM).symm,
    h.outScratch, (h.stackOut.sub_left sA).symm, h.paramsScratch,
    h.stackScratch.sub_left sM, (h.stackScratch.sub_left sA).symm,
    ?_, h.outBound, h.paramsBound, by omega, h.scratchBound,
    h.lengths, h.outLength, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega
  · cases extra with
    | zero => trivial
    | succ n => exact ⟨h.stackOut.sub_left sK, h.stackParams.sub_left sK, dKM,
        h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega

end VG.Proof.Dsa.AArch64
