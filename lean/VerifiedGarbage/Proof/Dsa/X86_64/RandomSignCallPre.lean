module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI
import VerifiedGarbage.Proof.Framework.Offset

/-! Establish the supplied-nonce contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

theorem random_call_pre {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hsp : t.gpr .rsp = randomBase s)
    (hw : ∀ i < 5, word t.mem (randomBase s) (8 * i) = randomCallArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi)
    (hdx : t.gpr .rdx = s.gpr .rcx) (hcx : t.gpr .rcx = s.gpr .r8)
    (h8 : t.gpr .r8 = s.gpr .r9) (h9 : t.gpr .r9 = off (randomBase s) Random.oNonce) :
    (Spec.Dsa.signContract abi extra).pre (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) := by
  have hE (i : Nat) (hi : i < 5) :
      stackArg (t.callEntry.withRegions (randomCallRd s) (randomCallWr s)) i = randomCallArg s i :=
    (random_call_stackArg hsp _ _ hi).trans (hw i hi)
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp,
    random_call_stackArgAddr hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide),
    hE 3 (by decide), hE 4 (by decide)]
  simp only [randomCallArg, randomCallRd, randomCallWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega
  have hk := randomStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, randomStack_offset_toNat h (by omega)]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 208) := by
    rw [random_nonceBase extra s, randomStack_offset_toNat h (by omega)]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩
      (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega)
  have sA : Region.Sub ⟨randomBase s, 40⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega)
  have sR : Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
    rw [random_callBase extra s]
    exact Offset.sub_base _ (by omega)
  have sK : Region.Sub (below (randomBase s - 8) extra) (below (s.gpr .rsp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega)
  have dRM : (⟨randomBase s - 8, 8⟩ : Region).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    rw [random_callBase extra s, random_nonceBase extra s]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dRA : (⟨randomBase s - 8, 8⟩ : Region).Disjoint ⟨randomBase s, 40⟩ := by
    rw [random_callBase extra s, random_frameBase extra s]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dKM : (below (randomBase s - 8) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (stackArg s 0).toNat⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega) (by omega)
  have dKA : (below (randomBase s - 8) extra).Disjoint ⟨randomBase s, 40⟩ := by
    change (⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega) (by omega)
  refine ⟨?_, by omega, trivial, trivial, h.outKey, (h.stackOut.sub_left sM).symm,
    h.outDigest, h.outScratch, (h.stackOut.sub_left sA).symm, h.keyScratch,
    h.stackScratch.sub_left sM, h.digestScratch, (h.stackScratch.sub_left sA).symm,
    h.stackOut.sub_left sR, h.stackKey.sub_left sR, dRM, h.stackDigest.sub_left sR,
    h.stackScratch.sub_left sR, ?_, h.outBound, h.keyBound, by omega, h.digestBound,
    h.scratchBound, h.lengths, h.outLength, h.keyLength, ?_⟩
  · cases extra <;> simp only <;> omega
  · cases extra with
    | zero => exact dRA
    | succ n => exact ⟨dRA, h.stackOut.sub_left sK, h.stackKey.sub_left sK, dKM,
        h.stackDigest.sub_left sK, h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.randomSignScratchWords at hh
    omega

end VG.Proof.Dsa.X86_64
