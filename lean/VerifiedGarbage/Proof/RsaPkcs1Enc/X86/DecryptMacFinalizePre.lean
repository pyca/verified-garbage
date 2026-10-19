module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashInit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLayout

/-! # HMAC finalization uses disjoint states, digest and working space -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def macFinalizeValues (g : Geometry) (dst count j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.workspace | 1 => g.workspace + BitVec.ofNat 32 sOuter
  | 2 => BitVec.ofNat 32 count | 3 => 0
  | 4 => g.workspace + BitVec.ofNat 32 dst | _ => g.workspace + BitVec.ofNat 32 sHash

def macFinalizeRd (g : Geometry) : List Region := [g.scratch sOuter 96]
def macFinalizeWr (g : Geometry) (dst : Nat) : List Region :=
  [g.scratch sSt 96, g.scratch dst 32, g.scratch sHash 832, callArgsRegion g 24]

theorem macFinalize_pre {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {dst count : Nat}
    (h : Context g bs s) (a : Arguments g (macFinalizeValues g dst count) 6 s)
    (dstLow : 192 ≤ dst) (dstHigh : dst + 32 ≤ sHash) :
    (Spec.Hmac.sha256I.finalizeScratchContract abi 48).pre
      (s.callEntry.withRegions (macFinalizeRd g) (macFinalizeWr g dst)) := by
  have sa := fun {j : Nat} (hj : j < 6) => callArgument_value h a (by decide : 6 ≤ 20) hj (macFinalizeRd g) (macFinalizeWr g dst)
  have v0 : macFinalizeValues g dst count 0 = g.workspace := rfl
  have v1 : macFinalizeValues g dst count 1 = g.workspace + BitVec.ofNat 32 sOuter := rfl
  have v4 : macFinalizeValues g dst count 4 = g.workspace + BitVec.ofNat 32 dst := rfl
  have v5 : macFinalizeValues g dst count 5 = g.workspace + BitVec.ofNat 32 sHash := rfl
  sig_pre [Spec.Hmac.Instance.finalizeScratchContract, Spec.Hmac.finalizeScratchContract, Spec.Hmac.finalizeScratchSig,
    Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 4 < 6),
    sa (by decide : 5 < 6), v0, v1, v4, v5,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  have fit2 : dst + 32 ≤ 8448 := by unfold sHash at dstHigh; omega
  have start2 : dst < 8448 := by omega
  have e0 : g.scratch sSt 96 = (⟨byteAddr g.workspace, 96⟩ : Region) := by simp [Geometry.scratch, sSt]
  have e1 := h.scratchRegion_pointer (n := 96) (by decide : sOuter < 8448)
  have e2 := h.scratchRegion_pointer (n := 32) start2
  have e3 := h.scratchRegion_pointer (n := 832) (by decide : sHash < 8448)
  have p01 := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sOuter)) (by decide : sSt + 96 ≤ 8448) (by decide : sOuter + 96 ≤ 8448)
  rw [e0, e1] at p01
  have p02 := scratchDisjoint g (Or.inl (by unfold sSt; omega : sSt + 96 ≤ dst)) (by decide : sSt + 96 ≤ 8448) fit2
  rw [e0, e2] at p02
  have p03 := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sHash)) (by decide : sSt + 96 ≤ 8448) (by decide : sHash + 832 ≤ 8448)
  rw [e0, e3] at p03
  have p12 := scratchDisjoint g (Or.inl (by unfold sOuter; omega : sOuter + 96 ≤ dst)) (by decide : sOuter + 96 ≤ 8448) fit2
  rw [e1, e2] at p12
  have p13 := scratchDisjoint g (Or.inl (by decide : sOuter + 96 ≤ sHash)) (by decide : sOuter + 96 ≤ 8448) (by decide : sHash + 832 ≤ 8448)
  rw [e1, e3] at p13
  have p23 := scratchDisjoint g (Or.inl dstHigh) fit2 (by decide : sHash + 832 ≤ 8448)
  rw [e2, e3] at p23
  have a0 := h.argsScratch (by decide : 24 ≤ 160) (by decide : sSt + 96 ≤ 8448)
  have r0 := h.returnScratch (by decide : sSt + 96 ≤ 8448)
  have b0 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sSt + 96 ≤ 8448)
  rw [e0] at a0 r0 b0
  have a1 := h.argsScratch (by decide : 24 ≤ 160) (by decide : sOuter + 96 ≤ 8448)
  have r1 := h.returnScratch (by decide : sOuter + 96 ≤ 8448)
  have b1 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sOuter + 96 ≤ 8448)
  rw [e1] at a1 r1 b1
  have a2 := h.argsScratch (by decide : 24 ≤ 160) fit2
  have r2 := h.returnScratch fit2
  have b2 := h.belowScratch (by decide : 48 ≤ 3368) fit2
  rw [e2] at a2 r2 b2
  have a3 := h.argsScratch (by decide : 24 ≤ 160) (by decide : sHash + 832 ≤ 8448)
  have r3 := h.returnScratch (by decide : sHash + 832 ≤ 8448)
  have b3 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sHash + 832 ≤ 8448)
  rw [e3] at a3 r3 b3
  refine ⟨?_, ?_, ?_, ?_, p01, p02, p03, a0.symm, p12, p13, a1.symm,
    p23, a2.symm, a3.symm, r0, r1, r2, r3, h.returnArgs (by decide : 24 ≤ 160),
    b0, b1, b2, b3, h.belowArgs (by decide : 48 ≤ 3368) (by decide : 24 ≤ 160),
    ?_, h.valid.scratchFit (by decide : sOuter + 96 ≤ 8448) (by decide),
    h.valid.scratchFit fit2 start2, h.valid.scratchFit (by decide : sHash + 832 ≤ 8448) (by decide)⟩
  · rw [h.callStackNat]
    have := h.valid.stackLow
    unfold calleeBytes at this
    omega
  · rw [h.callStackNat]
    have := h.valid.stackHigh
    unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes at this
    omega
  · simp only [macFinalizeRd, e1]
    rfl
  · simp only [macFinalizeWr, e0, e2, e3]
    rfl
  · have := h.valid.scratchMinimum
    have := h.valid.workspaceFit
    omega


end VG.Proof.RsaPkcs1Enc.X86.Dec
