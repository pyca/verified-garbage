module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashInit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLayout

/-! # HMAC initialization uses a disjoint 32-byte rejection key -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def macInitRd (g : Geometry) (key : Nat) : List Region := [g.scratch key 32]
def macInitWr (g : Geometry) : List Region :=
  [g.scratch sSt 96, g.scratch sOuter 96, g.scratch sHash 832, callArgsRegion g 20]

theorem macInit_pre {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {key : Nat}
    (h : Context g bs s) (a : Arguments g (fun j => (macInitPlan key j).valueAt g) 5 s)
    (keyLow : 192 ≤ key) (keyHigh : key + 32 ≤ sHash) :
    (Spec.Hmac.sha256I.initScratchContract abi 48).pre
      (s.callEntry.withRegions (macInitRd g key) (macInitWr g)) := by
  have sa := fun {j : Nat} (hj : j < 5) => callArgument_value h a (by decide : 5 ≤ 20) hj (macInitRd g key) (macInitWr g)
  have v0 : (macInitPlan key 0).valueAt g = g.workspace := by simp [macInitPlan, CallArg.valueAt, sSt]
  have v1 : (macInitPlan key 1).valueAt g = g.workspace + BitVec.ofNat 32 sOuter := rfl
  have v2 : (macInitPlan key 2).valueAt g = g.workspace + BitVec.ofNat 32 key := rfl
  have v3 : (macInitPlan key 3).valueAt g = BitVec.ofNat 32 32 := rfl
  have v4 : (macInitPlan key 4).valueAt g = g.workspace + BitVec.ofNat 32 sHash := rfl
  sig_pre [Spec.Hmac.Instance.initScratchContract, Spec.Hmac.initScratchContract, Spec.Hmac.initScratchSig,
    Spec.Hmac.initPre, Spec.Hmac.initSig, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256,
    abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 5), sa (by decide : 1 < 5), sa (by decide : 2 < 5),
    sa (by decide : 3 < 5), sa (by decide : 4 < 5), v0, v1, v2, v3, v4,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  simp only [show (32#32).toNat = 32 from rfl]
  have fit2 : key + 32 ≤ 8448 := by unfold sHash at keyHigh; omega
  have start2 : key < 8448 := by omega
  have e0 : g.scratch sSt 96 = (⟨byteAddr g.workspace, 96⟩ : Region) := by simp [Geometry.scratch, sSt]
  have e1 := h.scratchRegion_pointer (n := 96) (by decide : sOuter < 8448)
  have e2 := h.scratchRegion_pointer (n := 32) start2
  have e3 := h.scratchRegion_pointer (n := 832) (by decide : sHash < 8448)
  have p01 := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sOuter)) (by decide : sSt + 96 ≤ 8448) (by decide : sOuter + 96 ≤ 8448)
  rw [e0, e1] at p01
  have p02 := scratchDisjoint g (Or.inl (by unfold sSt; omega : sSt + 96 ≤ key)) (by decide : sSt + 96 ≤ 8448) fit2
  rw [e0, e2] at p02
  have p03 := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sHash)) (by decide : sSt + 96 ≤ 8448) (by decide : sHash + 832 ≤ 8448)
  rw [e0, e3] at p03
  have p12 := scratchDisjoint g (Or.inl (by unfold sOuter; omega : sOuter + 96 ≤ key)) (by decide : sOuter + 96 ≤ 8448) fit2
  rw [e1, e2] at p12
  have p13 := scratchDisjoint g (Or.inl (by decide : sOuter + 96 ≤ sHash)) (by decide : sOuter + 96 ≤ 8448) (by decide : sHash + 832 ≤ 8448)
  rw [e1, e3] at p13
  have p23 := scratchDisjoint g (Or.inl keyHigh) fit2 (by decide : sHash + 832 ≤ 8448)
  rw [e2, e3] at p23
  have a0 := h.argsScratch (by decide : 20 ≤ 160) (by decide : sSt + 96 ≤ 8448)
  have r0 := h.returnScratch (by decide : sSt + 96 ≤ 8448)
  have b0 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sSt + 96 ≤ 8448)
  rw [e0] at a0 r0 b0
  have a1 := h.argsScratch (by decide : 20 ≤ 160) (by decide : sOuter + 96 ≤ 8448)
  have r1 := h.returnScratch (by decide : sOuter + 96 ≤ 8448)
  have b1 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sOuter + 96 ≤ 8448)
  rw [e1] at a1 r1 b1
  have a2 := h.argsScratch (by decide : 20 ≤ 160) fit2
  have r2 := h.returnScratch fit2
  have b2 := h.belowScratch (by decide : 48 ≤ 3368) fit2
  rw [e2] at a2 r2 b2
  have a3 := h.argsScratch (by decide : 20 ≤ 160) (by decide : sHash + 832 ≤ 8448)
  have r3 := h.returnScratch (by decide : sHash + 832 ≤ 8448)
  have b3 := h.belowScratch (by decide : 48 ≤ 3368) (by decide : sHash + 832 ≤ 8448)
  rw [e3] at a3 r3 b3
  refine ⟨?_, ?_, ?_, ?_, p01, p02, p03, a0.symm, p12, p13, a1.symm,
    p23, a2.symm, a3.symm, r0, r1, r2, r3, h.returnArgs (by decide : 20 ≤ 160),
    b0, b1, b2, b3, h.belowArgs (by decide : 48 ≤ 3368) (by decide : 20 ≤ 160),
    ?_, h.valid.scratchFit (by decide : sOuter + 96 ≤ 8448) (by decide),
    h.valid.scratchFit fit2 start2, h.valid.scratchFit (by decide : sHash + 832 ≤ 8448) (by decide), by decide⟩
  · rw [h.callStackNat]
    have := h.valid.stackLow
    unfold calleeBytes at this
    omega
  · rw [h.callStackNat]
    have := h.valid.stackHigh
    unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes at this
    omega
  · simp only [macInitRd, e2]
    rfl
  · simp only [macInitWr, e0, e1, e3]
    rfl
  · have := h.valid.scratchMinimum
    have := h.valid.workspaceFit
    omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
