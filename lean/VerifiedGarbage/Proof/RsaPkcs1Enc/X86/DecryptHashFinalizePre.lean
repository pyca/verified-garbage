module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashInit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLayout

/-! # SHA-256 finalization writes DH in its separate digest region -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def finalizeWr (g : Geometry) : List Region :=
  [g.scratch sSt 96, g.scratch sDH 32, g.scratch sHash 608, callArgsRegion g 20]

theorem shaFinalize_pre {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (fun j => (shaFinalizePlan j).valueAt g) 5 s) :
    (Spec.Sha256.finalizeScratchContract abi 20).pre (s.callEntry.withRegions [] (finalizeWr g)) := by
  have sa := fun {j : Nat} (hj : j < 5) => callArgument_value h a (by decide : 5 ≤ 20) hj [] (finalizeWr g)
  have v0 : (shaFinalizePlan 0).valueAt g = g.workspace := by simp [shaFinalizePlan, CallArg.valueAt, sSt]
  have v3 : (shaFinalizePlan 3).valueAt g = g.workspace + BitVec.ofNat 32 sDH := rfl
  have v4 : (shaFinalizePlan 4).valueAt g = g.workspace + BitVec.ofNat 32 sHash := rfl
  sig_pre [Spec.Sha256.finalizeScratchContract, Spec.Sha256.finalizeScratchSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 5), sa (by decide : 3 < 5), sa (by decide : 4 < 5), v0, v3, v4,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  have st : g.scratch sSt 96 = (⟨byteAddr g.workspace, 96⟩ : Region) := by simp [Geometry.scratch, sSt]
  have dh := h.scratchRegion_pointer (n := 32) (by decide : sDH < 8448)
  have hs := h.scratchRegion_pointer (n := 608) (by decide : sHash < 8448)
  have sd := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sDH)) (by decide : sSt + 96 ≤ 8448) (by decide : sDH + 32 ≤ 8448)
  have sh := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sHash)) (by decide : sSt + 96 ≤ 8448) (by decide : sHash + 608 ≤ 8448)
  have dhh := scratchDisjoint g (Or.inl (by decide : sDH + 32 ≤ sHash)) (by decide : sDH + 32 ≤ 8448) (by decide : sHash + 608 ≤ 8448)
  have ast := h.argsScratch (by decide : 20 ≤ 160) (by decide : sSt + 96 ≤ 8448)
  have adh := h.argsScratch (by decide : 20 ≤ 160) (by decide : sDH + 32 ≤ 8448)
  have ahs := h.argsScratch (by decide : 20 ≤ 160) (by decide : sHash + 608 ≤ 8448)
  have rst := h.returnScratch (by decide : sSt + 96 ≤ 8448)
  have rdh := h.returnScratch (by decide : sDH + 32 ≤ 8448)
  have rhs := h.returnScratch (by decide : sHash + 608 ≤ 8448)
  have bst := h.belowScratch (by decide : 20 ≤ 3368) (by decide : sSt + 96 ≤ 8448)
  have bdh := h.belowScratch (by decide : 20 ≤ 3368) (by decide : sDH + 32 ≤ 8448)
  have bhs := h.belowScratch (by decide : 20 ≤ 3368) (by decide : sHash + 608 ≤ 8448)
  rw [st, dh] at sd
  rw [st, hs] at sh
  rw [dh, hs] at dhh
  rw [st] at ast rst bst
  rw [dh] at adh rdh bdh
  rw [hs] at ahs rhs bhs
  refine ⟨?_, ?_, ?_, sd, sh, ast.symm, dhh, adh.symm, ahs.symm,
    rst, rdh, rhs, h.returnArgs (by decide : 20 ≤ 160), bst, bdh, bhs,
    h.belowArgs (by decide : 20 ≤ 3368) (by decide : 20 ≤ 160), ?_,
    h.valid.scratchFit (by decide : sDH + 32 ≤ 8448) (by decide),
    h.valid.scratchFit (by decide : sHash + 608 ≤ 8448) (by decide)⟩
  · rw [h.callStackNat]
    have := h.valid.stackLow
    unfold calleeBytes at this
    omega
  · rw [h.callStackNat]
    have := h.valid.stackHigh
    unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes at this
    omega
  · simp only [finalizeWr, st, dh, hs]
    rfl
  · have := h.valid.scratchMinimum
    have := h.valid.workspaceFit
    omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
