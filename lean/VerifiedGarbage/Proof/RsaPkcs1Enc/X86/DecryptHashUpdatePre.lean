module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashInit

/-! # SHA-256 update is safe for disjoint data, state and hash-working space -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

def updateValues (g : Geometry) (data : BitVec 32) (len count j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.workspace | 1 => BitVec.ofNat 32 count | 2 => 0 | 3 => data
  | 4 => BitVec.ofNat 32 len | _ => g.workspace + BitVec.ofNat 32 sHash

def updateRd (_g : Geometry) (data : BitVec 32) (len : Nat) : List Region :=
  [⟨byteAddr data, len⟩]

def updateWr (g : Geometry) : List Region := [g.scratch sSt 96, g.scratch sHash 608, ⟨byteAddr g.stack, 24⟩]

theorem shaUpdate_pre {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    {data : BitVec 32} {len count : Nat}
    (h : Context g bs s) (a : Arguments g (updateValues g data len count) 6 s)
    (dataFit : data.toNat + len ≤ 2 ^ 32) (lengthBound : len < 2 ^ 32)
    (dataState : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sSt 96))
    (dataScratch : (⟨byteAddr data, len⟩ : Region).Disjoint (g.scratch sHash 608))
    (calleeData : g.calleeRegion.Disjoint ⟨byteAddr data, len⟩)
    (dataArgs : (⟨byteAddr data, len⟩ : Region).Disjoint ⟨byteAddr g.stack, 24⟩) :
    (Spec.Sha256.updateScratchContract abi 20).pre (s.callEntry.withRegions (updateRd g data len) (updateWr g)) := by
  have sa := fun {j : Nat} (hj : j < 6) =>
    callArgument_value h a (by decide : 6 ≤ 20) hj (updateRd g data len) (updateWr g)
  have v0 : updateValues g data len count 0 = g.workspace := rfl
  have v3 : updateValues g data len count 3 = data := rfl
  have v4 : updateValues g data len count 4 = BitVec.ofNat 32 len := rfl
  have v5 : updateValues g data len count 5 = g.workspace + BitVec.ofNat 32 sHash := rfl
  sig_pre [Spec.Sha256.updateScratchContract, Spec.Sha256.updateScratchSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 6), sa (by decide : 3 < 6), sa (by decide : 4 < 6), sa (by decide : 5 < 6),
    v0, v3, v4, v5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound,
    argAddr_withRegions, argAddr_callEntry, h.sp]
  simp only [Nat.mul_zero, BitVec.add_zero]
  have stateEq : g.scratch sSt 96 = (⟨byteAddr g.workspace, 96⟩ : Region) := by simp [Geometry.scratch, sSt]
  have hashEq : g.scratch sHash 608 = (⟨byteAddr (g.workspace + BitVec.ofNat 32 sHash), 608⟩ : Region) := by
    rw [h.valid.scratchAddress (by decide : sHash < 8448)]
    rfl
  rw [stateEq] at dataState
  rw [hashEq] at dataScratch
  have stateSub : (⟨byteAddr g.workspace, 96⟩ : Region).Sub g.workspaceRegion :=
    Region.sub_prefix (by have := h.valid.scratchMinimum; omega)
  have hashSub : (⟨byteAddr (g.workspace + BitVec.ofNat 32 sHash), 608⟩ : Region).Sub g.workspaceRegion := by
    rw [← hashEq]
    exact h.valid.scratchSub (by decide : sHash + 608 ≤ 8448)
  have argsSub : (⟨byteAddr g.stack, 24⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have argsWork := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (argsSub x hx))
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right argsSub
  have stateHash := scratchDisjoint g (Or.inl (by decide : sSt + 96 ≤ sHash))
    (by decide : sSt + 96 ≤ 8448) (by decide : sHash + 608 ≤ 8448)
  rw [stateEq, hashEq] at stateHash
  have low : 4 ≤ g.stack.toNat := by have := h.valid.stackLow; unfold calleeBytes at this; omega
  have spNat : (g.stack - 4).toNat = g.stack.toNat - 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl]
    exact sub_toNat low
  have below : (⟨(g.stack - 4).setWidth 64 - 20#64, 20⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [spNat]; have := h.valid.stackLow; unfold calleeBytes at this; omega : 20 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 20 + 4 ≤ calleeBytes) h.valid.stackLow
  refine ⟨?_, ?_, rfl, ?_, dataState.symm, stateHash, (argsWork.sub_right stateSub).symm,
    dataScratch, dataArgs, (argsWork.sub_right hashSub).symm,
    (cWork.sub_right stateSub).sub_left h.retSub, calleeData.sub_left h.retSub,
    (cWork.sub_right hashSub).sub_left h.retSub, cArgs.sub_left h.retSub,
    (cWork.sub_right stateSub).sub_left below, calleeData.sub_left below,
    (cWork.sub_right hashSub).sub_left below, cArgs.sub_left below,
    ?_, dataFit, h.valid.scratchFit (by decide : sHash + 608 ≤ 8448) (by decide)⟩
  · rw [spNat]
    have := h.valid.stackLow
    unfold calleeBytes at this
    omega
  · rw [spNat]
    have := h.valid.stackHigh
    unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes at this
    omega
  · simp only [updateWr, stateEq, hashEq]
    rfl
  · have := h.valid.scratchMinimum
    have := h.valid.workspaceFit
    omega

end VG.Proof.RsaPkcs1Enc.X86.Dec
