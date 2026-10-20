module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Streaming TDEA-CMAC on AArch64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which imply these
(`Verified.lean`). The functions call nothing and use no stack.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.AArch64

open VG VG.AArch64

/-- `vg_cmac_triple_des_stream_init(state = x0, key = x1, key_len = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 416⟩
    let key : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let scr : Region := ⟨s.gpr .x3, 640⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .x0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .x2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .x0) (Spec.TripleDes.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_absorb(state = x0, count = x1, data = x2, len = x3, scratch = x4)`. -/
def absorbAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 416⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, 688⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 688 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .x0) key msg →
      s.gpr .x1 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .x3).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .x0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_finish(state = x0, count = x1, out = x2, scratch = x3)`. -/
def finishAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 416⟩
    let out : Region := ⟨s.gpr .x2, 8⟩
    let scr : Region := ⟨s.gpr .x3, 640⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .x0).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .x0) key msg →
      s.gpr .x1 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .x2) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacTripleDes.Stream.AArch64
