module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.X86_64.Isa
import Mathlib.Util.CompileInductive
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Streaming TDEA-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which imply these
(`Verified.lean`). The functions call nothing and use no stack.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86_64

open VG VG.X86_64

/-- `vg_cmac_triple_des_stream_init(state = rdi, key = rsi, key_len = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 416⟩
    let key : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨s.gpr .rcx, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧ state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .rdx).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem (s.gpr .rdi) (Spec.TripleDes.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_absorb(state = rdi, count = rsi, data = rdx, len = rcx, scratch = r8)`. -/
def absorbX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 416⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 688⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 688 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .rdi) key msg →
      s.gpr .rsi = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .rcx).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem (s.gpr .rdi) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_finish(state = rdi, count = rsi, out = rdx, scratch = rcx)`. -/
def finishX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 416⟩
    let out : Region := ⟨s.gpr .rdx, 8⟩
    let scr : Region := ⟨s.gpr .rcx, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 416 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem (s.gpr .rdi) key msg →
      s.gpr .rsi = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacTripleDes.Stream.X86_64
