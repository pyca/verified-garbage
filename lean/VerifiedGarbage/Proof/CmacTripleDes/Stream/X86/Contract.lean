module

public import VerifiedGarbage.Spec.Cmac.TripleDesContract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Streaming TDEA-CMAC on x86: the contracts the proofs are written against

The artifacts' contracts are the shared ones of
`Spec/Cmac/TripleDesContract.lean`, with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`, `StreamScratchW.lean`), which
imply these (`Implies.lean`). The arguments are on the stack, from
`[esp + 4]` (cdecl). The functions push the arguments of the code they run
inline below the stack pointer: 20 bytes for `stream_init`, 24 for `absorb`
and `finish`, which may not overlap any buffer.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86

/-- The 64-bit `count` argument, in the slots 1 and 2 (low word first). -/
def countX86 (s : State) : BitVec 64 := arg s 2 ++ arg s 1

/-- `vg_cmac_triple_des_stream_init(state, key, key_len, scratch)`. -/
def initX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 416⟩
    let key : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [key, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 416 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 640 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      Spec.TripleDes.validKey (arg s 2).toNat
  post s s' :=
    Spec.Cmac.tdesRepr s'.mem ((arg s 0).setWidth 64)
      (Spec.TripleDes.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `vg_cmac_triple_des_absorb(state, count, data, len, scratch)`. -/
def absorbX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 416⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 688⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 416 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 688 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem ((arg s 0).setWidth 64) key msg →
      countX86 s = BitVec.ofNat 64 msg.length → msg.length + (arg s 4).toNat < 2 ^ 64 →
      Spec.Cmac.tdesRepr s'.mem ((arg s 0).setWidth 64) key
        (msg ++ Spec.Aes.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `vg_cmac_triple_des_finish(state, count, out, scratch)`. -/
def finishX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 416⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 8⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 688⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 416 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 688 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    ∀ key msg, Spec.Cmac.tdesRepr s.mem ((arg s 0).setWidth 64) key msg →
      countX86 s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem ((arg s 3).setWidth 64) 8 = Spec.Cmac.tdesCmac key 8 msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.CmacTripleDes.Stream.X86
